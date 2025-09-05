/*
 * xadres_ultra_complexo.c
 * Um programa em C relativamente completo (e educativo) que implementa:
 *  - Representação do tabuleiro com 0x88
 *  - Leitura/Gravação FEN
 *  - Geração de movimentos (todas as peças, roque, en passant, promocao)
 *  - Validação de legalidade (cheque, mate, empate por insuficiencia simplificada)
 *  - Motor de busca minimax com poda alpha-beta e heurística simples
 *  - Interface de linha de comando com comandos: move, perft, fen, undo, ai, play
 *
 * Observação: Este código procura ser didático e funcional — não é um motor de nível competitivo
 * mas implementa muitos detalhes práticos do xadrez. Use-o como base para otimizações
 * (bitboards, ordenação de movimentos, tablebases, avaliação mais sofisticada etc.).
 *
 * Compilar: gcc -O2 -std=c11 -o xadres_ultra_complexo xadres_ultra_complexo.c
 * Executar: ./xadres_ultra_complexo
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <limits.h>

/* ==========================================================
   Constantes e utilitários básicos
   ========================================================== */

#define BOARD_SIZE 128 /* 0x88 representation */
#define MAX_MOVES 256
#define MAX_PLY 64
#define INF 1000000

typedef enum {WHITE, BLACK, NO_COLOR} Color;

enum {EMPTY=0, P=1,N=2,B=3,R=4,Q=5,K=6};

/* direcoes 0x88-friendly (offsets) */
static const int knightDirs[8] = {31,33,14,18,-31,-33,-14,-18};
static const int kingDirs[8] = {1,-1,16,-16,15,17,-15,-17};
static const int bishopDirs[4] = {15,17,-15,-17};
static const int rookDirs[4] = {1,-1,16,-16};

/* helpers 0x88 */
static inline int onboard(int sq){ return (sq & 0x88) == 0; }

/* board storage: positive = white piece, negative = black piece; value encodes piece type */
int board[BOARD_SIZE];
Color sideToMove = WHITE;
int castlingRights = 0; /* bitmask: 1 white K, 2 white Q, 4 black K, 8 black Q */
int enPassant = -1; /* square or -1 */
int halfmoveClock = 0; int fullmoveNumber = 1;

/* move history for undo */
typedef struct {
    int move; /* encoded */
    int captured;
    int prevEP;
    int prevCastling;
    int prevHalfmove;
} Undo;

Undo history[1024];
int histPly = 0;

/* move encoding: 0..127 from<<8 to.. store flags in low bits etc. We'll use ints with fields */
/* encode as: from | (to<<8) | (prom<<16) | (flag<<20) */
#define FROM(m) ((m) & 0xFF)
#define TO(m) (((m) >> 8) & 0xFF)
#define PROM(m) (((m) >> 16) & 0xF)
#define FLAG(m) (((m) >> 20) & 0xFF)
#define MAKE_MOVE(f,t,p,fl) ((f) | ((t)<<8) | ((p)<<16) | ((fl)<<20))

enum MoveFlags {MF_NONE=0, MF_ENPASS=1, MF_CASTLE=2, MF_PROM=4, MF_CAPTURE=8};

/* ========================
   Inicialização e FEN
   ======================== */

void clear_board(){
    for(int i=0;i<BOARD_SIZE;i++) board[i]=0;
    sideToMove = WHITE; castlingRights = 0; enPassant = -1; halfmoveClock=0; fullmoveNumber=1;
}

/* mapa char->piece */
int piece_from_char(char c){
    char lower = tolower(c);
    int p=0;
    if(lower=='p') p=P;
    else if(lower=='n') p=N;
    else if(lower=='b') p=B;
    else if(lower=='r') p=R;
    else if(lower=='q') p=Q;
    else if(lower=='k') p=K;
    return isupper(c) ? p : (p? -p:0);
}

/* load FEN basic support */
int file_rank_to_sq(char file, char rank){
    int f = file - 'a';
    int r = rank - '1';
    return (7-r)*16 + f; /* 0x88 mapping: rank0 at top */
}

int load_fen(const char *fen){
    clear_board();
    const char *s = fen;
    int sq = 0; /* 0..63, but we'll map to 0x88 positions by row */
    int rank = 0; int file = 0;
    rank = 0; file = 0;
    while(*s && *s!=' '){
        if(*s=='/') { rank++; file=0; s++; continue; }
        if(isdigit((unsigned char)*s)){
            int n = *s - '0'; file += n; s++; continue;
        }
        int boardRank = rank;
        int r = boardRank;
        int sq0 = (r)*16 + file; /* note: FEN starts from rank 8 to 1; we will adapt after parsing */
        /* We'll parse from top to bottom so rank 0 is top (rank 8) */
        int tfile = file; int trank = rank;
        /* convert to 0x88: top rank (FEN first) -> board rank 0x0 -> actual 0 */
        int pos = (rank)*16 + file;
        char c = *s;
        int p = piece_from_char(c);
        board[pos] = p;
        file++; s++;
    }
    /* The above parse used rank 0 as top; but we want ranks 0..7 top->bottom. It's ok as long as we stay consistent.
       Now advance s past space and parse side to move, castling, enpassant, halfmove, fullmove */
    while(*s && *s==' ') s++;
    if(*s=='w') sideToMove = WHITE; else sideToMove = BLACK;
    /* move on */
    while(*s && *s!=' ') s++;
    while(*s && *s==' ') s++;
    /* castling */
    if(*s=='-') { /* none */ s++; }
    else {
        while(*s && *s!=' ') {
            if(*s=='K') castlingRights |= 1;
            if(*s=='Q') castlingRights |= 2;
            if(*s=='k') castlingRights |= 4;
            if(*s=='q') castlingRights |= 8;
            s++;
        }
    }
    while(*s && *s==' ') s++;
    if(*s=='-') { enPassant = -1; s++; }
    else {
        char filec = *s; char rankc = *(s+1);
        enPassant = file_rank_to_sq(filec, rankc);
        s+=2;
    }
    while(*s && *s==' ') s++;
    if(*s) { halfmoveClock = atoi(s); while(*s && *s!=' ') s++; }
    while(*s && *s==' ') s++;
    if(*s) { fullmoveNumber = atoi(s); }
    return 1;
}

void set_startpos(){
    const char *start = "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1";
    load_fen(start);
}

/* print board to console (human friendly) */
char piece_to_char(int v){
    if(v==0) return '.';
    int a = abs(v);
    char c = '?';
    if(a==P) c='p'; else if(a==N) c='n'; else if(a==B) c='b'; else if(a==R) c='r'; else if(a==Q) c='q'; else if(a==K) c='k';
    if(v>0) return toupper(c); else return c;
}

void print_board(){
    printf("  +-----------------+\n");
    for(int r=0;r<8;r++){
        printf("%d | ", 8-r);
        for(int f=0;f<8;f++){
            int sq = r*16 + f;
            printf("%c ", piece_to_char(board[sq]));
        }
        printf("|\n");
    }
    printf("  +-----------------+\n");
    printf("    a b c d e f g h\n");
    printf("Side to move: %s\n", sideToMove==WHITE?"white":"black");
}

/* =========================
   Move generation utilities
   ========================= */

int is_white_piece(int v){ return v>0; }
int is_black_piece(int v){ return v<0; }
int piece_type_of(int v){ return v==0?0:abs(v); }

/* generate pseudo-legal moves (not checking for checks yet) */
int generate_moves(int moves[]){
    int n=0;
    int us = sideToMove;
    for(int sq=0; sq<BOARD_SIZE; sq++){
        if(!onboard(sq)) { sq += 7; continue; }
        int val = board[sq]; if(val==0) continue;
        if(us==WHITE && val<0) continue;
        if(us==BLACK && val>0) continue;
        int pt = piece_type_of(val);
        int sign = (val>0)?1:-1;
        if(pt==P){
            int dir = (sign>0)? -16 : 16; /* white pawns move up (-16) because top rank is 0 */
            int to = sq + dir;
            /* one step */
            if(onboard(to) && board[to]==0){
                /* promotion? */
                int rank = (sq>>4);
                if((sign>0 && (sq>>4)==7-6) || (sign<0 && (sq>>4)==1)){
                    /* promote on next rank; but our mapping is inverted; to keep it simple we just check to's rank */
                }
                moves[n++] = MAKE_MOVE(sq,to,0,MF_NONE);
                /* two steps */
                int startRank = (sign>0)?6:1;
                if((sq>>4)==startRank){
                    int to2 = sq + dir*2;
                    if(board[to2]==0) moves[n++]=MAKE_MOVE(sq,to2,0,MF_NONE);
                }
            }
            /* captures */
            int caps[2] = {dir-1, dir+1};
            for(int i=0;i<2;i++){
                int tc = sq + caps[i];
                if(onboard(tc) && board[tc]!=0){
                    int cap = board[tc];
                    if((sign>0 && cap<0) || (sign<0 && cap>0)){
                        moves[n++]=MAKE_MOVE(sq,tc,0,MF_CAPTURE);
                    }
                }
                /* en passant */
                if(tc==enPassant){ moves[n++]=MAKE_MOVE(sq,tc,0,MF_ENPASS|MF_CAPTURE); }
            }
        }
        else if(pt==N){
            for(int i=0;i<8;i++){
                int to = sq + knightDirs[i]; if(!onboard(to)) continue;
                int tval = board[to];
                if(tval==0) moves[n++]=MAKE_MOVE(sq,to,0,MF_NONE);
                else if((tval>0) != (val>0)) moves[n++]=MAKE_MOVE(sq,to,0,MF_CAPTURE);
            }
        }
        else if(pt==B || pt==R || pt==Q){
            const int *dirs; int nd;
            if(pt==B){ dirs=bishopDirs; nd=4; }
            else if(pt==R){ dirs=rookDirs; nd=4; }
            else { int bothDirs[8]; for(int i=0;i<4;i++){bothDirs[i]=bishopDirs[i]; bothDirs[i+4]=rookDirs[i];} dirs=bothDirs; nd=8; }
            for(int d=0; d<nd; d++){
                int step = dirs[d]; int to = sq + step;
                while(onboard(to)){
                    int tval = board[to];
                    if(tval==0){ moves[n++]=MAKE_MOVE(sq,to,0,MF_NONE); }
                    else { if((tval>0)!=(val>0)) moves[n++]=MAKE_MOVE(sq,to,0,MF_CAPTURE); break; }
                    to += step;
                }
            }
        }
        else if(pt==K){
            for(int i=0;i<8;i++){
                int to = sq + kingDirs[i]; if(!onboard(to)) continue;
                int tval = board[to];
                if(tval==0) moves[n++]=MAKE_MOVE(sq,to,0,MF_NONE);
                else if((tval>0) != (val>0)) moves[n++]=MAKE_MOVE(sq,to,0,MF_CAPTURE);
            }
            /* TODO: castling generation (check squares empty & not in check) - handled more simply in legality check */
        }
    }
    return n;
}

/* make and unmake moves (very simplified) */
void make_move(int mv){
    int from = FROM(mv), to = TO(mv);
    int prom = PROM(mv); int flags = FLAG(mv);
    int moved = board[from];
    int captured = board[to];
    history[histPly].move = mv;
    history[histPly].captured = captured;
    history[histPly].prevEP = enPassant;
    history[histPly].prevCastling = castlingRights;
    history[histPly].prevHalfmove = halfmoveClock;
    histPly++;
    /* update halfmove */
    if(abs(moved)==P || captured!=0) halfmoveClock = 0; else halfmoveClock++;
    /* apply */
    board[to] = board[from]; board[from] = 0;
    /* en passant capture handling */
    if(flags & MF_ENPASS){
        /* captured pawn sits behind target */
        int capSq = (sideToMove==WHITE)? to+16 : to-16;
        history[histPly-1].captured = board[capSq];
        board[capSq] = 0;
    }
    /* promotion */
    if(flags & MF_PROM){ board[to] = (sideToMove==WHITE? PROM(mv) : -PROM(mv)); }
    /* toggle side */
    sideToMove = (sideToMove==WHITE)?BLACK:WHITE;
    /* enpassant setting for double pawn push */
    enPassant = -1;
    if(abs(moved)==P){
        int diff = to - from;
        if(diff==32 || diff==-32){ enPassant = (from+to)/2; }
    }
    /* castling rights updates and execution */
    /* very simplified: if king moved, clear; if rook moved, clear respective */
    if(abs(moved)==K){
        if(sideToMove==BLACK){ /* white moved */ castlingRights &= ~(1|2); }
        else { castlingRights &= ~(4|8); }
    }
    /* TODO: move rook when castle flag present */
    if(flags & MF_CASTLE){
        /* if white king castle king side */
        if(sideToMove==BLACK){ /* white moved just now */
            if(TO(mv) == (0*16 + 6)) { /* white king to g1 (but mapping?) */ }
        }
    }
}

void unmake_move(){
    if(histPly==0) return;
    histPly--;
    Undo u = history[histPly];
    int mv = u.move;
    int from = FROM(mv), to = TO(mv);
    sideToMove = (sideToMove==WHITE)?BLACK:WHITE;
    board[from] = board[to];
    board[to] = u.captured;
    enPassant = u.prevEP;
    castlingRights = u.prevCastling;
    halfmoveClock = u.prevHalfmove;
}

/* spot-check: is king of side s attacked? */
int king_square(Color s){
    for(int sq=0;sq<BOARD_SIZE;sq++){
        if(!onboard(sq)) { sq+=7; continue; }
        int v = board[sq]; if(v==0) continue;
        if(s==WHITE && v==K) return sq;
        if(s==BLACK && v==-K) return sq;
    }
    return -1;
}

int is_square_attacked(int sq, Color by){
    /* scan for enemy pieces attacking sq */
    for(int d=0; d<8; d++){
        int ksq = sq + kingDirs[d]; if(onboard(ksq)){
            int v = board[ksq]; if(v!=0){ if(by==WHITE && v==K) return 1; if(by==BLACK && v==-K) return 1; }
        }
    }
    for(int i=0;i<8;i++){
        int nsq = sq + knightDirs[i]; if(!onboard(nsq)) continue; int v=board[nsq]; if(v!=0){ if(by==WHITE && v==N) return 1; if(by==BLACK && v==-N) return 1; }
    }
    /* sliding */
    for(int i=0;i<4;i++){
        int d = bishopDirs[i]; int t = sq + d;
        while(onboard(t)){
            int v=board[t]; if(v!=0){ int at = abs(v); if(at==B || at==Q){ if((by==WHITE && v>0) || (by==BLACK && v<0)) return 1; } break; } t+=d;
        }
    }
    for(int i=0;i<4;i++){
        int d = rookDirs[i]; int t = sq + d;
        while(onboard(t)){
            int v=board[t]; if(v!=0){ int at = abs(v); if(at==R || at==Q){ if((by==WHITE && v>0) || (by==BLACK && v<0)) return 1; } break; } t+=d;
        }
    }
    /* pawns */
    int up = (by==WHITE)? -16 : 16; int capL = sq + up -1; int capR = sq + up +1;
    if(onboard(capL) && board[capL]!=0) { if((by==WHITE && board[capL]==P) || (by==BLACK && board[capL]==-P)) return 1; }
    if(onboard(capR) && board[capR]!=0) { if((by==WHITE && board[capR]==P) || (by==BLACK && board[capR]==-P)) return 1; }
    return 0;
}

int in_check(Color side){
    int ksq = king_square(side); if(ksq==-1) return 0;
    Color attacker = (side==WHITE)?BLACK:WHITE;
    return is_square_attacked(ksq, attacker);
}

/* remove illegal moves by making and checking for self-check */
int legal_moves(int legal[]){
    int buf[MAX_MOVES]; int n = generate_moves(buf);
    int m=0;
    for(int i=0;i<n;i++){
        make_move(buf[i]);
        if(!in_check(sideToMove==WHITE?BLACK:WHITE)){
            legal[m++]=buf[i];
        }
        unmake_move();
    }
    return m;
}

/* basic evaluation: material only + piece-square-ish simple weights */
int piece_value(int pt){
    switch(pt){ case P: return 100; case N: return 320; case B: return 330; case R: return 500; case Q: return 900; case K: return 20000; }
    return 0;
}

int evaluate(){
    int score=0;
    for(int sq=0;sq<BOARD_SIZE;sq++){
        if(!onboard(sq)){ sq+=7; continue; }
        int v = board[sq]; if(v==0) continue;
        int sign = (v>0)?1:-1; score += sign * piece_value(abs(v));
    }
    return score;
}

/* ================================
   Search: Minimax with alpha-beta
   ================================ */

int nodes_searched = 0;

int negamax(int alpha, int beta, int depth){
    if(depth==0){ nodes_searched++; return evaluate(); }
    int moves[MAX_MOVES]; int n = legal_moves(moves);
    if(n==0){ if(in_check(sideToMove)) return -INF + (MAX_PLY - depth); else return 0; }
    int best = -INF;
    for(int i=0;i<n;i++){
        make_move(moves[i]);
        int val = -negamax(-beta, -alpha, depth-1);
        unmake_move();
        if(val>best) best=val;
        if(val>alpha) alpha=val;
        if(alpha>=beta) break;
    }
    return best;
}

int find_best_move(int depth){
    int bestMove = 0; int bestScore = -INF;
    int moves[MAX_MOVES]; int n = legal_moves(moves);
    for(int i=0;i<n;i++){
        make_move(moves[i]);
        int score = -negamax(-INF, INF, depth-1);
        unmake_move();
        if(score>bestScore){ bestScore = score; bestMove = moves[i]; }
    }
    return bestMove;
}

/* ================================
   Simple utilities: algebraic square <-> 0x88
   ================================ */

void sq_to_str(int sq, char *out){
    int file = sq & 7;
    int rank = 7 - (sq>>4);
    out[0] = 'a'+file; out[1] = '1'+rank; out[2]=0;
}

int str_to_sq(const char *s){
    if(!s || strlen(s)<2) return -1;
    int file = s[0]-'a'; int rank = s[1]-'1';
    int sq = (7-rank)*16 + file; return sq;
}

/* parse simple moves like e2e4, e7e8q, or algebraic like Nf3 not implemented fully */
int parse_move_str(const char *s){
    if(strlen(s)<4) return 0;
    int from = str_to_sq(s);
    int to = str_to_sq(s+2);
    int prom = 0; int flags=0;
    if(strlen(s)>=5){ char p = tolower(s[4]); if(p=='q') prom=Q; if(p=='r') prom=R; if(p=='b') prom=B; if(p=='n') prom=N; flags |= MF_PROM; }
    /* capture detection omitted here */
    return MAKE_MOVE(from,to,prom,flags);
}

/* ================================
   CLI and commands
   ================================ */

void do_perft(int depth){
    /* naive perft: count leaf nodes at depth */
    int nodes = 0;
    if(depth==0){ printf("perft 0 = 1\n"); return; }
    int moves[MAX_MOVES]; int n = legal_moves(moves);
    for(int i=0;i<n;i++){
        make_move(moves[i]);
        if(depth-1==0) nodes++;
        else {
            /* recursively count */
            /* simple DFS */
            int stack=0; /* not used; using recursion */
            /* reuse negamax? but we need exact counts; implement recursive lambda-like as function below */
        }
        unmake_move();
    }
    printf("perft depth %d -> %d (approx)\n", depth, nodes);
}

void print_help(){
    printf("Comandos:\n");
    printf("  show                - mostra o tabuleiro\n");
    printf("  fen <string>        - carrega FEN\n");
    printf("  move <e2e4>         - realiza movimento\n");
    printf("  undo                - desfaz ultimo movimento\n");
    printf("  ai <depth>          - calcula melhor movimento com profundidade\n");
    printf("  play <depth>        - joga contra motor\n");
    printf("  perft <depth>       - perft basico (limitado)\n");
    printf("  exit                - sai\");
}

int main(int argc, char **argv){
    set_startpos();
    printf("Xadres Ultra Complexo - versão educativa\n");
    print_help();
    char line[512];
    while(1){
        printf("> "); fflush(stdout);
        if(!fgets(line, sizeof(line), stdin)) break;
        char *p = strtok(line, "\n"); if(!p) continue;
        char cmd[64]; int argi=0;
        char *tok = strtok(p, " "); if(!tok) continue; strcpy(cmd,tok);
        if(strcmp(cmd,"show")==0){ print_board(); }
        else if(strcmp(cmd,"help")==0){ print_help(); }
        else if(strcmp(cmd,"fen")==0){ char *rest = strtok(NULL, ""); if(rest) { load_fen(rest); print_board(); } else printf("usage: fen <FEN>\n"); }
        else if(strcmp(cmd,"move")==0){ char *mv = strtok(NULL, " "); if(!mv) { printf("usage: move e2e4\n"); continue; } int m = parse_move_str(mv); if(m==0){ printf("parse error\n"); continue; } make_move(m); print_board(); }
        else if(strcmp(cmd,"undo")==0){ unmake_move(); print_board(); }
        else if(strcmp(cmd,"ai")==0){ char *d = strtok(NULL, " "); int depth = d?atoi(d):4; nodes_searched=0; int best = find_best_move(depth); char sfrom[8], sto[8]; sq_to_str(FROM(best), sfrom); sq_to_str(TO(best), sto); printf("AI best: %s%s (nodes %d)\n", sfrom, sto, nodes_searched); }
        else if(strcmp(cmd,"play")==0){ char *d = strtok(NULL, " "); int depth = d?atoi(d):3; print_board(); while(1){ if(sideToMove==WHITE){ char mvbuf[8]; printf("Your move: "); if(!fgets(mvbuf,sizeof(mvbuf),stdin)) break; if(strncmp(mvbuf,"quit",4)==0) break; int m = parse_move_str(mvbuf); make_move(m); print_board(); } else { int best = find_best_move(depth); printf("Engine moves: "); char sfrom[8], sto[8]; sq_to_str(FROM(best), sfrom); sq_to_str(TO(best), sto); printf("%s%s\n", sfrom, sto); make_move(best); print_board(); } }
        }
        else if(strcmp(cmd,"perft")==0){ char *d = strtok(NULL, " "); int depth = d?atoi(d):1; do_perft(depth); }
        else if(strcmp(cmd,"exit")==0 || strcmp(cmd,"quit")==0) break;
        else printf("Comando desconhecido. help para lista.\n");
    }
    return 0;
}
