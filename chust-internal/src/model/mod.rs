use regex::{self, Regex};
use std::{
    fmt::{self, Display},
    lazy::SyncLazy,
    ops::Add,
};

pub const BOARD_LEN: usize = 8;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PieceType {
    Pawn,
    Knight,
    Bishop,
    Rook,
    Queen,
    King,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PieceColor {
    White,
    Black,
}
impl PieceColor {
    pub fn other(self) -> Self {
        match self {
            PieceColor::White => PieceColor::Black,
            PieceColor::Black => PieceColor::White,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Piece {
    WhitePawn,
    WhiteKnight,
    WhiteBishop,
    WhiteRook,
    WhiteQueen,
    WhiteKing,
    BlackPawn,
    BlackKnight,
    BlackBishop,
    BlackRook,
    BlackQueen,
    BlackKing,
}
impl Piece {
    pub fn new(piece_type: PieceType, piece_color: PieceColor) -> Self {
        match piece_color {
            PieceColor::White => match piece_type {
                PieceType::Pawn => Piece::WhitePawn,
                PieceType::Knight => Piece::WhiteKnight,
                PieceType::Bishop => Piece::WhiteBishop,
                PieceType::Rook => Piece::WhiteRook,
                PieceType::Queen => Piece::WhiteQueen,
                PieceType::King => Piece::WhiteKing,
            },
            PieceColor::Black => match piece_type {
                PieceType::Pawn => Piece::BlackPawn,
                PieceType::Knight => Piece::BlackKnight,
                PieceType::Bishop => Piece::BlackBishop,
                PieceType::Rook => Piece::BlackRook,
                PieceType::Queen => Piece::BlackQueen,
                PieceType::King => Piece::BlackKing,
            },
        }
    }
    pub fn piece_type(&self) -> PieceType {
        match self {
            Piece::WhitePawn => PieceType::Pawn,
            Piece::WhiteKnight => PieceType::Knight,
            Piece::WhiteBishop => PieceType::Bishop,
            Piece::WhiteRook => PieceType::Rook,
            Piece::WhiteQueen => PieceType::Queen,
            Piece::WhiteKing => PieceType::King,
            Piece::BlackPawn => PieceType::Pawn,
            Piece::BlackKnight => PieceType::Knight,
            Piece::BlackBishop => PieceType::Bishop,
            Piece::BlackRook => PieceType::Rook,
            Piece::BlackQueen => PieceType::Queen,
            Piece::BlackKing => PieceType::King,
        }
    }
    pub fn piece_color(&self) -> PieceColor {
        match self {
            Piece::WhitePawn => PieceColor::White,
            Piece::WhiteKnight => PieceColor::White,
            Piece::WhiteBishop => PieceColor::White,
            Piece::WhiteRook => PieceColor::White,
            Piece::WhiteQueen => PieceColor::White,
            Piece::WhiteKing => PieceColor::White,
            Piece::BlackPawn => PieceColor::Black,
            Piece::BlackKnight => PieceColor::Black,
            Piece::BlackBishop => PieceColor::Black,
            Piece::BlackRook => PieceColor::Black,
            Piece::BlackQueen => PieceColor::Black,
            Piece::BlackKing => PieceColor::Black,
        }
    }
    /// Given a piece at some coord in the context of some game, return the possible
    /// moves for that piece
    /// (ignoring other factors like check)
    pub fn possible_moves(&self, coord: Coord, game: &Game) -> Vec<GameMove> {
        const ORTHO_DIRS: &[Offset] = &[
            Offset::new(-1, 0),
            Offset::new(1, 0),
            Offset::new(0, -1),
            Offset::new(0, 1),
        ];
        const DIAG_DIRS: &[Offset] = &[
            Offset::new(-1, -1),
            Offset::new(-1, 1),
            Offset::new(1, -1),
            Offset::new(1, 1),
        ];
        const ALL_DIRS: &[Offset] = &[
            Offset::new(-1, -1),
            Offset::new(-1, 0),
            Offset::new(-1, 1),
            Offset::new(0, -1),
            Offset::new(0, 1),
            Offset::new(0, 1),
            Offset::new(0, 1),
            Offset::new(0, 1),
        ];
        const KNIGHT_DIRS: &[Offset] = &[
            Offset::new(-2, -1),
            Offset::new(-2, 1),
            Offset::new(-1, -2),
            Offset::new(-1, 2),
            Offset::new(1, -2),
            Offset::new(1, 2),
            Offset::new(2, -1),
            Offset::new(2, 1),
        ];
        let piece = match game.board.get(coord) {
            Tile::Empty => panic!("expected piece at {}", coord),
            Tile::Occupied(p) => p,
        };
        let is_friendly_piece = |coord: Coord| match game.board.get(coord) {
            Tile::Empty => false,
            Tile::Occupied(p) => p.piece_color() == piece.piece_color(),
        };
        let hopper_moves = |dirs: &[Offset]| {
            let mut game_moves = Vec::new();
            for &dir in dirs {
                let new_coord = match coord.offset(dir) {
                    Ok(c) => c,
                    Err(_) => continue,
                };
                if !is_friendly_piece(new_coord) {
                    game_moves.push(GameMove::new(coord, new_coord));
                }
            }
            game_moves
        };
        let rider_moves = |dirs: &[Offset]| {
            let mut game_moves = Vec::new();
            for &dir in dirs {
                let mut new_coord = match coord.offset(dir) {
                    Ok(c) => c,
                    Err(_) => continue,
                };
                while !is_friendly_piece(new_coord) {
                    game_moves.push(GameMove::new(coord, new_coord));
                    new_coord = match new_coord.offset(dir) {
                        Ok(c) => c,
                        Err(_) => break,
                    }
                }
            }
            game_moves
        };
        match self.piece_type() {
            PieceType::Pawn => {
                let mut game_moves = Vec::new();
                let forwards_dir = match piece.piece_color() {
                    PieceColor::White => Offset::new(0, 1),
                    PieceColor::Black => Offset::new(0, -1),
                };
                todo!();
                game_moves
            }
            PieceType::Knight => hopper_moves(KNIGHT_DIRS),
            PieceType::Bishop => rider_moves(DIAG_DIRS),
            PieceType::Rook => rider_moves(ORTHO_DIRS),
            PieceType::Queen => rider_moves(ALL_DIRS),
            PieceType::King => hopper_moves(ALL_DIRS),
        }
    }
    pub fn from_char(c: char) -> Result<Self, ()> {
        match c {
            'P' => Ok(Piece::WhitePawn),
            'N' => Ok(Piece::WhiteKnight),
            'B' => Ok(Piece::WhiteBishop),
            'R' => Ok(Piece::WhiteRook),
            'Q' => Ok(Piece::WhiteQueen),
            'K' => Ok(Piece::WhiteKing),
            'p' => Ok(Piece::BlackPawn),
            'n' => Ok(Piece::BlackKnight),
            'b' => Ok(Piece::BlackBishop),
            'r' => Ok(Piece::BlackRook),
            'q' => Ok(Piece::BlackQueen),
            'k' => Ok(Piece::BlackKing),
            _ => Err(()),
        }
    }
    pub fn other_color(self) -> Self {
        Piece::new(self.piece_type(), self.piece_color().other())
    }
    pub fn to_char(self) -> char {
        match self {
            Piece::WhitePawn => 'P',
            Piece::WhiteKnight => 'N',
            Piece::WhiteBishop => 'B',
            Piece::WhiteRook => 'R',
            Piece::WhiteQueen => 'Q',
            Piece::WhiteKing => 'K',
            Piece::BlackPawn => 'p',
            Piece::BlackKnight => 'n',
            Piece::BlackBishop => 'b',
            Piece::BlackRook => 'r',
            Piece::BlackQueen => 'q',
            Piece::BlackKing => 'k',
        }
    }
    pub fn to_char_pretty(self) -> char {
        const DARK_MODE: bool = false;
        let piece = if DARK_MODE { self.other_color() } else { self };
        match piece {
            Piece::WhitePawn => '♙',
            Piece::WhiteKnight => '♘',
            Piece::WhiteBishop => '♗',
            Piece::WhiteRook => '♖',
            Piece::WhiteQueen => '♕',
            Piece::WhiteKing => '♔',
            Piece::BlackPawn => '♟',
            Piece::BlackKnight => '♞',
            Piece::BlackBishop => '♝',
            Piece::BlackRook => '♜',
            Piece::BlackQueen => '♛',
            Piece::BlackKing => '♚',
        }
    }
}
impl Display for Piece {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let c = if f.alternate() {
            self.to_char_pretty()
        } else {
            self.to_char()
        };
        write!(f, "{}", c)
    }
}

#[derive(Debug, Clone, Copy)]
pub enum Tile {
    Empty,
    Occupied(Piece),
}
impl Tile {
    pub fn from_char(c: char) -> Result<Self, ()> {
        if c == '.' {
            Ok(Tile::Empty)
        } else {
            match Piece::from_char(c) {
                Ok(p) => Ok(Tile::Occupied(p)),
                Err(e) => Err(e),
            }
        }
    }
    pub fn to_char(self) -> char {
        match self {
            Tile::Empty => '.',
            Tile::Occupied(p) => p.to_char(),
        }
    }
    pub fn to_char_pretty(self) -> char {
        match self {
            Tile::Empty => '·',
            Tile::Occupied(p) => p.to_char_pretty(),
        }
    }
}
impl Display for Tile {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let c = if f.alternate() {
            self.to_char_pretty()
        } else {
            self.to_char()
        };
        write!(f, "{}", c)
    }
}

/// Represents a coordinate on the chessboard
#[derive(Debug, Clone, Copy)]
pub struct Coord(u8);
impl Coord {
    pub fn new(file: u8, rank: u8) -> Self {
        assert!(file < 8);
        assert!(rank < 8);
        Coord((file << 4) + rank)
    }
    pub fn offset(self, offset: Offset) -> Result<Self, ()> {
        let file = self.file() as i8 + offset.file();
        let rank = self.rank() as i8 + offset.rank();
        match (file, rank) {
            (0..=7, 0..=7) => Ok(Coord::new(file as u8, rank as u8)),
            _ => Err(()),
        }
    }
    pub fn file(&self) -> u8 {
        (self.0 >> 4) & 0b0111
    }
    pub fn rank(&self) -> u8 {
        self.0 & 0b0111
    }
    pub fn from_alg(text: &str) -> Result<Self, ()> {
        let bytes = text.as_bytes();
        if bytes.len() != 2 {
            return Err(());
        }
        let file_min = u32::from('a') as u8;
        let file_max = u32::from('h') as u8;
        let rank_min = u32::from('1') as u8;
        let rank_max = u32::from('8') as u8;
        if (file_min..=file_max).contains(&bytes[0]) && (rank_min..=rank_max).contains(&bytes[1]) {
            return Ok(Coord::new(bytes[0] - file_min, bytes[1] - rank_min));
        }
        Err(())
    }
    pub fn to_alg(self) -> &'static str {
        static ALG: SyncLazy<String> = SyncLazy::new(|| {
            let mut text = String::new();
            for file in 'a'..='h' {
                for rank in '1'..='8' {
                    text.push(file);
                    text.push(rank);
                }
            }
            text
        });
        let idx = 2 * (self.file() as usize * BOARD_LEN + self.rank() as usize);
        std::str::from_utf8(&ALG.as_bytes()[idx..idx + 2]).unwrap()
    }
}
impl Display for Coord {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_alg())
    }
}

/// Represents an offset between two coordinates on a chessboard
#[derive(Debug, Clone, Copy)]
pub struct Offset(i8, i8);
impl Offset {
    pub const fn new(file: i8, rank: i8) -> Self {
        assert!(matches!(file, -7..=7));
        assert!(matches!(rank, -7..=7));
        Offset(file, rank)
    }
    pub fn file(&self) -> i8 {
        self.0
    }
    pub fn rank(&self) -> i8 {
        self.1
    }
}
impl Add<Offset> for Offset {
    type Output = Result<Offset, ()>;

    fn add(self, rhs: Offset) -> Self::Output {
        let file = self.file() + rhs.file();
        let rank = self.rank() + rhs.rank();
        match (file, rank) {
            (-7..=7, -7..=-7) => Ok(Offset(file, rank)),
            _ => Err(()),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct GameMove {
    pub from: Coord,
    pub to: Coord,
}
impl GameMove {
    pub fn new(from: Coord, to: Coord) -> Self {
        GameMove { from, to }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Board {
    pub tiles: [[Tile; BOARD_LEN]; BOARD_LEN],
}
impl Board {
    pub fn new() -> Self {
        const EM: Tile = Tile::Empty;
        const BP: Tile = Tile::Occupied(Piece::BlackPawn);
        const BN: Tile = Tile::Occupied(Piece::BlackKnight);
        const BB: Tile = Tile::Occupied(Piece::BlackBishop);
        const BR: Tile = Tile::Occupied(Piece::BlackRook);
        const BQ: Tile = Tile::Occupied(Piece::BlackQueen);
        const BK: Tile = Tile::Occupied(Piece::BlackKing);
        const WP: Tile = Tile::Occupied(Piece::WhitePawn);
        const WN: Tile = Tile::Occupied(Piece::WhiteKnight);
        const WB: Tile = Tile::Occupied(Piece::WhiteBishop);
        const WR: Tile = Tile::Occupied(Piece::WhiteRook);
        const WQ: Tile = Tile::Occupied(Piece::WhiteQueen);
        const WK: Tile = Tile::Occupied(Piece::WhiteKing);
        Board {
            tiles: [
                [WR, WP, EM, EM, EM, EM, BP, BR],
                [WN, WP, EM, EM, EM, EM, BP, BN],
                [WB, WP, EM, EM, EM, EM, BP, BB],
                [WQ, WP, EM, EM, EM, EM, BP, BQ],
                [WK, WP, EM, EM, EM, EM, BP, BK],
                [WB, WP, EM, EM, EM, EM, BP, BB],
                [WN, WP, EM, EM, EM, EM, BP, BN],
                [WR, WP, EM, EM, EM, EM, BP, BR],
            ],
        }
    }
    pub fn new_empty() -> Self {
        Board {
            tiles: [[Tile::Empty; BOARD_LEN]; BOARD_LEN],
        }
    }
    pub fn get(&self, coord: Coord) -> Tile {
        self.tiles[coord.file() as usize][coord.rank() as usize]
    }
    pub fn from_fen(text: &str) -> Result<Board, ()> {
        static PATTERN: SyncLazy<Regex> = SyncLazy::new(|| {
            Regex::new(r"^[PNBRQKpnbrqk1-8]{1,8}(?:/[PNBRQKpnbrqk1-8]{1,8}){7}$").unwrap()
        });
        if !PATTERN.is_match(text) {
            return Err(());
        }
        let mut tiles = [[Tile::Empty; BOARD_LEN]; BOARD_LEN];
        for (j, rank) in text.split('/').enumerate() {
            let j = BOARD_LEN - j - 1;
            let mut i = 0;
            for c in rank.chars() {
                if let Some(d) = c.to_digit(10) {
                    i += d as usize;
                    continue;
                }
                if let Ok(p) = Piece::from_char(c) {
                    if i >= 8 {
                        return Err(());
                    }
                    tiles[i][j] = Tile::Occupied(p);
                    i += 1;
                    continue;
                }
                return Err(());
            }
            if i != 8 {
                return Err(());
            }
        }
        Ok(Board { tiles })
    }
    pub fn to_fen(&self) -> String {
        let mut text = String::new();
        for j in (0..BOARD_LEN).rev() {
            for i in 0..BOARD_LEN {
                if let Tile::Occupied(p) = self.tiles[i][j] {
                    text.push(p.to_char());
                } else {
                    let last = text.chars().rev().next();
                    if let Some(d) = last.map(|c| c.to_digit(10)).flatten() {
                        text.pop();
                        text.push(char::from_digit(d + 1, 10).unwrap());
                    } else {
                        text.push('1');
                    }
                }
            }
            if j != 0 {
                text.push('/');
            }
        }
        text
    }
}
impl Display for Board {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let alternate = f.alternate();
        if alternate {
            write!(f, "┌────────┐\n")?;
        } else {
            // write!(f, "+--------+\n")?;
        }
        for rank in (0..BOARD_LEN).rev() {
            if alternate {
                write!(f, "{}", rank + 1)?;
            } else {
                // write!(f, "{}", rank + 1)?;
            }
            for file in 0..BOARD_LEN {
                let tile = self.tiles[file][rank];
                if alternate {
                    write!(f, "{:#}", tile)?;
                } else {
                    write!(f, "{}", tile)?;
                }
            }
            if alternate {
                write!(f, "│\n")?;
            } else {
                // write!(f, "|\n")?;
                write!(f, "\n")?;
            }
        }
        if alternate {
            write!(f, "└abcdefgh┘\n")?;
        } else {
            // write!(f, "+abcdefgh+\n")?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone, Copy)]
pub struct CanCastle(u8);
impl CanCastle {
    pub fn new(white_king: bool, white_queen: bool, black_king: bool, black_queen: bool) -> Self {
        let mut can_castle = CanCastle(0);
        can_castle.set_bit(0, white_king);
        can_castle.set_bit(1, white_queen);
        can_castle.set_bit(2, black_king);
        can_castle.set_bit(3, black_queen);
        can_castle
    }
    fn bit(&self, bit: u8) -> bool {
        self.0 & (1 << bit) != 0
    }
    fn set_bit(&mut self, bit: u8, val: bool) {
        if val {
            self.0 |= 1 << bit;
        } else {
            self.0 &= !(1 << bit);
        }
    }
    pub fn white_king(&self) -> bool {
        self.bit(0)
    }
    pub fn set_white_king(&mut self, val: bool) {
        self.set_bit(0, val)
    }
    pub fn white_queen(&self) -> bool {
        self.bit(1)
    }
    pub fn set_white_queen(&mut self, val: bool) {
        self.set_bit(1, val)
    }
    pub fn black_king(&self) -> bool {
        self.bit(2)
    }
    pub fn set_black_king(&mut self, val: bool) {
        self.set_bit(2, val)
    }
    pub fn black_queen(&self) -> bool {
        self.bit(3)
    }
    pub fn set_black_queen(&mut self, val: bool) {
        self.set_bit(3, val)
    }
    pub fn from_fen(fen: &str) -> Result<Self, ()> {
        let mut can_castle = CanCastle(0);
        if fen == "-" {
            return Ok(can_castle);
        }
        for c in fen.chars() {
            match c {
                'K' => can_castle.set_white_king(true),
                'Q' => can_castle.set_white_queen(true),
                'k' => can_castle.set_black_king(true),
                'q' => can_castle.set_black_queen(true),
                _ => return Err(()),
            }
        }
        Ok(can_castle)
    }
    pub fn to_fen(&self) -> String {
        let mut text = String::new();
        if self.white_king() {
            text.push('K');
        }
        if self.white_queen() {
            text.push('Q');
        }
        if self.black_king() {
            text.push('k');
        }
        if self.black_queen() {
            text.push('q');
        }
        if text.len() == 0 {
            text.push('-');
        }
        text
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Game {
    pub board: Board,
    pub to_move: PieceColor,
    pub can_castle: CanCastle,
    pub en_passent: Option<Coord>,
    pub half_move: u8,
    pub full_move: u32,
}
impl Game {
    pub fn new() -> Self {
        let board = Board::new();
        let to_move = PieceColor::White;
        let can_castle = CanCastle::new(true, true, true, true);
        let en_passent = None;
        let half_move = 0;
        let full_move = 1;
        Game {
            board,
            to_move,
            can_castle,
            en_passent,
            half_move,
            full_move,
        }
    }
    pub fn from_fen(text: &str) -> Result<Self, ()> {
        static PATTERN: SyncLazy<Regex> = SyncLazy::new(|| {
            Regex::new(r"([pnbrqkPNBRQK1-8/]+) ([wb]) ([KQkq]+|-) ([a-h][1-8]|-) (\d+) (\d+)")
                .unwrap()
        });
        let caps = match PATTERN.captures(text) {
            Some(caps) => caps,
            None => return Err(()),
        };
        let board = Board::from_fen(&caps[1])?;
        let to_move = match &caps[2] {
            "w" => PieceColor::White,
            "b" => PieceColor::Black,
            _ => return Err(()),
        };
        let can_castle = CanCastle::from_fen(&caps[3])?;
        let en_passent = match &caps[4] {
            "-" => None,
            text => match Coord::from_alg(text) {
                Ok(coord) => Some(coord),
                Err(()) => return Err(()),
            },
        };
        let half_move = match caps[5].parse() {
            Ok(x) => x,
            Err(_) => return Err(()),
        };
        let full_move = match caps[6].parse() {
            Ok(x) => x,
            Err(_) => return Err(()),
        };
        Ok(Game {
            board,
            to_move,
            can_castle,
            en_passent,
            half_move,
            full_move,
        })
    }
    pub fn to_fen(&self) -> String {
        let board = self.board.to_fen();
        let to_move = match self.to_move {
            PieceColor::White => "w",
            PieceColor::Black => "b",
        };
        let can_castle = self.can_castle.to_fen();
        let en_passent = match self.en_passent {
            Some(coord) => coord.to_alg(),
            None => "-",
        };
        let half_move = format!("{}", self.half_move);
        let full_move = format!("{}", self.full_move);
        format!(
            "{} {} {} {} {} {}",
            board, to_move, can_castle, en_passent, half_move, full_move
        )
    }
}
impl Display for Game {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if f.alternate() {
            write!(f, "{:#}", self.board)?;
        } else {
            write!(f, "{}", self.board)?;
        }
        let to_move = match self.to_move {
            PieceColor::White => "White",
            PieceColor::Black => "Black",
        };
        let can_castle = self.can_castle.to_fen();
        let en_passent = match self.en_passent {
            Some(coord) => coord.to_alg(),
            None => "-",
        };
        let half_move = self.half_move;
        let full_move = self.full_move;
        writeln!(f, "{} {} {}", to_move, full_move, half_move)?;
        writeln!(f, "{} {}", can_castle, en_passent)?;
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn can_parse_coords() {
        for file in 'a'..='h' {
            for rank in '1'..='8' {
                let mut text = String::new();
                text.push(file);
                text.push(rank);
                let coord = Coord::from_alg(&text).unwrap();
                assert_eq!(&text, coord.to_alg());
            }
        }

        assert!(Coord::from_alg("").is_err());
        assert!(Coord::from_alg("a1a1").is_err());
        assert!(Coord::from_alg("a9").is_err());
        assert!(Coord::from_alg("p1").is_err());
        assert!(Coord::from_alg("11").is_err());
        assert!(Coord::from_alg("aa").is_err());
        assert!(Coord::from_alg("1a").is_err());
    }

    #[test]
    fn can_parse_fen() {
        let fens = [
            "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1",
            "rnbqkbnr/pppppppp/8/8/4P3/8/PPPP1PPP/RNBQKBNR b KQkq e3 0 1",
            "rnbqkbnr/pp1ppppp/8/2p5/4P3/8/PPPP1PPP/RNBQKBNR w KQkq c6 0 2",
            "rnbqkbnr/pp1ppppp/8/2p5/4P3/5N2/PPPP1PPP/RNBQKB1R b KQkq - 1 2",
            "r3rk2/1b2p2N/p1pp2Q1/8/8/1qP4P/1b3PP1/3RR1K1 b - - 2 23",
        ];
        for fen in fens {
            let fen2 = Game::from_fen(fen).unwrap().to_fen();
            assert_eq!(fen, fen2);
        }
    }
}
