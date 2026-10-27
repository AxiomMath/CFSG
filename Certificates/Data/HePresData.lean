module

public section

namespace CFSG.ComponentClassification.AS81.HePres.Native

@[expose] def ofCodes (c : List Nat) : List (Fin 8 × Bool) :=
  c.map fun x => (⟨x / 2 % 8, Nat.mod_lt _ (by decide)⟩, decide (x % 2 = 0))

@[expose] def hePiRBCodes : List (List Nat) :=
  [[6, 6],
    [0, 0, 0, 0],
    [0, 5, 0, 5],
    [0, 6, 0, 7],
    [2, 2, 2, 2],
    [0, 2, 0, 3, 5, 5],
    [0, 4, 0, 6, 5, 6],
    [2, 4, 2, 5, 5, 5],
    [2, 5, 6, 2, 5, 7],
    [2, 6, 4, 2, 7, 4],
    [4, 4, 6, 5, 5, 7],
    [0, 2, 0, 2, 0, 2, 0, 2]]

@[expose] def hePiR12Codes : List (List Nat) :=
  [[8, 8, 8],
    [0, 6, 8, 1, 7, 9],
    [2, 8, 2, 9, 6, 8, 5],
    [0, 0, 2, 8, 1, 4, 9, 2]]

@[expose] def hePiR13Codes : List (List Nat) :=
  [[10, 10, 10],
    [0, 5, 5, 10, 0, 11],
    [0, 0, 2, 6, 11, 2, 11],
    [2, 2, 6, 11, 5, 2, 10]]

@[expose] def hePiRCCodes : List (List Nat) :=
  [[2, 8, 11, 9, 11, 4, 9, 10]]

@[expose] def hePiR23Codes : List (List Nat) :=
  [[14, 14, 14],
    [0, 13, 0, 13],
    [0, 14, 2, 6, 14],
    [0, 2, 2, 14, 5, 14],
    [0, 2, 14, 3, 12, 15, 5]]

@[expose] def hePiRNECodes : List (List Nat) :=
  [[4, 8, 6, 15, 9, 13, 9, 12, 8, 13]]

@[expose] def hePiRNFCodes : List (List Nat) :=
  [[0, 12, 14, 11, 14, 10, 14, 11, 15, 10, 4]]

@[expose] def hePiRelsCodes : List (List Nat) :=
  hePiRBCodes ++ hePiR12Codes ++ hePiR13Codes ++ hePiRCCodes ++ hePiR23Codes ++ hePiRNECodes ++
    hePiRNFCodes

@[expose] def hePiRelsCCodes : List (List Nat) :=
  hePiRBCodes ++ hePiR12Codes ++ hePiR13Codes ++ hePiRCCodes

@[expose] def hePiRelsECodes : List (List Nat) :=
  hePiRBCodes ++ hePiR12Codes ++ hePiR23Codes ++ hePiRNECodes

@[expose] def hePiRelsFCodes : List (List Nat) :=
  hePiRBCodes ++ hePiR13Codes ++ hePiR23Codes ++ hePiRNFCodes

@[expose] def hePiRels23Codes : List (List Nat) := hePiRBCodes ++ hePiR23Codes

@[expose] def hePiRels : List (List (Fin 8 × Bool)) := hePiRelsCodes.map ofCodes

@[expose] def hePiRelsC : List (List (Fin 8 × Bool)) := hePiRelsCCodes.map ofCodes

@[expose] def hePiRelsE : List (List (Fin 8 × Bool)) := hePiRelsECodes.map ofCodes

@[expose] def hePiRelsF : List (List (Fin 8 × Bool)) := hePiRelsFCodes.map ofCodes

@[expose] def hePiRels23 : List (List (Fin 8 × Bool)) := hePiRels23Codes.map ofCodes

@[expose] def hePiCArrs0 : Array (Array Nat) :=
  #[#[0, 1, 3, 2, 4, 5, 7, 6, 12, 13, 15, 14, 8, 9, 11, 10, 24, 25, 27, 26, 28, 29, 31, 30, 20, 21,
      23, 22, 16, 17, 19, 18],
    #[0, 1, 2, 3, 7, 6, 5, 4, 13, 12, 15, 14, 10, 11, 8, 9, 26, 27, 24, 25, 29, 28, 31, 30, 23, 22,
      21, 20, 16, 17, 18, 19],
    #[0, 1, 3, 2, 6, 7, 5, 4, 14, 15, 13, 12, 8, 9, 11, 10, 27, 26, 24, 25, 29, 28, 30, 31, 21, 20,
      22, 23, 19, 18, 16, 17],
    #[0, 1, 3, 2, 4, 5, 7, 6, 12, 13, 15, 14, 8, 9, 11, 10, 21, 20, 22, 23, 17, 16, 18, 19, 25, 24,
      26, 27, 29, 28, 30, 31],
    #[0, 1, 2, 3, 8, 9, 10, 11, 12, 13, 14, 15, 4, 5, 6, 7, 16, 17, 18, 19, 24, 25, 26, 27, 28, 29,
      30, 31, 20, 21, 22, 23],
    #[0, 1, 4, 5, 6, 7, 2, 3, 8, 9, 12, 13, 14, 15, 10, 11, 18, 19, 22, 23, 20, 21, 16, 17, 26, 27,
      30, 31, 28, 29, 24, 25],
    #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
      26, 27, 28, 29, 30, 31],
    #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
      26, 27, 28, 29, 30, 31]]

@[expose] def hePiCArrs1 : Array (Array Nat) :=
  #[#[0, 1, 3, 2, 7, 6, 4, 5, 8, 9, 11, 10, 15, 14, 12, 13, 24, 25, 27, 26, 31, 30, 28, 29, 16, 17,
      19, 18, 23, 22, 20, 21],
    #[0, 1, 3, 2, 7, 6, 4, 5, 14, 15, 13, 12, 9, 8, 10, 11, 20, 21, 23, 22, 19, 18, 16, 17, 26, 27,
      25, 24, 29, 28, 30, 31],
    #[0, 1, 3, 2, 7, 6, 4, 5, 13, 12, 14, 15, 10, 11, 9, 8, 28, 29, 31, 30, 27, 26, 24, 25, 17, 16,
      18, 19, 22, 23, 21, 20],
    #[0, 1, 2, 3, 7, 6, 5, 4, 8, 9, 10, 11, 15, 14, 13, 12, 25, 24, 27, 26, 30, 31, 28, 29, 17, 16,
      19, 18, 22, 23, 20, 21],
    #[0, 1, 4, 5, 6, 7, 2, 3, 8, 9, 12, 13, 14, 15, 10, 11, 16, 17, 20, 21, 22, 23, 18, 19, 24, 25,
      28, 29, 30, 31, 26, 27],
    #[0, 1, 2, 3, 9, 8, 11, 10, 13, 12, 15, 14, 4, 5, 6, 7, 16, 17, 18, 19, 25, 24, 27, 26, 29, 28,
      31, 30, 20, 21, 22, 23],
    #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
      26, 27, 28, 29, 30, 31],
    #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
      26, 27, 28, 29, 30, 31]]

@[expose] def hePiCArrs (s : Bool) : Array (Array Nat) := if s then hePiCArrs1 else hePiCArrs0

@[expose] def hePiEArrs : Array (Array Nat) :=
  #[#[13, 12, 14, 15, 9, 8, 10, 11, 1, 0, 2, 3, 5, 4, 6, 7, 22, 23, 21, 20, 18, 19, 17, 16, 26, 27,
      25, 24, 30, 31, 29, 28, 59, 58, 56, 57, 63, 62, 60, 61, 55, 54, 52, 53, 51, 50, 48, 49, 32,
      33, 35, 34, 36, 37, 39, 38, 44, 45, 47, 46, 40, 41, 43, 42],
    #[41, 45, 33, 37, 40, 44, 32, 36, 43, 47, 35, 39, 42, 46, 34, 38, 55, 51, 63, 59, 54, 50, 62,
      58, 53, 49, 61, 57, 52, 48, 60, 56, 14, 10, 6, 2, 15, 11, 7, 3, 12, 8, 4, 0, 13, 9, 5, 1, 16,
      20, 24, 28, 17, 21, 25, 29, 18, 22, 26, 30, 19, 23, 27, 31],
    #[42, 43, 41, 40, 46, 47, 45, 44, 38, 39, 37, 36, 34, 35, 33, 32, 49, 48, 50, 51, 53, 52, 54,
      55, 61, 60, 62, 63, 57, 56, 58, 59, 28, 29, 31, 30, 24, 25, 27, 26, 16, 17, 19, 18, 20, 21,
      23, 22, 7, 6, 4, 5, 3, 2, 0, 1, 11, 10, 8, 9, 15, 14, 12, 13],
    #[18, 22, 30, 26, 19, 23, 31, 27, 17, 21, 29, 25, 16, 20, 28, 24, 12, 8, 0, 4, 13, 9, 1, 5, 15,
      11, 3, 7, 14, 10, 2, 6, 43, 47, 39, 35, 42, 46, 38, 34, 40, 44, 36, 32, 41, 45, 37, 33, 53,
      49, 57, 61, 52, 48, 56, 60, 54, 50, 58, 62, 55, 51, 59, 63],
    #[9, 18, 36, 63, 23, 12, 58, 33, 46, 53, 3, 24, 48, 43, 29, 6, 13, 22, 32, 59, 19, 8, 62, 37,
      42, 49, 7, 28, 52, 47, 25, 2, 1, 26, 44, 55, 31, 4, 50, 41, 38, 61, 11, 16, 56, 35, 21, 14, 5,
      30, 40, 51, 27, 0, 54, 45, 34, 57, 15, 20, 60, 39, 17, 10],
    #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
      26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48,
      49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63],
    #[3, 0, 2, 1, 11, 8, 10, 9, 15, 12, 14, 13, 7, 4, 6, 5, 22, 21, 23, 20, 30, 29, 31, 28, 26, 25,
      27, 24, 18, 17, 19, 16, 41, 42, 40, 43, 33, 34, 32, 35, 37, 38, 36, 39, 45, 46, 44, 47, 60,
      63, 61, 62, 52, 55, 53, 54, 48, 51, 49, 50, 56, 59, 57, 58],
    #[60, 61, 62, 63, 52, 53, 54, 55, 48, 49, 50, 51, 56, 57, 58, 59, 12, 13, 14, 15, 4, 5, 6, 7, 0,
      1, 2, 3, 8, 9, 10, 11, 44, 45, 46, 47, 36, 37, 38, 39, 32, 33, 34, 35, 40, 41, 42, 43, 28, 29,
      30, 31, 20, 21, 22, 23, 16, 17, 18, 19, 24, 25, 26, 27]]

@[expose] def hePiFArrs : Array (Array Nat) :=
  #[#[50, 51, 49, 48, 54, 55, 53, 52, 62, 63, 61, 60, 58, 59, 57, 56, 34, 35, 33, 32, 38, 39, 37,
      36, 46, 47, 45, 44, 42, 43, 41, 40, 2, 3, 1, 0, 6, 7, 5, 4, 14, 15, 13, 12, 10, 11, 9, 8, 18,
      19, 17, 16, 22, 23, 21, 20, 30, 31, 29, 28, 26, 27, 25, 24],
    #[32, 36, 44, 40, 33, 37, 45, 41, 35, 39, 47, 43, 34, 38, 46, 42, 62, 58, 50, 54, 63, 59, 51,
      55, 61, 57, 49, 53, 60, 56, 48, 52, 25, 29, 21, 17, 24, 28, 20, 16, 26, 30, 22, 18, 27, 31,
      23, 19, 7, 3, 11, 15, 6, 2, 10, 14, 4, 0, 8, 12, 5, 1, 9, 13],
    #[50, 51, 49, 48, 54, 55, 53, 52, 62, 63, 61, 60, 58, 59, 57, 56, 44, 45, 47, 46, 40, 41, 43,
      42, 32, 33, 35, 34, 36, 37, 39, 38, 11, 10, 8, 9, 15, 14, 12, 13, 7, 6, 4, 5, 3, 2, 0, 1, 21,
      20, 22, 23, 17, 16, 18, 19, 25, 24, 26, 27, 29, 28, 30, 31],
    #[40, 44, 32, 36, 41, 45, 33, 37, 42, 46, 34, 38, 43, 47, 35, 39, 61, 57, 53, 49, 60, 56, 52,
      48, 63, 59, 55, 51, 62, 58, 54, 50, 2, 6, 10, 14, 3, 7, 11, 15, 0, 4, 8, 12, 1, 5, 9, 13, 23,
      19, 31, 27, 22, 18, 30, 26, 21, 17, 29, 25, 20, 16, 28, 24],
    #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
      26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48,
      49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63],
    #[44, 50, 11, 21, 55, 41, 16, 14, 1, 31, 38, 56, 26, 4, 61, 35, 45, 51, 10, 20, 54, 40, 17, 15,
      0, 30, 39, 57, 27, 5, 60, 34, 46, 48, 9, 23, 53, 43, 18, 12, 3, 29, 36, 58, 24, 6, 63, 33, 47,
      49, 8, 22, 52, 42, 19, 13, 2, 28, 37, 59, 25, 7, 62, 32],
    #[56, 59, 57, 58, 52, 55, 53, 54, 60, 63, 61, 62, 48, 51, 49, 50, 8, 11, 9, 10, 4, 7, 5, 6, 12,
      15, 13, 14, 0, 3, 1, 2, 40, 43, 41, 42, 36, 39, 37, 38, 44, 47, 45, 46, 32, 35, 33, 34, 24,
      27, 25, 26, 20, 23, 21, 22, 28, 31, 29, 30, 16, 19, 17, 18],
    #[62, 63, 60, 61, 50, 51, 48, 49, 58, 59, 56, 57, 54, 55, 52, 53, 20, 21, 22, 23, 24, 25, 26,
      27, 16, 17, 18, 19, 28, 29, 30, 31, 1, 0, 3, 2, 13, 12, 15, 14, 5, 4, 7, 6, 9, 8, 11, 10, 43,
      42, 41, 40, 39, 38, 37, 36, 47, 46, 45, 44, 35, 34, 33, 32]]

@[expose] def hePiHeWord0 : String :=
  "abbbabbbabbbabbbBBAabbbabbbabbbabbbabbabbbabbbabbbabbbBBAabbbabbbabbbabbbabbbaBBbbbbBBBBbbABB" ++
    "BBABBBABBBABBBAbaBBbbbbBBBABBBABBBABBBABBBBbbABBBBABBBABBBABBBAbaBBbbbbBBBABBBABBBABBBABBBB" ++
    "bbABBBBABBBABBBABBBAbaBBbbbbBBBABBBABBBABBBABBBBbbABBBBABBBABBBABBBAbaBBbbbbBBBABBBABBBABBB" ++
    "ABBBBbbABBBBABBBABBBABBBAbaBBbbbbBBBABBBABBBABBBABBBBbbABBBBABBBABBBABBBAbaBBbbbbBBBABBBABB" ++
    "BABBBABBBBbbABBBBABBBABBBABBBAbaBBbbbbBBBABBBABBBABBBABBBBbbABBBBABBBABBBABBBAbaBBbbbbBBBAB" ++
    "BBABBBABBBABBBBbbABBBBABBBABBBABBBAbaBBbbbbBBBABBBABBBABBBABbaBbBbABbBBBABBBABBBABBBABbaBbB" ++
    "BBABBBABBBABBBABbABbBBBABBBABBBABBBABbaBbBBBABBBABBBABBBABBbaABbbBBBABBBABBBABBBABBbaBBBABB" ++
    "BABBBABBBAABbbBBBABBBABBBABBBABBbaBBBABBBABBBABBBAABbbBBBABBBABBBABBBABBbaBBBABBBABBBABBBAA" ++
    "BbbBBBABBBABBBABBBABBbaBBBABBBABBBABBBAABbbBBBABBBABBBABBBABBbaBBBABBBABBBABBBAABbbBBBABBBA" ++
    "BBBABBBABBbaBBBABBBABBBABBBAABbbBBBABBBABBBABBBABBbaBBBABBBABBBABBBAABbbBBBABBBABBBABBBABBb" ++
    "aBBBABBBABBBABBBAABbbBBBABBBABBBABBBABBbaBBBABBBABBBABBBAABbbBBBABBBABBBABBBABBbaBBBABBBABB" ++
    "BABBBAABbbBBBABBBABBBABBBABBbaBBBABBBABBBABBBAabbbabbbabbbabbbBBAabbbabbbabbbabbbabbabbbabb" ++
    "babbbabbbBBAabbbabbbabbbabbbabbbaBBbbbbBBBBbbABBBBABBBABBBABBBAbaBBbbbbBBBABBBABBBABBBABBBB" ++
    "bbABBBBABBBABBBABBBAbaBBbbbbBBBABBBABBBABBBABBBBbbABBBBABBBABBBABBBAbaBBbbbbBBBABBBABBBABBB" ++
    "ABBBBbbABBBBABBBABBBABBBAbaBBbbbbBBBABBBABBBABBBABBBBbbABBBBABBBABBBABBBAbaBBbbbbBBBABBBABB" ++
    "BABBBABBBBbbABBBBABBBABBBABBBAbaBBbbbbBBBABBBABBBABBBABBBBbbABBBBABBBABBBABBBAbaBBbbbbBBBAB" ++
    "BBABBBABBBABBBBbbABBBBABBBABBBABBBAbaBBbbbbBBBABBBABBBABBBABBBBbbABBBBABBBABBBABBBAbaBBbbbb" ++
    "BBBABBBABBBABBBABbaBbBbABbBBBABBBABBBABBBABbaBbBBBABBBABBBABBBABbABbBBBABBBABBBABBBABbaBbBB" ++
    "BABBBABBBABBBA"

@[expose] def hePiHeWord1 : String :=
  "abbbabbbabbbabbbBBBBbbABabbbabbbabbbabbbbaBBbbbbabbbabbbabbbabbbBBBBbbABabbbabbbabbbabbbbaBBb" ++
    "bbbabbbabbbabbbabbbBBBBbbABabbbabbbabbbabbbbaBBbbbbabbbabbbabbbabbbBBBBbbABabbbabbbabbbabbb" ++
    "baBBbbbbabbbabbbabbbabbbBBBBbbABabbbabbbabbbabbbbaBBbbbbabbbabbbabbbabbbBBBBbbABabbbabbbabb" ++
    "babbbbaBBbbbbabbbabbbabbbabbbBBBBbbABabbbabbbabbbabbbbaBBbbbbabbbabbbabbbabbbBBBBbbABabbbab" ++
    "bbabbbabbbbaBBbbbbabbbabbbabbbabbbBBBBbbABabbbabbbabbbabbbbaBBbbbbBBBBbbABabbbabbbabbbabbbB" ++
    "BBBbbABabbbabbbabbbabbbbaBBbbbbabbbabbbabbbabbbBBBBbbABabbbabbbabbbabbbbaBBbbbbabbbabbbabbb" ++
    "abbbBBBBbbABabbbabbbabbbabbbbaBBbbbbabbbabbbabbbabbbBBBBbbABabbbabbbabbbabbbbaBBbbbbabbbabb" ++
    "babbbabbbBBBBbbABabbbabbbabbbabbbbaBBbbbbabbbabbbabbbabbbBBBBbbABabbbabbbabbbabbbbaBBbbbbab" ++
    "bbabbbabbbabbbBBBBbbABabbbabbbabbbabbbbaBBbbbbabbbabbbabbbabbbBBBBbbABabbbabbbabbbabbbbaBBb" ++
    "bbbabbbabbbabbbabbbBBBBbbABabbbabbbabbbabbbbaBBbbbbBBBBbbABBBbaABbbBBBABBBABBBABBBABBbaBBBA" ++
    "BBBABBBABBBAABbbBBBABBBABBBABBBABBbaBBBABBBABBBABBBAABbbBBBABBBABBBABBBABBbaBBBABBBABBBABBB" ++
    "AABbbBBBABBBABBBABBBABBbaBBBABBBABBBABBBAABbbBBBABBBABBBABBBABBbaBBBABBBABBBABBBAABbbBBBABB" ++
    "BABBBABBBABBbaBBBABBBABBBABBBAABbbBBBABBBABBBABBBABBbaBBBABBBABBBABBBAABbbBBBABBBABBBABBBAB" ++
    "BbaBBBABBBABBBABBBAABbbBBBABBBABBBABBBABBbaBBBABBBABBBABBBAABbbBBBABBBABBBABBBABBbaBBBABBBA" ++
    "BBBABBBAABbbBBBABBBABBBABBBABBbaBBBABBBABBBABBBAabbbabbbabbbabbbBBBBbbABabbbabbbabbbabbbbaB" ++
    "BbbbbabbbabbbabbbabbbBBBBbbABabbbabbbabbbabbbbaBBbbbbabbbabbbabbbabbbBBBBbbABabbbabbbabbbab" ++
    "bbbaBBbbbbabbbabbbabbbabbbBBBBbbABabbbabbbabbbabbbbaBBbbbbabbbabbbabbbabbbBBBBbbABabbbabbba" ++
    "bbbabbbbaBBbbbbabbbabbbabbbabbbBBBBbbABabbbabbbabbbabbbbaBBbbbbabbbabbbabbbabbbBBBBbbABabbb" ++
    "abbbabbbabbbbaBBbbbbabbbabbbabbbabbbBBBBbbABabbbabbbabbbabbbbaBBbbbbabbbabbbabbbabbbBBBBbbA" ++
    "BabbbabbbabbbabbbbaBBbbbbBBBBbbABabbbabbbabbbabbbBBAabbbabbbabbbabbbabbabbbabbbabbbabbbBBAa" ++
    "bbbabbbabbbabbbabbabbbabbbabbbabbbBBBBbbABabbbabbbabbbabbbbaBBbbbbabbbabbbabbbabbbBBBBbbABa" ++
    "bbbabbbabbbabbbbaBBbbbbabbbabbbabbbabbbBBBBbbABabbbabbbabbbabbbbaBBbbbbabbbabbbabbbabbbBBBB" ++
    "bbABabbbabbbabbbabbbbaBBbbbbabbbabbbabbbabbbBBBBbbABabbbabbbabbbabbbbaBBbbbbabbbabbbabbbabb" ++
    "bBBBBbbABabbbabbbabbbabbbbaBBbbbbabbbabbbabbbabbbBBBBbbABabbbabbbabbbabbbbaBBbbbbabbbabbbab" ++
    "bbabbbBBBBbbABabbbabbbabbbabbbbaBBbbbbabbbabbbabbbabbbBBBBbbABabbbabbbabbbabbbbaBBbbbbBBBBb" ++
    "bABBbaBbBbABbBBBABBBABBBABBBABbaBbBBBABBBABBBABBBABbABbBBBABBBABBBABBBABbaBbBBBABBBABBBABBB" ++
    "AbaBBbbbbBBBBbbABBBBABBBABBBABBBAbaBBbbbbBBBABBBABBBABBBABBBBbbABBBBABBBABBBABBBAbaBBbbbbBB" ++
    "BABBBABBBABBBABBBBbbABBBBABBBABBBABBBAbaBBbbbbBBBABBBABBBABBBABBBBbbABBBBABBBABBBABBBAbaBBb" ++
    "bbbBBBABBBABBBABBBABBBBbbABBBBABBBABBBABBBAbaBBbbbbBBBABBBABBBABBBABBBBbbABBBBABBBABBBABBBA" ++
    "baBBbbbbBBBABBBABBBABBBABBBBbbABBBBABBBABBBABBBAbaBBbbbbBBBABBBABBBABBBABBBBbbABBBBABBBABBB" ++
    "ABBBAbaBBbbbbBBBABBBABBBABBBABBBBbbABBBBABBBABBBABBBAbaBBbbbbBBBABBBABBBABBBA"

@[expose] def hePiHeWord2 : String :=
  "abbbabbbabbbabbbBbaBbBbABbBBBABBBABBBABBBABbaBbBBBABBBABBBABBBABbABbBBBABBBABBBABBBABbaBbBBBA" ++
    "BBBABBBABBBAbaBBbbbbBBBBbbABBBBABBBABBBABBBAbaBBbbbbBBBABBBABBBABBBABBBBbbABBBBABBBABBBABBB" ++
    "AbaBBbbbbBBBABBBABBBABBBABBBBbbABBBBABBBABBBABBBAbaBBbbbbBBBABBBABBBABBBABBBBbbABBBBABBBABB" ++
    "BABBBAbaBBbbbbBBBABBBABBBABBBABBBBbbABBBBABBBABBBABBBAbaBBbbbbBBBABBBABBBABBBABBBBbbABBBBAB" ++
    "BBABBBABBBAbaBBbbbbBBBABBBABBBABBBABBBBbbABBBBABBBABBBABBBAbaBBbbbbBBBABBBABBBABBBABBBBbbAB" ++
    "BBBABBBABBBABBBAbaBBbbbbBBBABBBABBBABBBABBBBbbABBBBABBBABBBABBBAbaBBbbbbBBBABBBABBBABBBABBb" ++
    "aABbbBBBABBBABBBABBBABBbaBBBABBBABBBABBBAABbbBBBABBBABBBABBBABBbaBBBABBBABBBABBBAABbbBBBABB" ++
    "BABBBABBBABBbaBBBABBBABBBABBBAABbbBBBABBBABBBABBBABBbaBBBABBBABBBABBBAABbbBBBABBBABBBABBBAB" ++
    "BbaBBBABBBABBBABBBAABbbBBBABBBABBBABBBABBbaBBBABBBABBBABBBAABbbBBBABBBABBBABBBABBbaBBBABBBA" ++
    "BBBABBBAABbbBBBABBBABBBABBBABBbaBBBABBBABBBABBBAABbbBBBABBBABBBABBBABBbaBBBABBBABBBABBBAABb" ++
    "bBBBABBBABBBABBBABBbaBBBABBBABBBABBBAABbbBBBABBBABBBABBBABBbaBBBABBBABBBABBBAabbbabbbabbbab" ++
    "bbBBAabbbabbbabbbabbbabbabbbabbbabbbabbbBBAabbbabbbabbbabbbabbBBbaABbbBBBABBBABBBABBBABBbaB" ++
    "BBABBBABBBABBBAABbbBBBABBBABBBABBBABBbaBBBABBBABBBABBBAABbbBBBABBBABBBABBBABBbaBBBABBBABBBA" ++
    "BBBAABbbBBBABBBABBBABBBABBbaBBBABBBABBBABBBAABbbBBBABBBABBBABBBABBbaBBBABBBABBBABBBAABbbBBB" ++
    "ABBBABBBABBBABBbaBBBABBBABBBABBBAABbbBBBABBBABBBABBBABBbaBBBABBBABBBABBBAABbbBBBABBBABBBABB" ++
    "BABBbaBBBABBBABBBABBBAABbbBBBABBBABBBABBBABBbaBBBABBBABBBABBBAABbbBBBABBBABBBABBBABBbaBBBAB" ++
    "BBABBBABBBAABbbBBBABBBABBBABBBABBbaBBBABBBABBBABBBAbaBBbbbbBBBBbbABBBBABBBABBBABBBAbaBBbbbb" ++
    "BBBABBBABBBABBBABBBBbbABBBBABBBABBBABBBAbaBBbbbbBBBABBBABBBABBBABBBBbbABBBBABBBABBBABBBAbaB" ++
    "BbbbbBBBABBBABBBABBBABBBBbbABBBBABBBABBBABBBAbaBBbbbbBBBABBBABBBABBBABBBBbbABBBBABBBABBBABB" ++
    "BAbaBBbbbbBBBABBBABBBABBBABBBBbbABBBBABBBABBBABBBAbaBBbbbbBBBABBBABBBABBBABBBBbbABBBBABBBAB" ++
    "BBABBBAbaBBbbbbBBBABBBABBBABBBABBBBbbABBBBABBBABBBABBBAbaBBbbbbBBBABBBABBBABBBABBBBbbABBBBA" ++
    "BBBABBBABBBAbaBBbbbbBBBABBBABBBABBBA"

@[expose] def hePiHeWord3 : String :=
  "abbbabbbabbbabbbBBAabbbabbbabbbabbbabbabbbabbbabbbabbbBBAabbbabbbabbbabbbabbbaBBbbbbBBBBbbABB" ++
    "BBABBBABBBABBBAbaBBbbbbBBBABBBABBBABBBABBBBbbABBBBABBBABBBABBBAbaBBbbbbBBBABBBABBBABBBABBBB" ++
    "bbABBBBABBBABBBABBBAbaBBbbbbBBBABBBABBBABBBABBBBbbABBBBABBBABBBABBBAbaBBbbbbBBBABBBABBBABBB" ++
    "ABBBBbbABBBBABBBABBBABBBAbaBBbbbbBBBABBBABBBABBBABBBBbbABBBBABBBABBBABBBAbaBBbbbbBBBABBBABB" ++
    "BABBBABBBBbbABBBBABBBABBBABBBAbaBBbbbbBBBABBBABBBABBBABBBBbbABBBBABBBABBBABBBAbaBBbbbbBBBAB" ++
    "BBABBBABBBABBBBbbABBBBABBBABBBABBBAbaBBbbbbBBBABBBABBBABBBABbaBbBbABbBBBABBBABBBABBBABbaBbB" ++
    "BBABBBABBBABBBABbABbBBBABBBABBBABBBABbaBbBBBABBBABBBABBBAabbbabbbabbbabbbBBBBbbABabbbabbbab" ++
    "bbabbbbaBBbbbbabbbabbbabbbabbbBBBBbbABabbbabbbabbbabbbbaBBbbbbabbbabbbabbbabbbBBBBbbABabbba" ++
    "bbbabbbabbbbaBBbbbbabbbabbbabbbabbbBBBBbbABabbbabbbabbbabbbbaBBbbbbabbbabbbabbbabbbBBBBbbAB" ++
    "abbbabbbabbbabbbbaBBbbbbabbbabbbabbbabbbBBBBbbABabbbabbbabbbabbbbaBBbbbbabbbabbbabbbabbbBBB" ++
    "BbbABabbbabbbabbbabbbbaBBbbbbabbbabbbabbbabbbBBBBbbABabbbabbbabbbabbbbaBBbbbbabbbabbbabbbab" ++
    "bbBBBBbbABabbbabbbabbbabbbbaBBbbbbBBBBbbABBBbaABbbBBBABBBABBBABBBABBbaBBBABBBABBBABBBAABbbB" ++
    "BBABBBABBBABBBABBbaBBBABBBABBBABBBAABbbBBBABBBABBBABBBABBbaBBBABBBABBBABBBAABbbBBBABBBABBBA" ++
    "BBBABBbaBBBABBBABBBABBBAABbbBBBABBBABBBABBBABBbaBBBABBBABBBABBBAABbbBBBABBBABBBABBBABBbaBBB" ++
    "ABBBABBBABBBAABbbBBBABBBABBBABBBABBbaBBBABBBABBBABBBAABbbBBBABBBABBBABBBABBbaBBBABBBABBBABB" ++
    "BAABbbBBBABBBABBBABBBABBbaBBBABBBABBBABBBAABbbBBBABBBABBBABBBABBbaBBBABBBABBBABBBAABbbBBBAB" ++
    "BBABBBABBBABBbaBBBABBBABBBABBBAabbbabbbabbbabbbBBBBbbABabbbabbbabbbabbbbaBBbbbbabbbabbbabbb" ++
    "abbbBBBBbbABabbbabbbabbbabbbbaBBbbbbabbbabbbabbbabbbBBBBbbABabbbabbbabbbabbbbaBBbbbbabbbabb" ++
    "babbbabbbBBBBbbABabbbabbbabbbabbbbaBBbbbbabbbabbbabbbabbbBBBBbbABabbbabbbabbbabbbbaBBbbbbab" ++
    "bbabbbabbbabbbBBBBbbABabbbabbbabbbabbbbaBBbbbbabbbabbbabbbabbbBBBBbbABabbbabbbabbbabbbbaBBb" ++
    "bbbabbbabbbabbbabbbBBBBbbABabbbabbbabbbabbbbaBBbbbbabbbabbbabbbabbbBBBBbbABabbbabbbabbbabbb" ++
    "baBBbbbbBBBBbbABabbbabbbabbbabbbBBBBbbABabbbabbbabbbabbbbaBBbbbbabbbabbbabbbabbbBBBBbbABabb" ++
    "babbbabbbabbbbaBBbbbbabbbabbbabbbabbbBBBBbbABabbbabbbabbbabbbbaBBbbbbabbbabbbabbbabbbBBBBbb" ++
    "ABabbbabbbabbbabbbbaBBbbbbabbbabbbabbbabbbBBBBbbABabbbabbbabbbabbbbaBBbbbbabbbabbbabbbabbbB" ++
    "BBBbbABabbbabbbabbbabbbbaBBbbbbabbbabbbabbbabbbBBBBbbABabbbabbbabbbabbbbaBBbbbbabbbabbbabbb" ++
    "abbbBBBBbbABabbbabbbabbbabbbbaBBbbbbabbbabbbabbbabbbBBBBbbABabbbabbbabbbabbbbaBBbbbbBBBBbbA" ++
    "B"

@[expose] def hePiHeWord4 : String :=
  "BBbaABbbBBBABBBABBBABBBABBbaBBBABBBABBBABBBAABbbBBBABBBABBBABBBABBbaBBBABBBABBBABBBAABbbBBBAB" ++
    "BBABBBABBBABBbaBBBABBBABBBABBBAABbbBBBABBBABBBABBBABBbaBBBABBBABBBABBBAABbbBBBABBBABBBABBBA" ++
    "BBbaBBBABBBABBBABBBAABbbBBBABBBABBBABBBABBbaBBBABBBABBBABBBAABbbBBBABBBABBBABBBABBbaBBBABBB" ++
    "ABBBABBBAABbbBBBABBBABBBABBBABBbaBBBABBBABBBABBBAABbbBBBABBBABBBABBBABBbaBBBABBBABBBABBBAAB" ++
    "bbBBBABBBABBBABBBABBbaBBBABBBABBBABBBAABbbBBBABBBABBBABBBABBbaBBBABBBABBBABBBAabbbabbbabbba" ++
    "bbbBBBBbbABabbbabbbabbbabbbbaBBbbbbabbbabbbabbbabbbBBBBbbABabbbabbbabbbabbbbaBBbbbbabbbabbb" ++
    "abbbabbbBBBBbbABabbbabbbabbbabbbbaBBbbbbabbbabbbabbbabbbBBBBbbABabbbabbbabbbabbbbaBBbbbbabb" ++
    "babbbabbbabbbBBBBbbABabbbabbbabbbabbbbaBBbbbbabbbabbbabbbabbbBBBBbbABabbbabbbabbbabbbbaBBbb" ++
    "bbabbbabbbabbbabbbBBBBbbABabbbabbbabbbabbbbaBBbbbbabbbabbbabbbabbbBBBBbbABabbbabbbabbbabbbb" ++
    "aBBbbbbabbbabbbabbbabbbBBBBbbABabbbabbbabbbabbbbaBBbbbbBBBBbbABabbbabbbabbbabbbBBAabbbabbba" ++
    "bbbabbbabbabbbabbbabbbabbbBBAabbbabbbabbbabbbabbBBbaABbbBBBABBBABBBABBBABBbaBBBABBBABBBABBB" ++
    "AABbbBBBABBBABBBABBBABBbaBBBABBBABBBABBBAABbbBBBABBBABBBABBBABBbaBBBABBBABBBABBBAABbbBBBABB" ++
    "BABBBABBBABBbaBBBABBBABBBABBBAABbbBBBABBBABBBABBBABBbaBBBABBBABBBABBBAABbbBBBABBBABBBABBBAB" ++
    "BbaBBBABBBABBBABBBAABbbBBBABBBABBBABBBABBbaBBBABBBABBBABBBAABbbBBBABBBABBBABBBABBbaBBBABBBA" ++
    "BBBABBBAABbbBBBABBBABBBABBBABBbaBBBABBBABBBABBBAABbbBBBABBBABBBABBBABBbaBBBABBBABBBABBBAABb" ++
    "bBBBABBBABBBABBBABBbaBBBABBBABBBABBBAbaBBbbbbBBBBbbABBBBABBBABBBABBBAbaBBbbbbBBBABBBABBBABB" ++
    "BABBBBbbABBBBABBBABBBABBBAbaBBbbbbBBBABBBABBBABBBABBBBbbABBBBABBBABBBABBBAbaBBbbbbBBBABBBAB" ++
    "BBABBBABBBBbbABBBBABBBABBBABBBAbaBBbbbbBBBABBBABBBABBBABBBBbbABBBBABBBABBBABBBAbaBBbbbbBBBA" ++
    "BBBABBBABBBABBBBbbABBBBABBBABBBABBBAbaBBbbbbBBBABBBABBBABBBABBBBbbABBBBABBBABBBABBBAbaBBbbb" ++
    "bBBBABBBABBBABBBABBBBbbABBBBABBBABBBABBBAbaBBbbbbBBBABBBABBBABBBABBBBbbABBBBABBBABBBABBBAba" ++
    "BBbbbbBBBABBBABBBABBBABBbaABbbBBBABBBABBBABBBABBbaBBBABBBABBBABBBAABbbBBBABBBABBBABBBABBbaB" ++
    "BBABBBABBBABBBAABbbBBBABBBABBBABBBABBbaBBBABBBABBBABBBAABbbBBBABBBABBBABBBABBbaBBBABBBABBBA" ++
    "BBBAABbbBBBABBBABBBABBBABBbaBBBABBBABBBABBBAABbbBBBABBBABBBABBBABBbaBBBABBBABBBABBBAABbbBBB" ++
    "ABBBABBBABBBABBbaBBBABBBABBBABBBAABbbBBBABBBABBBABBBABBbaBBBABBBABBBABBBAABbbBBBABBBABBBABB" ++
    "BABBbaBBBABBBABBBABBBAABbbBBBABBBABBBABBBABBbaBBBABBBABBBABBBAABbbBBBABBBABBBABBBABBbaBBBAB" ++
    "BBABBBABBBAbaBBbbbbBBBBbbABBBBABBBABBBABBBAbaBBbbbbBBBABBBABBBABBBABBBBbbABBBBABBBABBBABBBA" ++
    "baBBbbbbBBBABBBABBBABBBABBBBbbABBBBABBBABBBABBBAbaBBbbbbBBBABBBABBBABBBABBBBbbABBBBABBBABBB" ++
    "ABBBAbaBBbbbbBBBABBBABBBABBBABBBBbbABBBBABBBABBBABBBAbaBBbbbbBBBABBBABBBABBBABBBBbbABBBBABB" ++
    "BABBBABBBAbaBBbbbbBBBABBBABBBABBBABBBBbbABBBBABBBABBBABBBAbaBBbbbbBBBABBBABBBABBBABBBBbbABB" ++
    "BBABBBABBBABBBAbaBBbbbbBBBABBBABBBABBBABBBBbbABBBBABBBABBBABBBAbaBBbbbbBBBABBBABBBABBBA"

@[expose] def hePiHeWord5 : String :=
  "abbbabbbabbbabbbBbaBbBbABbBBBABBBABBBABBBABbaBbBBBABBBABBBABBBABbABbBBBABBBABBBABBBABbaBbBBBA" ++
    "BBBABBBABBBAabbbabbbabbbabbbBBAabbbabbbabbbabbbabbabbbabbbabbbabbbBBAabbbabbbabbbabbbabbBba" ++
    "BbBbABbBBBABBBABBBABBBABbaBbBBBABBBABBBABBBABbABbBBBABBBABBBABBBABbaBbBBBABBBABBBABBBAabbba" ++
    "bbbabbbabbbBBBBbbABabbbabbbabbbabbbbaBBbbbbabbbabbbabbbabbbBBBBbbABabbbabbbabbbabbbbaBBbbbb" ++
    "abbbabbbabbbabbbBBBBbbABabbbabbbabbbabbbbaBBbbbbabbbabbbabbbabbbBBBBbbABabbbabbbabbbabbbbaB" ++
    "BbbbbabbbabbbabbbabbbBBBBbbABabbbabbbabbbabbbbaBBbbbbabbbabbbabbbabbbBBBBbbABabbbabbbabbbab" ++
    "bbbaBBbbbbabbbabbbabbbabbbBBBBbbABabbbabbbabbbabbbbaBBbbbbabbbabbbabbbabbbBBBBbbABabbbabbba" ++
    "bbbabbbbaBBbbbbabbbabbbabbbabbbBBBBbbABabbbabbbabbbabbbbaBBbbbbBBBBbbABBbaBbBbABbBBBABBBABB" ++
    "BABBBABbaBbBBBABBBABBBABBBABbABbBBBABBBABBBABBBABbaBbBBBABBBABBBABBBAbaBBbbbbBBBBbbABBBBABB" ++
    "BABBBABBBAbaBBbbbbBBBABBBABBBABBBABBBBbbABBBBABBBABBBABBBAbaBBbbbbBBBABBBABBBABBBABBBBbbABB" ++
    "BBABBBABBBABBBAbaBBbbbbBBBABBBABBBABBBABBBBbbABBBBABBBABBBABBBAbaBBbbbbBBBABBBABBBABBBABBBB" ++
    "bbABBBBABBBABBBABBBAbaBBbbbbBBBABBBABBBABBBABBBBbbABBBBABBBABBBABBBAbaBBbbbbBBBABBBABBBABBB" ++
    "ABBBBbbABBBBABBBABBBABBBAbaBBbbbbBBBABBBABBBABBBABBBBbbABBBBABBBABBBABBBAbaBBbbbbBBBABBBABB" ++
    "BABBBABBBBbbABBBBABBBABBBABBBAbaBBbbbbBBBABBBABBBABBBABBbaABbbBBBABBBABBBABBBABBbaBBBABBBAB" ++
    "BBABBBAABbbBBBABBBABBBABBBABBbaBBBABBBABBBABBBAABbbBBBABBBABBBABBBABBbaBBBABBBABBBABBBAABbb" ++
    "BBBABBBABBBABBBABBbaBBBABBBABBBABBBAABbbBBBABBBABBBABBBABBbaBBBABBBABBBABBBAABbbBBBABBBABBB" ++
    "ABBBABBbaBBBABBBABBBABBBAABbbBBBABBBABBBABBBABBbaBBBABBBABBBABBBAABbbBBBABBBABBBABBBABBbaBB" ++
    "BABBBABBBABBBAABbbBBBABBBABBBABBBABBbaBBBABBBABBBABBBAABbbBBBABBBABBBABBBABBbaBBBABBBABBBAB" ++
    "BBAABbbBBBABBBABBBABBBABBbaBBBABBBABBBABBBA"

@[expose] def hePiHeWord6 : String :=
  "BABABBABBABABBABAbbbbbbabababbabbbabbabaBBABBABBABBBABBABBBBABBAbbbbababbbbabbbababbbabaBABBA" ++
    "BBBBBBABBBBABABABBabbabbbabbbabbabbabbbabABABBABBBABBABABABBBBBBababbababbabbababABABBABBBA" ++
    "BBABABABBBBBBababbababbabbababBBBABBABBABABABBBBABababbbbabababbabbabbb"

@[expose] def hePiHeWord7 : String :=
  "BABABBABBABABBABAbbbbbbabababbabbbabbabaBABBBABBABBABBBABBBABBAbbabababbbbabbbbbbabbabBBABBAB" ++
    "BABBBABBABBBBABBAbbbbababbbbabbbababbbabaBBBABBABBABABABBBBABababbbbabababbabbabbbBABBBABBA" ++
    "BBABBBABBBABBAbbabababbbbabbbbbbabbab"

@[expose] def seedLetters (s : String) : List Int :=
  s.toList.map fun c => if c = 'a' then 1 else if c = 'A' then -1 else if c = 'b' then 2 else -2

@[expose] def hePiHeWords : List (List Int) :=
  List.map seedLetters [hePiHeWord0, hePiHeWord1, hePiHeWord2, hePiHeWord3,
    hePiHeWord4, hePiHeWord5, hePiHeWord6, hePiHeWord7]

@[expose] def hePiAWord : List (Fin 8 × Bool) :=
  ofCodes [11, 14, 11, 9, 11, 15, 10, 0, 0, 3, 6, 2]

@[expose] def hePiBWord : List (Fin 8 × Bool) :=
  ofCodes [12, 8, 14, 11, 8, 12, 8, 10, 0, 5, 5, 1]

@[expose] def hePiZWord : List (Fin 8 × Bool) :=
  ofCodes [2, 4, 2, 4]

end CFSG.ComponentClassification.AS81.HePres.Native
