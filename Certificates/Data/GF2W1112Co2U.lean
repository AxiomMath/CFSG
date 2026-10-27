module

public import Certificates.Data.GF2W1112Co2
public import Certificates.Data.CFSGNative.GF2W1112.Uniq

public section

namespace CFSG.GF2W1112

open CFSG.Sporadic.SmallF2.Native

@[expose] def w12UWords : Array String := #[
  "babbbabbababbabbbbababbbbabbbbabbbbabbababbbbabbbababababbbbabbbbabbbbabbababbbbabbb\
    abbabbababbbbabbbabbbbabbbbabbabbbabbabbababbabbababbbbabbbabbbabababbbabbabbbbabbba\
    bbabbbbabbabbababbbbabbbabbbabbabbababbbbabbbabbbbabbbabbabbbabababbbbabbbbaba",
  "babbabbababbbabbbababbbbabbbabbababbbbabababbbbabbbbabbbabbbabbbbabbbbabbbbabbabbbab\
    babbbabababbbbabbbabbababbbabbabbababbbbabbbabbabbabbbbabbabbababbbbabbbabbbababbbba\
    bbbbabbabbbbabbbbaba",
  "bbbbabbabbbabababbbbabbbbabbbabbababbbbabbbabbbabababbababbbbabbbabbbabbbbabbbbbbbab\
    abbbabbabbabbababbababbbbabbbabbbabbbababbbbabbabbababbbbabbbababbabbbabbbbabababbb",
  "abbbbabbabbbabbabbbbababbbbabbabbababbbbabbbabbbabbbbabbabbbabbbabbbabbabbbbabbbbabb\
    bbabbbabbbabbabbbabbbbbbabbbbababababbbbabbbbabbbbababbbbabbbbababbababbbbabbbbabbbb\
    abbababbbbabbbbabbbbabbbabbbbabbbbabbbabababbbbabb",
  "bbabbabababbbbabbbbababababbbbabbbbabbbbabbabbbabbabbbabbbbabbabbbababababbbbabbbabb\
    ababbbabbabbababbbbabbbabbbbabbbbabbbbabbabbbabbbabbababbbbabbbabbbababbbbababbbabba\
    bbbbabbbbab",
  "bbbbabababbbabbabbbababababbababbbbabbbabbabbabbbbabbbbabbbabbbabbabbabbababbababbbb\
    abbbabbbabbababbbbabbbbabbbbababbbbabbbbababbababbbbabbbbabbbbababababbbbababbbbabbb\
    babbbbabbbbabbbbabba",
  "",
  "bbbbabababbbabbabbbababababbababbbbabbbabbabbabbbbabbbbabbbabbbabbabbabbababbababbbb\
    abbbabbbabbababbbbabbbbabbbbababbbbabbbbababbababbbbabbbbabbbbababababbbbababbbbabbb\
    babbbbabbbbabbbbabba",
  "bbbababbbbabbbbabbababbabbbabababababbbbabbbababababbbbabbbababababbbbabbbabbabbabab\
    bbbabbbabbbabababbbabbabbbbabbbabbabbbababbabbababbbbabbbabbbabbbbabababbbaba",
  "babbbbabbbbababbabbababbbbabbbabbbabbabbababbbbabbbabbbababbbabbbbbbabbabbbabbabbbba\
    bbbbabbbbabbabbbbababababbbbabbbbabbbbababbbbabbbbababbababbbbabbbbabbbbabbababbbbab\
    abbbbabbbbabbbabbbabbbbabbabbbbabbbabba",
  "babbbbababbbabbabbbababababbababbbbabbbabbbabbbbabbabbbabbbabbababbbbabbbabbbababbbb\
    abbabbbabbabbbbabbbbabbbbabbabbbabbabbbbabbbbabbbbbbbbababbbababbbbabbbbababbbababbb\
    bbbabbbbabbbabbbabbabbbbabbbba",
  "bbbababbbababbabbbbababbbababbbbabbbbabbbabbbabbbbabbbbabbbbabbabbbabbabbbbabbbbabba\
    bbbabbabbbbabbbbabbabbbabbabbabbababbbabbabbabbabbbbabbabbababbbbabbbabbbabbabbababb\
    bbabbbabbbababbbbabbbbabbabbbba",
  "babbbbabbbbababbabbababbbbabbbabbbabbbbabbabbbabbababbbbabbbabbababbababababbababbbb\
    abbbabbbababbabbabbbbababababbbbabbbbababbbbbbbbabbbbabbbbababa",
  "babbbabbbabbbabbbabbbbabbabababbbbabbbababababbbbabbbababababbbbabbbbabbbbabbabbbabb\
    abbbbabbbbabbabbbabbabbbabbbbababbbbabbababbbabbabbabbabbbabbbabbababbbbabbbabbababa\
    bbbba",
  "babbbbabbbbabbabbbabbabbbbabbabbababbbbabbbabbabbabbbbabbbbababbabbbabbabbbbabbbbabb\
    bbabbababbbabbabbbabbbbbbabbbabbbbbbbbabbbabbabbbabbbbbbbababbabbabababbbbabbbbababb\
    bbabbbababbbbabbababbbbabbbbabbbabbbbbbabbbabbbbabbbabbbbabbabbbbabbbabbbb",
  "bbbbababbbbabbabbbbabbabbababbbbabbbabbbabbbbabbabbbabbbabbababbbbabbbabbbabbabbbabb\
    abbbbabbbabababbbababbababbbbabbbbabbbbababbbbabbababbbbabbbabbababbbbabbbbabbabbbab\
    bbbabbbabbbbabbbabbb",
  "babbbabbbabbababbbbabbbabbabbabbbababbbbababbabbbabbabbbbabbbbabbbbababbabbababbbbab\
    bbabbbabababbbbababbbabbbabbbbabbbbababbbabbbabbbabbabbbb",
  "bbbbabbabbbbababbbababbbbababbabbababbbbabbbabbbababbbabbbabbababbbbabbbabbbabababba\
    babbbbabbbabbbabbabbbabbabbabbabbbababbbabbabbbbabbbbabbbabbbbabbabababbbabbbbabbbba\
    bbbbabbbabbbbabbbabbbbabbba",
  "babababbabbbbabbbbabbabababbbbababbbbabbbababbbababbbababbbbabbbbababbbbabbbbabbbaba\
    babbbbabbabbbabbabbbabbbbabbabbbbabababbbabbabbababbabbababbbbabbbabbbbabbbbababbbab\
    abbabbababbbbabbbabbabababbbbabbbbabbabbbabbabbbba",
  "abbbbababbbbabbabbbbababbbababbabbababbbbabbbabbbababbbbabbbbababbabbababbbbabbbabbb\
    abababbbabbabbbbabbbababababbababbbbabbbabbbabbbbabbbbbbabbababbabbabababbbbabbbbaba\
    bbbbabbbabbababbbbabbabbbbbbbabbabbbbabbabbbabbbbabbbba",
  "bbbbabbabbbbababbbbabbbbababbabbababbbbabbbabbabbabbbababababbbbabbbabbababbbabbbbab\
    ababbbbabbababbabbabababbbbabbbbababbbbababbbabbbabbbbabbbbabbbbabbbbabbbbabbb",
  "abbabbabbbababbbbababbbbabbabbabbbbabababbabbbbabbbbabababbbabbbababbbabbabbbabababa\
    bbbabbabbbbabbbababbabbababbbbabbbabbbbabbbbabbabbababbbbabbbabbbbabbbbabbbbabbabbba\
    bbabbbbabbbbab",
  "abbbbabbabbbbababbbbabbbbabbababbababbbbabbbabbbabbbbabbabbbbabababbababbbbabbbabbba\
    bbabbababbbbabbbabbbabbabbbabbabbbbabbbbababbbabbababbbabbabbbabbbbbbabababbbbabbbba\
    bbbbababbbbabbbbababbababbbbabbbbabbbbabbababbbbabbbbabbbbabbbbabbbbbbbababbabbabbab\
    bbbabbba",
  "bbababbabababababababbabbababbbbabababbbbabbbbabbbabbbabbbbabbababababbbabbabbbabbab\
    bababbbbabbbabbbababbbabababbbabbbabbababbbbabbbabbababbbbabbabbbbabbbbab",
  "abbbbabababbbabbabbbababbbbabbbabbababbbbabbbabbbabbbbabbabbbbabababbababbbbabbbabbb\
    abbbbabbbbbbbbabbbabbabbbbabbbbabbbbabbbabbbabbabbbabbbbbbabbbabbbbbbbababbababbbbab\
    bbabbbabbabbbabbabbbabbbbbbabababbabbabababbbbababababbabbbbabbbabbbba",
  "ababbbbabbbbabbabbbbabababbababbbbabbbabbbabababbbabbabbbbabbbbabababbbabbabbbabbbbb\
    babbbabbbbbbbbabbbabbabbbabbbbbbabbabababbbbabbabbbbabbabbbbabbbabbbbabbabb",
  "bbbbabbbbababbbababbbbabbbabababababbbbabbbabbbbabababbbbababababbbbabbababbbbababab\
    bbbabbabbbabbabbabbababbbabbabbbabbabbababbbbabbbabbbbabbbbababbbababbabbababbbbabbb\
    abbabbabbbbababbbab",
  "abbbbabbabbbbababbbababbbbabbbabbababbbbabbbabbbabbbbabbabbbabbababbababbbbabbbabbba\
    bbabbbabbabbbbabbbbabbbbabbabbbabbababbababbbbabbbabbbabbababbbbabbbbabbbbababababbb\
    babbbababbbabbbbbbbabababbbbababbbababbbbabababbbabbbb",
  "ababbbbabbbbabbabbbababbabbababbbbabbbabbabbabbbabababbbbabbabbbabbabbbbabbbbabababb\
    ababbbbabbbabbbabbbbabbbbbbbbabbbabbabbbabbbbbbababbababbbbabbbabbbabbabbabbbbabbbba\
    bababbbabbbbabbbbabbababbbbabbbbababbbbabbbbabbbbabbbbabbabbbb",
  "bbababbbabbabbabababbabbabababbbbabbbbabbbabbabababbbbabbbababbbbabbbababbbbabbbbaba\
    bbbbabbbbbabbababbbbabbbabbbabababbbabbabbbabbabbababbbbabbbabbbbabbbabbabbbb",
  "bababbabbababbabababbabbbbabbabbbbabbababbbbabbbababbbbababababbbbabbbabbabbababbbba\
    bbbabbbabbbbababababbbabbabbbabbabbababbbbabbbabbbbabbbbabbbbabbabbbbabbabbababbbbab\
    bbabbbabbabbababbbbabbbabbbababbbbababbbabbabbbbabbbbaba",
  "a",
  "b"]

@[expose] def w12UOrds : Array Nat := #[
  3, 3, 3, 3, 6, 4, 1, 4, 8, 20, 6, 4, 6, 4, 20, 6, 2, 4, 4, 2, 4, 4, 4, 4, 2, 4, 4, 2, 3, 5,
  5, 2, 5]

@[expose] def w12UConj : Array (Array Nat) := #[
  #[],
  #[],
  #[],
  #[],
  #[1, 2, 2, 0, 0, 2, 0, 0, 2, 1, 1, 1, 1, 2, 1, 0],
  #[2, 2, 1, 1, 0, 1, 1, 2, 2, 2, 2, 2, 2, 1, 0, 1],
  #[1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1],
  #[2, 2, 1, 1, 0, 1, 1, 2, 2, 2, 2, 2, 2, 1, 0, 1],
  #[0, 2, 1, 0, 0, 2, 2, 1, 2, 2, 2, 1, 1, 0, 2, 1],
  #[1, 1, 0, 1, 0, 1, 1, 2, 0, 2, 2, 0, 2, 2, 1, 0],
  #[0, 1, 1, 1, 1, 1, 2, 1, 0, 0, 2, 0, 1, 0, 0, 2],
  #[1, 1, 0, 2, 0, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2],
  #[1, 2, 2, 0, 1, 1, 2, 2, 0, 0, 2, 0, 1, 2, 2, 1],
  #[2, 0, 0, 0, 2, 2, 1, 2, 2, 0, 0, 2, 2, 0, 1, 0],
  #[0, 1, 0, 0, 0, 1, 1, 2, 1, 1, 1, 2, 2, 0, 2, 2],
  #[1, 0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 0, 0, 0, 1],
  #[0, 1, 1, 1, 0, 2, 0, 0, 0, 0, 2, 0, 1, 1, 1, 0],
  #[0, 2, 2, 1, 0, 1, 0, 0, 0, 0, 1, 0, 2, 2, 2, 0],
  #[2, 2, 0, 2, 0, 1, 0, 0, 0, 2, 2, 0, 2, 2, 2, 1],
  #[1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2],
  #[0, 2, 2, 1, 0, 1, 0, 0, 0, 0, 1, 0, 2, 2, 2, 0],
  #[0, 1, 2, 0, 0, 1, 0, 0, 0, 2, 1, 2, 1, 1, 1, 0],
  #[0, 2, 2, 1, 0, 2, 2, 2, 1, 2, 2, 2, 0, 0, 1, 0],
  #[1, 1, 0, 1, 1, 2, 2, 0, 1, 0, 1, 0, 2, 1, 0, 0],
  #[1, 1, 2, 1, 2, 2, 0, 1, 2, 1, 1, 1, 0, 1, 2, 2],
  #[0, 1, 1, 1, 1, 1, 2, 1, 0, 0, 2, 0, 2, 0, 0, 1],
  #[2, 2, 0, 1, 0, 1, 2, 0, 0, 2, 0, 2, 0, 2, 1, 1],
  #[0, 2, 0, 0, 2, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0],
  #[],
  #[0, 1, 0, 0, 0, 2, 2, 1, 1, 0, 1, 0, 0, 1, 0, 2],
  #[0, 1, 2, 0, 2, 2, 0, 2, 2, 0, 1, 0, 0, 2, 1, 2],
  #[],
  #[]]

@[expose] def w12UConjInv : Array (Array Nat) := #[
  #[],
  #[],
  #[],
  #[],
  #[2, 2, 0, 2, 0, 2, 0, 0, 1, 0, 0, 2, 1, 0, 1, 0],
  #[1, 1, 2, 2, 0, 2, 2, 1, 1, 1, 1, 1, 1, 2, 0, 2],
  #[1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1],
  #[1, 1, 2, 2, 0, 2, 2, 1, 1, 1, 1, 1, 1, 2, 0, 2],
  #[0, 1, 2, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 2, 2],
  #[2, 2, 0, 1, 2, 2, 1, 2, 1, 1, 1, 1, 0, 2, 2, 0],
  #[2, 1, 1, 0, 2, 2, 0, 1, 0, 0, 2, 0, 2, 1, 1, 2],
  #[2, 2, 1, 1, 1, 2, 2, 0, 1, 1, 1, 1, 2, 1, 0, 1],
  #[0, 2, 2, 2, 2, 2, 0, 2, 0, 0, 2, 0, 2, 0, 0, 1],
  #[2, 0, 0, 0, 2, 2, 1, 1, 2, 0, 0, 1, 1, 0, 2, 0],
  #[0, 2, 1, 0, 1, 0, 0, 0, 1, 1, 1, 1, 2, 0, 1, 1],
  #[1, 0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 0, 0, 0, 1],
  #[0, 1, 1, 1, 0, 2, 0, 0, 0, 0, 2, 0, 1, 1, 1, 0],
  #[0, 2, 2, 2, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0],
  #[1, 1, 2, 1, 0, 1, 0, 0, 0, 2, 2, 0, 1, 1, 1, 2],
  #[1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2],
  #[0, 2, 2, 2, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0],
  #[1, 1, 0, 1, 0, 1, 0, 0, 2, 1, 0, 0, 2, 0, 2, 0],
  #[0, 2, 1, 0, 1, 1, 0, 2, 0, 0, 0, 1, 2, 1, 0, 0],
  #[0, 1, 1, 1, 0, 1, 1, 2, 0, 2, 0, 2, 1, 1, 1, 0],
  #[1, 1, 2, 1, 2, 2, 0, 1, 2, 1, 1, 1, 0, 1, 2, 2],
  #[2, 1, 1, 0, 2, 2, 0, 2, 0, 0, 2, 0, 2, 1, 1, 1],
  #[2, 2, 1, 2, 0, 2, 2, 2, 0, 1, 2, 2, 0, 1, 0, 1],
  #[0, 2, 0, 0, 2, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0],
  #[],
  #[0, 1, 1, 1, 1, 0, 0, 0, 0, 2, 0, 2, 1, 0, 0, 2],
  #[0, 1, 1, 2, 1, 1, 2, 2, 0, 1, 2, 2, 2, 0, 0, 2],
  #[],
  #[]]

@[expose] def w12UClsTab : Array Nat := #[
  0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0,
  1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
  1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0]

@[expose] def w12UParTab : Array Nat := #[
  0, 25, 0, 3, 10, 0, 0, 34, 0, 79, 27, 0, 73, 57, 0, 0, 30, 0, 0, 52, 0, 25, 30, 0, 0, 49, 0,
  27, 7, 0, 13, 49, 0, 0, 4, 0, 63, 57, 0, 66, 9, 0, 0, 37, 0, 0, 16, 0, 63, 39, 0, 0, 73, 0,
  0, 12, 0, 10, 39, 0, 0, 27, 0, 34, 70, 0, 3, 64, 0, 0, 13, 0, 0, 61, 0, 43, 58, 0, 0, 55, 0]

@[expose] def w12UGenTab : Array Nat := #[
  0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0,
  1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1,
  0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]

@[expose] def w12UCTab : Array Nat := #[
  0, 1, 0, 1, 2, 0, 0, 2, 0, 2, 1, 0, 2, 2, 0, 0, 1, 0, 0, 2, 0, 1, 1, 0, 0, 2, 0, 1, 2, 0, 1,
  1, 0, 0, 2, 0, 2, 2, 0, 2, 1, 0, 0, 1, 0, 0, 2, 0, 2, 2, 0, 0, 2, 0, 0, 1, 0, 2, 2, 0, 0, 1,
  0, 1, 2, 0, 2, 2, 0, 0, 2, 0, 0, 1, 0, 2, 1, 0, 0, 1, 0]

@[expose] def w12UDepthTab : Array Nat := #[
  0, 5, 0, 0, 2, 0, 0, 4, 0, 6, 1, 0, 3, 3, 0, 0, 5, 0, 0, 4, 0, 5, 5, 0, 0, 4, 0, 0, 5, 0, 4,
  4, 0, 0, 3, 0, 5, 3, 0, 2, 7, 0, 0, 4, 0, 0, 6, 0, 5, 3, 0, 0, 3, 0, 0, 4, 0, 2, 3, 0, 0, 1,
  0, 4, 5, 0, 1, 6, 0, 0, 4, 0, 0, 2, 0, 5, 4, 0, 0, 5, 0]

@[expose] def w12URootCodes : Array Nat := #[27, 3]

@[expose] def w12UOrbCodes : Array Nat := #[3, 66, 39, 49, 58, 25, 31, 76, 1, 21]

@[expose] def w12UCrTab : Array Nat := #[1, 2, 1, 2, 2, 1, 2, 2, 1, 1]

@[expose] def w12UCtVal : Nat := 2

@[expose] def w12UW1Code : Nat := 3

@[expose] def w12UV0Code : Nat := 3

@[expose] def w12UDecSigma : Array Nat := #[
  0, 2, 3, 5, 7, 8, 1, 9, 6, 4, 1, 0, 4, 6, 2, 9, 3, 8, 7, 5, 4, 8, 0, 2, 3, 5, 1, 7, 9, 6, 1,
  4, 3, 6, 5, 0, 8, 7, 2, 9, 4, 5, 6, 8, 0, 1, 2, 7, 3, 9, 6, 2, 8, 0, 4, 1, 9, 7, 5, 3, 2, 9,
  1, 5, 8, 4, 6, 7, 3, 0, 8, 3, 2, 1, 5, 4, 9, 7, 0, 6]

@[expose] def w12UDecU : Array Nat := #[
  0, 6, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 6, 0, 3, 3, 6, 0, 3, 0, 6, 0, 3, 0, 3, 6, 3, 0,
  3, 6, 3, 3, 6, 0, 6, 6, 3, 0, 6, 3, 6, 6, 3, 6, 3, 0, 6, 0, 6, 0, 3, 3, 0, 3, 0, 0, 6, 6, 3,
  3, 0, 3, 0, 0, 3, 0, 3, 3, 6, 3, 0, 3, 0, 0, 3, 6, 3, 6, 0, 6, 3, 6, 3, 6, 3, 3, 6, 6, 3, 6,
  3, 0, 3, 6, 3, 0, 3, 0, 3, 6, 3, 6, 0, 0, 6, 0, 6, 0, 3, 0, 6, 3, 0, 3, 0, 0, 3, 3, 0, 6, 0,
  3, 0, 0, 3, 3, 6, 3, 6, 0, 6, 3, 0, 3, 6, 3, 6, 6, 3, 3, 6, 0, 3, 6, 0, 6, 3, 6, 3, 0, 3, 0,
  3, 6, 3, 0, 3]

@[expose] def w12UDecEps : Array Nat := #[
  1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0,
  0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1,
  1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1,
  1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0,
  1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0,
  0, 1, 1, 0, 0]

@[expose] def w12UDecP : Array (List (Nat × Nat)) := #[
  [(0, 1), (4, 2), (0, 1)], [(3, 3), (1, 1), (4, 1), (1, 1), (0, 2)], [], [], [], [], [], [],
  [], [], [], [], [(1, 3), (3, 3), (0, 1)], [(0, 1), (4, 3), (3, 1), (4, 3), (1, 1), (0, 2)],
  [(2, 1), (0, 2), (1, 3), (4, 3), (1, 3), (4, 1)], [(4, 2), (2, 1), (0, 3), (4, 3)],
  [(0, 3), (3, 1), (1, 1)], [(0, 2), (1, 3), (4, 1), (3, 3), (4, 1), (0, 3)],
  [(2, 1), (0, 2), (1, 3), (4, 3), (1, 3), (3, 3)],
  [(0, 2), (1, 3), (4, 1), (1, 3), (3, 1), (2, 1)], [], [],
  [(2, 1), (4, 1), (3, 3), (4, 1), (0, 3), (3, 3)],
  [(2, 1), (4, 1), (3, 3), (4, 1), (0, 3), (3, 3)], [], [], [], [],
  [(2, 1), (1, 3), (3, 1), (1, 1)], [(2, 1), (1, 3), (3, 1), (1, 1)], [], [],
  [(4, 1), (0, 3), (4, 1), (2, 1)], [(4, 1), (0, 3), (4, 1), (2, 1)],
  [(3, 3), (1, 1), (4, 3), (1, 1)], [(3, 1), (1, 3), (4, 3), (1, 1)],
  [(2, 1), (0, 3), (1, 3), (3, 1), (4, 3), (1, 3)], [(0, 2), (4, 2), (2, 1), (0, 3)],
  [(0, 1), (3, 1), (4, 3), (0, 3), (2, 1), (4, 3)],
  [(0, 1), (3, 1), (4, 3), (0, 3), (2, 1), (4, 3)],
  [(1, 1), (0, 1), (4, 1), (1, 1), (3, 1), (0, 1)], [(0, 1), (1, 3), (4, 1), (1, 3)],
  [(3, 1), (0, 1), (1, 3), (4, 1), (1, 1), (0, 1)], [(1, 1), (2, 1), (4, 1), (1, 1), (2, 1)],
  [(1, 1), (4, 3), (3, 1), (4, 3), (0, 1), (2, 1)], [(2, 1), (0, 3), (1, 3), (3, 1), (0, 3)],
  [(1, 3), (4, 1), (1, 3), (3, 1), (0, 3)], [(4, 2), (1, 3), (3, 3), (1, 1)],
  [(3, 3), (0, 1), (4, 3), (1, 1), (0, 3), (2, 1)], [(3, 3), (2, 1), (4, 1), (1, 1), (0, 1)],
  [(2, 1), (1, 3), (4, 1), (1, 3), (0, 3)], [(2, 1), (1, 3), (4, 1), (1, 3), (0, 3)],
  [(2, 1), (4, 2), (1, 3), (0, 3)], [(2, 1), (1, 3), (4, 1), (3, 2)],
  [(2, 1), (0, 3), (3, 1), (4, 1), (0, 3)], [(0, 1), (3, 1), (0, 3), (4, 3), (2, 1)],
  [(2, 1), (1, 3), (4, 3), (0, 1), (4, 3)],
  [(1, 1), (4, 1), (2, 1), (3, 1), (2, 1), (4, 1), (0, 1), (2, 1)],
  [(0, 3), (1, 3), (3, 3), (4, 1), (1, 3)], [(0, 3), (1, 3), (4, 3), (3, 3), (1, 1)],
  [(2, 1), (0, 2), (4, 3), (2, 1), (3, 3), (1, 3)], [(0, 3), (4, 1), (1, 1)],
  [(0, 3), (1, 3), (4, 3), (2, 1), (3, 1), (0, 3)], [(2, 1), (1, 3), (3, 1), (0, 3), (4, 3)],
  [(0, 3), (1, 3), (4, 3), (3, 1), (1, 1)], [(1, 3), (4, 1), (3, 3), (1, 1), (0, 3)],
  [(0, 3), (4, 3), (2, 1), (3, 3), (1, 3), (3, 3)], [(2, 1), (0, 2), (4, 1), (3, 1), (1, 1)],
  [(2, 1), (3, 1), (4, 3), (1, 3)], [(2, 1), (4, 1), (1, 3), (3, 1)],
  [(1, 1), (3, 1), (1, 1), (4, 2), (1, 1)], [(0, 1), (1, 3), (4, 1), (0, 1)],
  [(2, 1), (4, 2), (1, 1), (2, 1)], [(0, 2), (1, 3), (3, 1), (4, 1), (3, 1)],
  [(2, 1), (0, 1), (1, 3), (3, 1), (1, 3)], [(2, 1), (0, 2), (3, 1), (0, 3)],
  [(2, 1), (0, 1), (4, 3), (3, 1), (4, 1), (0, 3)],
  [(2, 1), (0, 1), (4, 3), (3, 1), (4, 1), (0, 3)], [(2, 1), (0, 3), (4, 3), (3, 2)],
  [(1, 3), (4, 2), (1, 1), (2, 1)], [(2, 1), (1, 3), (4, 3), (2, 1), (3, 3), (2, 1), (1, 3)],
  [(2, 1), (3, 1), (4, 2), (0, 1)], [(0, 2), (4, 3), (3, 1), (0, 1), (3, 3), (4, 3)],
  [(0, 2), (4, 3), (3, 1), (0, 1), (3, 3), (4, 3)],
  [(2, 1), (0, 3), (1, 3), (4, 3), (2, 1), (3, 3), (2, 1), (4, 3)],
  [(1, 1), (4, 3), (3, 1), (4, 3), (0, 2), (2, 1)], [(4, 1), (0, 3), (4, 1), (0, 1), (2, 1)],
  [(2, 1), (0, 3), (4, 3), (3, 1), (0, 1), (3, 3), (4, 3)], [(0, 3), (4, 2), (3, 3), (2, 1)],
  [(2, 1), (0, 3), (4, 3), (3, 1), (4, 1)], [(0, 2), (4, 3), (3, 1), (0, 1), (3, 3), (4, 3)],
  [(0, 2), (4, 3), (3, 1), (0, 1), (3, 3), (4, 3)],
  [(3, 1), (0, 1), (4, 3), (3, 1), (4, 3), (1, 1), (2, 1)],
  [(0, 1), (1, 1), (4, 3), (3, 1), (4, 3), (0, 1), (2, 1)], [(0, 3), (1, 3), (3, 3), (1, 3)],
  [(0, 1), (1, 3), (3, 1), (1, 3)], [(2, 1), (0, 1), (4, 3), (3, 1), (0, 1), (3, 3), (4, 3)],
  [(3, 1), (4, 1), (0, 3), (4, 1), (0, 2), (2, 1)],
  [(0, 3), (1, 3), (4, 3), (3, 1), (0, 1), (1, 3), (3, 3), (4, 3)],
  [(2, 1), (0, 1), (1, 3), (4, 3), (2, 1), (1, 3), (3, 3)], [(1, 1), (3, 1), (1, 1)], [(0, 1)],
  [(1, 3), (4, 1), (1, 1), (3, 1), (0, 3)], [(4, 2), (1, 3), (3, 3), (1, 3)],
  [(2, 1), (0, 3), (1, 3), (4, 1), (3, 1), (1, 1)],
  [(2, 1), (0, 3), (1, 3), (4, 3), (1, 3), (4, 1)], [(4, 2), (1, 3), (4, 1), (0, 2)],
  [(1, 3), (4, 3), (3, 1), (0, 1), (3, 3), (4, 3)],
  [(2, 1), (0, 3), (4, 3), (2, 1), (3, 3), (2, 1), (4, 3)],
  [(4, 1), (3, 1), (0, 3), (3, 3), (4, 1), (0, 1), (2, 1)],
  [(1, 3), (3, 3), (4, 1), (1, 1), (0, 1), (2, 1)],
  [(1, 3), (3, 3), (4, 1), (1, 1), (0, 1), (2, 1)],
  [(0, 2), (4, 1), (3, 3), (4, 1), (0, 3), (3, 3)],
  [(0, 2), (4, 1), (3, 3), (4, 1), (0, 3), (3, 3)],
  [(2, 1), (0, 3), (1, 3), (3, 1), (1, 1), (4, 3), (0, 3)], [(0, 3), (2, 1), (4, 1), (0, 2)],
  [(0, 1), (1, 3), (4, 1), (3, 3), (1, 3)], [(0, 1), (1, 3), (4, 1), (1, 1), (0, 3)],
  [(0, 2), (4, 3), (2, 1), (3, 3), (2, 1), (4, 3), (1, 3)], [(1, 3), (3, 3)],
  [(3, 1), (0, 1), (4, 1), (1, 3), (3, 3), (2, 1)], [(2, 1), (1, 3), (4, 2), (3, 3)],
  [(0, 3), (1, 3), (3, 1), (4, 3), (3, 3), (0, 3)],
  [(0, 3), (1, 3), (3, 1), (4, 3), (0, 3), (3, 3)], [(0, 1), (1, 3), (4, 3), (1, 3), (3, 1)],
  [(3, 1), (4, 1), (3, 3), (4, 3), (3, 3)], [(2, 1), (1, 3), (4, 3), (1, 1), (0, 3), (3, 3)],
  [(2, 1), (1, 3), (4, 3), (1, 3)], [(0, 1), (4, 1), (1, 3), (3, 1)],
  [(2, 1), (0, 1), (3, 1), (2, 1), (4, 3), (1, 3)], [(2, 1), (1, 3), (4, 3)],
  [(1, 3), (3, 1), (4, 3), (0, 3), (2, 1), (3, 3)], [(0, 1), (4, 3), (2, 1), (3, 3), (0, 3)],
  [(2, 1), (3, 1), (4, 3), (0, 2)], [(2, 1), (1, 3), (4, 1), (1, 3), (4, 1)],
  [(2, 1), (3, 1), (4, 1), (3, 1), (4, 3)], [(0, 3), (4, 2), (3, 3)],
  [(4, 3), (3, 1), (4, 1), (0, 3)], [(2, 1), (0, 3), (4, 1), (3, 3), (0, 1)],
  [(0, 2), (4, 3), (2, 1), (0, 1)], [(0, 1), (1, 3), (4, 1), (3, 2)],
  [(2, 1), (0, 3), (1, 3), (4, 3), (3, 1), (2, 1)], [(4, 1), (0, 2), (3, 3)],
  [(3, 1), (4, 3), (0, 2)], [(0, 3), (3, 1), (0, 3), (4, 1)],
  [(0, 1), (1, 3), (4, 2), (0, 3), (1, 3)], [(0, 2), (4, 1), (0, 3)],
  [(2, 1), (3, 1), (2, 1), (4, 3)], [(0, 1), (4, 1), (1, 1), (3, 1), (0, 1)],
  [(2, 1), (4, 3), (1, 3), (3, 3), (2, 1), (3, 3)],
  [(2, 1), (0, 2), (1, 3), (3, 1), (4, 3), (0, 3), (2, 1), (3, 3)],
  [(0, 2), (3, 3), (1, 1), (4, 1), (3, 3)], [(3, 3), (4, 1), (0, 1), (2, 1)],
  [(2, 1), (3, 1), (4, 1), (3, 1)], [(0, 3), (1, 3), (4, 2), (1, 3), (3, 3)],
  [(2, 1), (0, 1), (3, 1), (2, 1), (4, 3), (3, 3)],
  [(2, 1), (0, 1), (4, 3), (2, 1), (3, 3), (1, 3)],
  [(3, 1), (2, 1), (3, 1), (2, 1), (4, 1), (1, 1)], [(2, 1), (0, 3), (4, 3), (3, 1)],
  [(3, 3), (4, 3), (3, 3), (2, 1)]]

@[expose] def w12UYWords : Array (List (Nat × Nat)) := #[
  [(0, 4), (1, 4), (0, 3), (1, 1), (0, 1), (1, 4), (0, 4), (1, 2), (0, 4), (1, 1), (0, 4),
     (1, 3), (0, 1)],
  [(0, 4), (1, 1), (0, 4), (1, 4), (0, 1), (1, 1), (0, 4), (1, 3), (0, 4), (1, 1), (0, 1)],
  [(0, 4), (1, 4), (0, 3), (1, 1), (0, 2), (1, 1), (0, 4), (1, 2)]]

@[expose] def w12UZWords : Array (List (Nat × Nat)) := #[
  [(0, 4), (1, 4), (0, 3), (1, 2), (0, 3), (1, 1), (0, 4), (1, 3), (0, 1), (1, 3), (0, 4)],
  [(0, 4), (1, 4), (0, 3), (1, 2), (0, 4), (1, 2), (0, 4)],
  [(1, 1), (0, 4), (1, 3), (0, 4), (1, 1), (0, 2), (1, 4), (0, 2), (1, 4), (0, 3)]]

@[expose] def w12UPairs : Array (List (Nat × Nat) × List (Nat × Nat)) := #[
  ([(0, 1), (1, 2)],
   [(0, 1), (1, 2), (1, 1)]),
  ([(1, 1), (1, 2)],
   [(1, 1), (1, 2), (1, 1)]),
  ([(0, 2), (0, 1), (0, 1)],
   [(0, 2), (0, 2), (1, 2)]),
  ([(1, 2), (1, 1)],
   [(1, 2), (1, 1), (1, 1)]),
  ([(1, 1), (0, 1), (0, 1)],
   [(0, 1), (1, 1), (0, 2)]),
  ([(1, 2), (0, 2)],
   [(0, 1), (0, 1)]),
  ([(1, 1), (0, 1), (1, 2)],
   [(0, 1), (0, 1)]),
  ([(1, 2), (1, 1), (0, 1)],
   [(0, 1), (1, 1)]),
  ([(1, 2), (1, 1)],
   [(1, 2), (1, 1)]),
  ([(0, 1), (0, 1)],
   [(1, 2), (0, 2), (1, 2)]),
  ([(0, 2), (0, 2), (1, 1)],
   [(0, 2), (0, 1)]),
  ([(1, 1), (1, 2)],
   [(0, 1), (1, 1)]),
  ([(1, 2), (0, 1), (1, 2)],
   [(0, 1), (1, 1)]),
  ([(1, 1), (1, 2), (1, 2)],
   [(0, 2), (1, 1), (0, 2)]),
  ([(0, 1), (0, 2)],
   [(1, 2), (1, 1), (1, 1)]),
  ([(1, 1), (0, 1), (1, 2)],
   [(1, 2), (1, 2)]),
  ([(1, 2), (0, 2)],
   [(0, 2), (0, 2)]),
  ([(1, 1), (0, 1)],
   [(1, 1), (0, 1), (0, 1)]),
  ([(1, 2), (0, 2), (1, 2)],
   [(1, 1), (1, 2), (1, 2)]),
  ([(1, 2), (0, 2), (0, 1)],
   [(1, 2), (0, 1), (1, 1)]),
  ([(1, 1), (1, 1), (0, 1)],
   [(1, 1), (1, 2), (1, 2)]),
  ([(0, 2), (1, 1), (0, 2)],
   [(0, 2), (1, 2)]),
  ([(0, 1), (0, 1)],
   [(0, 1), (0, 2), (0, 2)]),
  ([(0, 1), (1, 2), (1, 1)],
   [(1, 1), (0, 1)])]

@[expose] def w12UPerf : Array (List (Nat × Nat)) := #[
  [(9, 0), (2, 0), (10, 1), (0, 0), (0, 0)],
  [(10, 1), (10, 1), (23, 1), (10, 0), (0, 1)]]

@[expose] def w12UTauWords : Array (List (Nat × Nat)) := #[
  [(0, 1)],
  [(1, 1)],
  [(0, 1), (1, 1)],
  [(0, 2), (1, 1)],
  [(0, 1), (1, 2)],
  [(0, 1), (1, 1), (0, 1), (1, 3)],
  [(1, 1), (0, 2), (1, 2)],
  [(0, 1), (1, 1), (0, 1), (1, 2)]]

@[expose] def w12UTauOrd : Array Nat := #[12, 12, 12, 30, 30, 12, 6, 18]

@[expose] def w12USeedA : List (Nat × Nat) :=
  [(1, 2), (0, 2), (1, 2), (2, 1), (1, 2), (0, 5), (1, 1), (0, 5), (1, 1), (2, 2), (1, 3),
   (0, 5), (1, 3), (2, 1), (0, 3), (2, 2), (1, 2), (2, 1), (1, 3), (2, 1), (1, 3), (2, 1),
   (1, 2), (0, 2), (2, 2), (1, 3), (0, 5), (1, 1), (0, 5), (1, 3), (0, 4), (1, 1), (0, 4),
   (2, 1), (0, 5), (1, 1), (0, 5), (1, 3), (2, 2), (0, 1), (1, 1), (2, 2), (0, 1), (1, 1),
   (0, 1), (2, 2)]

@[expose] def w12USeedB : List (Nat × Nat) :=
  [(0, 5), (1, 1), (0, 5), (1, 1), (0, 3), (1, 3), (0, 1), (1, 1), (0, 4), (1, 2), (0, 1),
   (1, 2), (0, 5), (1, 3), (0, 1), (1, 1), (0, 5), (2, 1), (0, 3), (2, 2), (1, 3), (0, 5),
   (1, 2), (0, 5), (1, 3), (2, 1), (1, 3), (0, 1), (2, 1), (0, 5), (2, 2), (1, 3), (2, 2),
   (1, 2), (2, 2), (0, 1), (2, 1), (0, 5), (2, 2), (0, 5), (2, 2), (1, 3)]

@[expose] def w12UBRows : Array (Array Nat) := #[
  #[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[196608, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 196608, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0],
  #[
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 131072, 65536, 0, 0, 0, 0],
  #[
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 65536, 131072, 0, 0, 0, 0],
  #[
  0, 0, 1890920, 3719100, 1351652, 3962232, 2424232, 1877756, 3436140, 2938804, 2915308,
  1633652, 2668132, 3988956, 3472116, 1594796, 0, 0, 1867412, 2398588, 3975588, 1374044]]

@[expose] def w12UFree : List Nat := [0, 1, 17, 22, 23, 39, 374, 375, 390, 391, 482]

@[expose] def w12UThetaCodes : Array Nat := #[9, 11]

@[expose] def w12UM0Rows : Array Nat :=
  #[
  196610, 196611, 1890920, 3719100, 1351652, 3962232, 2424232, 1877756, 3436140, 2938804,
  2915308, 1633652, 2668132, 3988956, 3472116, 1594796, 131073, 65537, 1867412, 2398588,
  3975588, 1374044]

@[expose] def w12USCodes : List Nat := [13, 14, 9, 11, 6, 7]

@[expose] def w12UParse (s : String) : List Bool := s.toList.map (· == 'a')

@[expose] def w12URows (_ : Unit := ()) : Array (Array Nat) :=
  w12UWords.map fun s => w12WordRows (w12Co2RowsA ()) (w12Co2RowsB ()) (w12UParse s)

@[expose] def w12UEvalE (G : Array (Array Nat)) (L : List (Nat × Nat)) : Array Nat :=
  L.foldl (fun acc q => mulRows 22 acc (powRows 22 G[q.1]! q.2)) (idRows 22)

@[expose] def w12UIdxOk (L : List (Nat × Nat)) : Bool := L.all fun q => decide (q.1 < 33)

@[expose] def w12UEqCheck (G : Array (Array Nat))
    (eqs : List (List (Nat × Nat) × List (Nat × Nat))) : Bool :=
  eqs.all fun q => w12UIdxOk q.1 && w12UIdxOk q.2 && w12UEqR (w12UEvalE G q.1) (w12UEvalE G q.2)

@[expose] def w12UPowCheck (G : Array (Array Nat)) (ps : List (List (Nat × Nat) × Nat)) : Bool :=
  ps.all fun q => w12UIdxOk q.1 && w12UEqR (powRows 22 (w12UEvalE G q.1) q.2) (idRows 22)

@[expose] def w12UIota (c : Nat) : List (Nat × Nat) :=
  [(0, c % 3), (1, c / 3 % 3), (2, c / 9 % 3), (3, c / 27 % 3)]

@[expose] def w12UNormIdx : List Nat :=
  [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 29, 30]

@[expose] def w12UConjCode (k i : Nat) : Nat :=
  let A := w12UConj[k]!
  A[i]! + 3 * A[4 + i]! + 9 * A[8 + i]! + 27 * A[12 + i]!

@[expose] def w12UConjEq (k i : Nat) : List (Nat × Nat) × List (Nat × Nat) :=
  ([(k, 1), (i, 1)], w12UIota (w12UConjCode k i) ++ [(k, 1)])

@[expose] def w12UConjEqs (_ : Unit := ()) : List (List (Nat × Nat) × List (Nat × Nat)) :=
  w12UNormIdx.flatMap fun k => (List.range 4).map fun i => w12UConjEq k i

@[expose] def w12UOrd (i : Nat) : Nat := w12UOrds.getD i 1

@[expose] def w12UOrdEqs (_ : Unit := ()) : List (List (Nat × Nat) × List (Nat × Nat)) :=
  (List.range 33).map fun i => ([(i, w12UOrd i)], [])

@[expose] def w12UCommEqs (_ : Unit := ()) : List (List (Nat × Nat) × List (Nat × Nat)) :=
  (List.range 4).flatMap fun i => (List.range 4).map fun j => ([(i, 1), (j, 1)], [(j, 1), (i, 1)])

@[expose] def w12UCheck1 (_ : Unit := ()) : Bool :=
  let G := w12URows ()
  w12UEqCheck G (w12UOrdEqs () ++ w12UCommEqs () ++ w12UConjEqs ()) &&
    !(w12UEqR (G[0]!) (idRows 22))

@[expose] def w12UIdxM (m : Nat) : Nat := if m < 2 then 4 + m else 20 + m

@[expose] def w12UDecEq (m i j : Nat) : List (Nat × Nat) × List (Nat × Nat) :=
  let k := m * 20 + i * 2 + j
  ([(w12UIdxM m, 1), (6 + i, 1), (1, j)],
    [(6 + w12UDecSigma[m * 10 + i]! % 10, 1)] ++ w12UIota w12UDecU[k]! ++ [(16, w12UDecEps[k]!)] ++
      (w12UDecP[k]!).map fun q => (17 + q.1 % 5, q.2))

@[expose] def w12UDecEqs (_ : Unit := ()) : List (List (Nat × Nat) × List (Nat × Nat)) :=
  (List.range 8).flatMap fun m => (List.range 10).flatMap fun i =>
    (List.range 2).map fun j => w12UDecEq m i j

@[expose] def w12UCheck2 (_ : Unit := ()) : Bool := w12UEqCheck (w12URows ()) (w12UDecEqs ())

@[expose] def w12UMapS (L : List (Nat × Nat)) : List (Nat × Nat) := L.map fun q => (29 + q.1, q.2)

@[expose] def w12UInv (L : List (Nat × Nat)) : List (Nat × Nat) :=
  L.reverse.map fun q => (q.1, w12UOrd q.1 - q.2 % w12UOrd q.1)

@[expose] def w12UComm (u v : List (Nat × Nat)) : List (Nat × Nat) :=
  u ++ v ++ w12UInv u ++ w12UInv v

@[expose] def w12UPairEx (pk d : Nat) : List (Nat × Nat) :=
  let p := w12UPairs[pk]!
  if d == 0 then w12UComm (w12UMapS p.1) (w12UMapS p.2) else w12UComm (w12UMapS p.2) (w12UMapS p.1)

@[expose] def w12UPerfEq (si : Nat) : List (Nat × Nat) × List (Nat × Nat) :=
  ([(29 + si, 1)], (w12UPerf[si]!).flatMap fun q => w12UPairEx q.1 q.2)

@[expose] def w12UMapN (L : List (Nat × Nat)) : List (Nat × Nat) :=
  L.map fun q => (4 + q.1 % 2, q.2)

@[expose] def w12UMapNG (L : List (Nat × Nat)) : List (Nat × Nat) :=
  L.map fun q => (if q.1 == 2 then 28 else 4 + q.1 % 2, q.2)

@[expose] def w12UGlueEqs (_ : Unit := ()) : List (List (Nat × Nat) × List (Nat × Nat)) :=
  (List.range 3).map (fun k => ([(22 + k, 1)], w12UMapS (w12UYWords[k]!))) ++
  (List.range 3).map (fun k => ([(25 + k, 1)], w12UMapS (w12UZWords[k]!))) ++
  (List.range 2).map w12UPerfEq ++
  (List.range 3).map (fun k => ([(28, 1), (22 + k, 1)], [(25 + k, 1), (28, 1)])) ++
  [([(31, 1)], w12UMapNG w12USeedA), ([(32, 1)], w12UMapNG w12USeedB)]

@[expose] def w12UTauPows (_ : Unit := ()) : List (List (Nat × Nat) × Nat) :=
  (List.range 8).map fun j => (w12UMapN (w12UTauWords[j]!) ++ [(28, 1)], w12UTauOrd[j]!)

@[expose] def w12UCheck3 (_ : Unit := ()) : Bool :=
  let G := w12URows ()
  w12UEqCheck G (w12UGlueEqs ()) && w12UPowCheck G (w12UTauPows ())

end CFSG.GF2W1112

