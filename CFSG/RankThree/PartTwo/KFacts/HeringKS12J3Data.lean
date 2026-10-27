module

public import CFSG.RankThree.Asc83Table.MatCertDefs

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS12J3

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native

@[expose] def cert : MCert where
  nregs := 23
  prog := [
      .mul 1 0 2, .pow 2 1 3, .mul 2 3 4, .mul 3 0 5, .mul 5 3 6, .pow 6 6 7, .mul 7 3 8,
      .mul 8 0 8, .mul 2 1 9, .pow 9 9 10, .mul 8 10 8, .mul 8 0 8, .mul 8 1 8, .pow 2 2 11,
      .mul 8 11 8, .mul 8 3 8, .mul 8 0 8, .pow 2 8 8, .mul 4 8 4, .pow 7 6 12, .mul 4 12 4,
      .mul 0 3 13, .pow 8 13 14, .mul 0 1 15, .pow 2 15 16, .mul 16 1 17, .pow 2 17 17,
      .mul 14 17 18, .mul 18 0 18, .mul 18 7 18, .mul 18 3 18, .mul 18 0 18, .mul 18 1 18,
      .pow 2 18 18, .mul 4 18 4, .mul 4 14 4, .pow 8 2 2, .mul 2 3 18, .mul 18 14 18,
      .mul 18 17 18, .mul 18 0 18, .mul 18 12 18, .pow 6 13 19, .mul 18 19 18, .mul 18 0 18,
      .mul 18 1 18, .mul 18 0 18, .mul 18 3 18, .pow 2 5 20, .mul 18 20 18, .mul 18 1 18,
      .mul 18 0 18, .pow 8 6 21, .mul 18 21 18, .mul 18 3 18, .mul 18 0 18, .pow 7 9 22,
      .mul 18 22 18, .mul 18 0 18, .mul 18 3 18, .mul 18 20 18, .mul 18 1 18, .mul 18 0 18,
      .pow 9 6 6, .mul 18 6 18, .mul 18 19 18, .mul 18 0 18, .mul 18 1 18, .mul 18 0 18,
      .mul 18 3 18, .mul 18 20 18, .mul 18 1 18, .mul 18 0 18, .mul 18 21 18, .mul 18 3 18,
      .mul 18 0 18, .mul 18 10 18, .mul 18 0 18, .mul 18 1 18, .mul 18 11 18, .mul 18 3 18,
      .mul 18 0 18, .mul 18 7 18, .mul 18 3 18, .mul 18 0 18, .pow 8 9 9, .mul 18 9 9,
      .mul 9 1 9, .mul 3 20 18, .pow 2 18 18, .mul 18 1 18, .mul 18 0 18, .mul 18 21 21,
      .mul 21 3 21, .mul 21 0 21, .mul 21 22 21, .mul 21 0 21, .mul 21 3 21, .mul 21 20 21,
      .mul 21 1 21, .mul 21 0 21, .mul 21 6 21, .mul 21 19 21, .mul 21 0 21, .mul 21 1 21,
      .mul 15 0 15, .mul 15 3 15, .pow 2 15 6, .mul 21 6 6, .mul 6 0 6, .mul 17 0 21,
      .mul 21 7 21, .mul 21 3 21, .mul 21 0 21, .mul 21 10 21, .mul 21 0 21, .mul 21 1 21,
      .mul 21 11 21, .mul 21 3 21, .mul 21 0 21, .mul 21 7 7, .mul 7 3 7, .mul 7 0 7,
      .mul 7 22 7, .pow 3 15 15, .mul 7 15 7, .mul 7 8 7, .mul 7 1 7, .mul 7 0 7, .mul 7 3 7,
      .mul 2 10 2, .mul 2 0 2, .mul 2 1 2, .mul 2 11 11, .mul 11 3 11, .mul 11 0 11,
      .mul 11 12 11, .mul 11 19 19, .mul 19 0 19, .mul 19 1 19, .mul 19 15 15, .mul 12 14 12,
      .mul 12 17 12, .mul 12 0 12, .pow 3 12 12, .mul 15 12 15, .mul 15 1 15, .mul 15 0 15,
      .mul 15 3 15, .mul 13 0 12, .mul 12 1 12, .pow 2 13 13, .mul 12 13 13, .mul 13 16 13,
      .pow 2 13 13, .mul 13 0 13, .mul 13 3 13, .mul 13 16 13, .mul 12 0 12, .mul 12 3 12,
      .pow 2 12 12, .mul 13 12 13, .mul 13 3 13, .mul 13 0 13, .mul 13 3 13, .mul 13 0 13,
      .mul 13 3 13, .mul 13 0 13, .mul 13 3 13, .mul 13 0 13, .mul 13 1 13, .mul 13 12 13,
      .mul 13 0 13, .pow 3 5 5, .mul 13 5 5, .mul 5 3 3]
  facts := [
      MFact.ord 6 3,
      MFact.ord 7 3,
      MFact.ord 15 2,
      MFact.ord 3 8,
      MFact.ord 4 2,
      MFact.ord 9 2,
      MFact.eq [(6, 1), (7, 1)] [(7, 1), (6, 1)],
      MFact.ne [(6, 1)] [] 0,
      MFact.ne [(7, 1)] [] 0,
      MFact.ne [(7, 1)] [(6, 1)] 0,
      MFact.ne [(7, 1)] [(6, 2)] 0,
      MFact.ne [(4, 1)] [] 0,
      MFact.eq [(4, 1), (9, 1)] [(9, 1), (4, 1)],
      MFact.conj 15 [(6, 1)] [(6, 2), (7, 0)],
      MFact.conj 15 [(7, 1)] [(6, 0), (7, 1)],
      MFact.conj 3 [(7, 1)] [(6, 0), (7, 2)],
      MFact.conj 6 [(4, 1)] [(4, 0), (9, 1)],
      MFact.conj 6 [(9, 1)] [(4, 1), (9, 1)],
      MFact.conj 7 [(4, 1)] [(4, 0), (9, 1)],
      MFact.conj 7 [(9, 1)] [(4, 1), (9, 1)]]

end CFSG.RankThree.PartTwo.KFacts.KS12J3

