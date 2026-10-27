module

public import CFSG.RankThree.Asc83Table.MatCertDefs

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214.FourHe

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native

@[expose] def cert : MCert where
  nregs := 32
  prog := [
      .pow 2 1 2, .pow 3 1 3, .pow 4 1 4, .pow 5 1 5, .pow 6 1 6, .mul 0 1 7, .mul 0 2 8,
      .mul 0 3 9, .mul 0 4 10, .mul 0 5 11, .mul 0 6 12, .mul 2 7 13, .mul 13 7 13, .mul 13 8 13,
      .mul 13 8 13, .mul 13 8 13, .mul 13 7 13, .mul 13 12 13, .mul 13 7 13, .mul 13 7 13,
      .mul 13 11 13, .mul 13 7 13, .mul 13 8 13, .mul 13 7 13, .mul 13 9 13, .mul 13 7 13,
      .mul 13 12 13, .mul 13 10 13, .mul 13 12 13, .mul 13 11 13, .mul 13 7 13, .mul 13 11 13,
      .mul 13 8 13, .mul 13 11 13, .mul 13 8 13, .mul 13 0 13, .mul 7 9 14, .mul 14 9 14,
      .mul 14 7 14, .mul 14 7 14, .mul 14 10 14, .mul 14 10 14, .mul 14 11 14, .mul 14 7 14,
      .mul 14 7 14, .mul 14 8 14, .mul 14 8 14, .mul 14 7 14, .mul 14 12 14, .mul 14 11 14,
      .mul 14 11 14, .mul 14 7 14, .mul 14 12 14, .mul 14 7 14, .mul 14 7 14, .mul 14 7 14,
      .mul 14 10 14, .mul 14 7 14, .mul 14 11 14, .mul 14 8 14, .mul 14 11 14, .mul 14 8 14,
      .mul 14 0 14, .pow 2 13 15, .pow 2 14 16, .mul 13 14 17, .mul 17 15 17, .mul 17 16 17,
      .mul 13 14 18, .mul 13 16 19, .mul 12 12 20, .mul 20 7 20, .mul 20 9 20, .mul 20 10 20,
      .mul 20 12 20, .mul 20 7 20, .mul 20 12 20, .mul 20 7 20, .mul 20 9 20, .mul 20 11 20,
      .mul 20 12 20, .mul 20 12 20, .mul 20 8 20, .mul 20 12 20, .mul 20 9 20, .mul 20 7 20,
      .mul 20 7 20, .mul 20 12 20, .mul 20 10 20, .mul 20 12 20, .mul 20 12 20, .pow 2 13 21,
      .mul 21 20 22, .mul 22 13 22, .mul 11 8 23, .mul 23 11 23, .mul 23 8 23, .mul 23 11 23,
      .mul 23 7 23, .mul 23 7 23, .mul 23 8 23, .mul 23 7 23, .mul 23 12 23, .mul 23 12 23,
      .mul 23 10 23, .mul 23 12 23, .mul 23 8 23, .mul 23 12 23, .mul 23 10 23, .mul 23 12 23,
      .mul 23 8 23, .mul 23 12 23, .mul 23 12 23, .mul 23 9 23, .mul 23 10 23, .mul 23 10 23,
      .mul 23 10 23, .mul 23 7 23, .mul 23 12 23, .mul 23 8 23, .mul 23 7 23, .mul 23 7 23,
      .pow 2 14 24, .mul 24 23 25, .mul 25 14 25, .mul 5 8 26, .mul 26 11 26, .mul 26 8 26,
      .mul 26 11 26, .mul 26 9 26, .mul 26 12 26, .mul 26 11 26, .mul 26 8 26, .mul 26 7 26,
      .mul 26 7 26, .mul 26 9 26, .mul 26 12 26, .mul 26 7 26, .mul 26 9 26, .mul 26 7 26,
      .mul 26 7 26, .mul 26 7 26, .mul 26 12 26, .mul 26 8 26, .mul 26 11 26, .mul 26 7 26,
      .mul 26 11 26, .mul 26 10 26, .mul 26 9 26, .mul 26 11 26, .mul 26 11 26, .mul 26 12 26,
      .pow 2 18 27, .mul 18 26 28, .mul 28 27 28, .mul 1 7 29, .mul 29 9 29, .mul 29 8 29,
      .mul 29 12 29, .mul 29 9 29, .mul 29 8 29, .mul 29 12 29, .mul 29 7 29, .mul 29 10 29,
      .mul 29 9 29, .mul 29 7 29, .mul 29 7 29, .mul 29 12 29, .mul 29 12 29, .mul 29 8 29,
      .mul 29 11 29, .mul 29 8 29, .pow 2 19 30, .mul 19 29 31, .mul 31 30 31]
  facts := [
      MFact.ord 13 3,
      MFact.ord 14 3,
      MFact.eq [(13, 1), (14, 1), (13, 2), (14, 2), (13, 1)]
        [(13, 1), (13, 1), (14, 1), (13, 2), (14, 2)],
      MFact.eq [(13, 1), (14, 1), (13, 2), (14, 2), (14, 1)]
        [(14, 1), (13, 1), (14, 1), (13, 2), (14, 2)],
      MFact.ne [(13, 1), (14, 1), (13, 2), (14, 2)] [] 0,
      MFact.ord 17 3,
      MFact.eq [(17, 1)] [(13, 1), (14, 1), (13, 2), (14, 2)],
      MFact.ord 18 3,
      MFact.eq [(18, 1)] [(13, 1), (14, 1)],
      MFact.ord 19 3,
      MFact.eq [(19, 1)] [(13, 1), (14, 2)],
      MFact.ord 20 2,
      MFact.ord 22 2,
      MFact.eq [(20, 1), (22, 1)] [(22, 1), (20, 1)],
      MFact.ne [(20, 1)] [] 0,
      MFact.ne [(22, 1)] [] 0,
      MFact.ne [(20, 1)] [(22, 1)] 0,
      MFact.conj 17 [(20, 1)] [(20, 1), (22, 1)],
      MFact.conj 17 [(22, 1)] [(20, 1), (22, 0)],
      MFact.conj 13 [(20, 1)] [(20, 1), (22, 1)],
      MFact.conj 13 [(22, 1)] [(20, 1), (22, 0)],
      MFact.ne [(17, 1), (20, 1)] [(20, 1), (17, 1)] 0,
      MFact.ord 23 2,
      MFact.ord 25 2,
      MFact.eq [(23, 1), (25, 1)] [(25, 1), (23, 1)],
      MFact.ne [(23, 1)] [] 0,
      MFact.ne [(25, 1)] [] 0,
      MFact.ne [(23, 1)] [(25, 1)] 0,
      MFact.conj 17 [(23, 1)] [(23, 1), (25, 0)],
      MFact.conj 17 [(25, 1)] [(23, 0), (25, 1)],
      MFact.conj 14 [(23, 1)] [(23, 1), (25, 1)],
      MFact.conj 14 [(25, 1)] [(23, 1), (25, 0)],
      MFact.ne [(14, 1), (23, 1)] [(23, 1), (14, 1)] 0,
      MFact.ord 26 2,
      MFact.ord 28 2,
      MFact.eq [(26, 1), (28, 1)] [(28, 1), (26, 1)],
      MFact.ne [(26, 1)] [] 0,
      MFact.ne [(28, 1)] [] 0,
      MFact.ne [(26, 1)] [(28, 1)] 0,
      MFact.conj 17 [(26, 1)] [(26, 1), (28, 0)],
      MFact.conj 17 [(28, 1)] [(26, 0), (28, 1)],
      MFact.conj 18 [(26, 1)] [(26, 0), (28, 1)],
      MFact.conj 18 [(28, 1)] [(26, 1), (28, 1)],
      MFact.ne [(18, 1), (26, 1)] [(26, 1), (18, 1)] 0,
      MFact.ord 29 2,
      MFact.ord 31 2,
      MFact.eq [(29, 1), (31, 1)] [(31, 1), (29, 1)],
      MFact.ne [(29, 1)] [] 0,
      MFact.ne [(31, 1)] [] 0,
      MFact.ne [(29, 1)] [(31, 1)] 0,
      MFact.conj 17 [(29, 1)] [(29, 1), (31, 1)],
      MFact.conj 17 [(31, 1)] [(29, 1), (31, 0)],
      MFact.conj 19 [(29, 1)] [(29, 0), (31, 1)],
      MFact.conj 19 [(31, 1)] [(29, 1), (31, 1)],
      MFact.ne [(17, 1), (29, 1)] [(29, 1), (17, 1)] 0]

end CFSG.RankThree.PartTwo.Sec21.Hering214.FourHe
