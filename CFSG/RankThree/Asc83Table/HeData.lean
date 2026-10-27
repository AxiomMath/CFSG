module

public import CFSG.RankThree.Asc83Table.MatCertDefs

public section

namespace CFSG.RankThree.Asc83Table.He

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native

@[expose] def heCert : MCert where
  nregs := 17
  prog := [
      .pow 2 1 2, .pow 3 1 3, .pow 4 1 4, .pow 5 1 5, .pow 6 1 6, .pow 1 1 7, .mul 7 0 7,
      .mul 7 1 7, .mul 7 0 7, .mul 7 2 7, .mul 7 0 7, .mul 7 1 7, .mul 7 0 7, .mul 7 5 7,
      .mul 7 0 7, .mul 7 2 7, .mul 7 0 7, .mul 7 1 7, .mul 7 0 7, .mul 7 3 7, .mul 7 0 7,
      .mul 7 1 7, .mul 7 0 7, .mul 7 3 7, .mul 7 0 7, .mul 7 3 7, .mul 7 0 7, .mul 7 2 7,
      .mul 7 0 7, .mul 7 3 7, .mul 7 0 7, .mul 7 1 7, .mul 7 0 7, .mul 7 3 7, .mul 7 0 7,
      .mul 7 3 7, .mul 7 0 7, .mul 7 5 7, .mul 7 0 7, .mul 7 4 7, .mul 7 0 7, .mul 7 1 7,
      .mul 7 0 7, .mul 7 6 7, .mul 7 0 7, .mul 7 5 7, .mul 7 0 7, .mul 7 6 7, .mul 7 0 7,
      .mul 7 6 7, .mul 7 0 7, .mul 7 6 7, .mul 7 0 7, .mul 7 6 7, .mul 7 0 7, .pow 1 0 8,
      .mul 8 2 8, .mul 8 0 8, .mul 8 2 8, .mul 8 0 8, .mul 8 2 8, .mul 8 0 8, .mul 8 2 8,
      .mul 8 0 8, .mul 8 1 8, .mul 8 0 8, .mul 8 1 8, .mul 8 0 8, .mul 8 1 8, .mul 8 0 8,
      .mul 8 1 8, .mul 8 0 8, .mul 8 4 8, .mul 8 0 8, .mul 8 3 8, .mul 8 0 8, .mul 8 3 8,
      .mul 8 0 8, .mul 8 1 8, .mul 8 0 8, .mul 8 3 8, .mul 8 0 8, .mul 8 3 8, .mul 8 0 8,
      .mul 8 6 8, .mul 8 0 8, .mul 8 2 8, .mul 8 0 8, .mul 8 1 8, .mul 8 0 8, .mul 8 3 8,
      .mul 8 0 8, .mul 8 1 8, .mul 8 0 8, .mul 8 3 8, .mul 8 0 8, .mul 8 3 8, .mul 8 0 8,
      .mul 8 2 8, .mul 8 0 8, .mul 8 3 8, .mul 8 0 8, .mul 8 1 8, .mul 8 0 8, .mul 8 3 8,
      .mul 8 0 8, .mul 8 3 8, .mul 8 0 8, .mul 8 2 8, .mul 8 0 8, .mul 8 3 8, .mul 8 0 8,
      .mul 8 1 8, .mul 8 0 8, .mul 8 3 8, .mul 8 0 8, .mul 8 3 8, .mul 8 0 8, .mul 8 1 8,
      .mul 8 0 8, .mul 8 5 8, .mul 8 0 8, .mul 8 2 8, .mul 8 0 8, .mul 8 6 8, .mul 8 0 8,
      .mul 8 1 8, .mul 8 0 8, .mul 8 1 8, .mul 8 0 8, .mul 8 1 8, .mul 8 0 8, .mul 8 2 8,
      .mul 8 0 8, .mul 8 1 8, .mul 8 0 8, .mul 8 6 8, .mul 8 0 8, .mul 8 3 8, .mul 8 0 8,
      .mul 8 1 8, .mul 8 0 8, .pow 1 0 9, .mul 9 2 9, .mul 9 0 9, .mul 9 1 9, .mul 9 0 9,
      .mul 9 3 9, .mul 9 0 9, .mul 9 3 9, .mul 9 0 9, .mul 9 2 9, .mul 9 0 9, .mul 9 2 9,
      .mul 9 0 9, .mul 9 2 9, .mul 9 0 9, .mul 9 1 9, .mul 9 0 9, .mul 9 3 9, .mul 9 0 9,
      .mul 9 1 9, .mul 9 0 9, .mul 9 3 9, .mul 9 0 9, .mul 9 3 9, .mul 9 0 9, .mul 9 2 9,
      .mul 9 0 9, .mul 9 3 9, .mul 9 0 9, .mul 9 1 9, .mul 9 0 9, .mul 9 3 9, .mul 9 0 9,
      .mul 9 3 9, .mul 9 0 9, .mul 9 1 9, .mul 9 0 9, .mul 9 1 9, .mul 9 0 9, .mul 9 3 9,
      .mul 9 0 9, .mul 9 1 9, .mul 9 0 9, .mul 9 3 9, .mul 9 0 9, .mul 9 3 9, .mul 9 0 9,
      .mul 9 1 9, .mul 9 0 9, .mul 9 1 9, .mul 9 0 9, .mul 9 3 9, .mul 9 0 9, .mul 9 1 9,
      .mul 9 0 9, .mul 9 3 9, .mul 9 0 9, .mul 9 3 9, .mul 9 0 9, .mul 9 2 9, .mul 9 0 9,
      .mul 9 3 9, .mul 9 0 9, .mul 9 1 9, .mul 9 0 9, .mul 9 3 9, .mul 9 0 9, .mul 9 3 9,
      .mul 9 0 9, .mul 9 6 9, .mul 9 0 9, .mul 9 3 9, .mul 9 0 9, .mul 9 3 9, .mul 9 0 9,
      .mul 9 1 9, .mul 9 0 9, .mul 9 3 9, .mul 9 0 9, .mul 9 3 9, .mul 9 0 9, .mul 9 6 9,
      .pow 1 6 10, .mul 10 0 10, .mul 10 3 10, .mul 10 0 10, .mul 10 6 10, .mul 10 0 10,
      .mul 10 4 10, .mul 10 0 10, .mul 10 4 10, .mul 10 0 10, .mul 10 6 10, .mul 10 0 10,
      .mul 10 4 10, .mul 10 0 10, .mul 10 5 10, .mul 10 0 10, .mul 10 4 10, .mul 10 0 10,
      .mul 10 4 10, .mul 10 0 10, .mul 10 6 10, .mul 10 0 10, .mul 10 4 10, .mul 10 0 10,
      .mul 10 6 10, .mul 10 0 10, .mul 10 5 10, .mul 10 0 10, .mul 10 1 10, .mul 10 0 10,
      .mul 10 4 10, .mul 10 0 10, .mul 10 4 10, .mul 10 0 10, .mul 10 6 10, .mul 10 0 10,
      .mul 10 4 10, .mul 10 0 10, .mul 10 5 10, .mul 10 0 10, .mul 10 4 10, .mul 10 0 10,
      .mul 10 4 10, .mul 10 0 10, .mul 10 6 10, .mul 10 0 10, .mul 10 4 10, .mul 10 0 10,
      .mul 10 4 10, .mul 10 0 10, .mul 10 2 10, .mul 10 0 10, .mul 10 3 10, .mul 10 0 10,
      .mul 10 5 10, .mul 10 0 10, .mul 10 3 10, .mul 10 0 10, .mul 10 6 10, .mul 10 0 10,
      .mul 10 6 10, .mul 10 0 10, .mul 10 4 10, .mul 10 0 10, .pow 1 1 11, .mul 11 0 11,
      .mul 11 5 11, .mul 11 0 11, .mul 11 6 11, .mul 11 0 11, .mul 11 1 11, .mul 11 0 11,
      .mul 11 4 11, .mul 11 0 11, .mul 11 4 11, .mul 11 0 11, .mul 11 2 11, .mul 11 0 11,
      .mul 11 4 11, .mul 11 0 11, .mul 11 1 11, .mul 11 0 11, .mul 11 2 11, .mul 11 0 11,
      .mul 11 5 11, .mul 11 0 11, .mul 11 1 11, .mul 11 0 11, .mul 11 6 11, .mul 11 0 11,
      .mul 11 1 11, .mul 11 0 11, .mul 11 4 11, .mul 11 0 11, .mul 11 1 11, .mul 11 0 11,
      .mul 11 6 11, .mul 11 0 11, .mul 11 6 11, .mul 11 0 11, .mul 11 2 11, .mul 11 0 11,
      .mul 11 6 11, .mul 11 0 11, .mul 11 1 11, .mul 11 0 11, .mul 11 1 11, .mul 11 0 11,
      .pow 1 3 12, .mul 12 0 12, .mul 12 6 12, .mul 12 0 12, .mul 12 4 12, .mul 12 0 12,
      .mul 12 1 12, .mul 12 0 12, .mul 12 5 12, .mul 12 0 12, .mul 12 3 12, .mul 12 0 12,
      .mul 12 1 12, .mul 12 0 12, .mul 12 3 12, .mul 12 0 12, .mul 12 3 12, .mul 12 0 12,
      .mul 12 2 12, .mul 12 0 12, .mul 12 3 12, .mul 12 0 12, .mul 12 1 12, .mul 12 0 12,
      .mul 12 3 12, .mul 12 0 12, .mul 12 3 12, .mul 12 0 12, .mul 12 6 12, .mul 12 0 12,
      .mul 12 3 12, .mul 12 0 12, .mul 12 3 12, .mul 12 0 12, .mul 12 1 12, .mul 12 0 12,
      .mul 12 3 12, .mul 12 0 12, .mul 12 3 12, .mul 12 0 12, .mul 12 6 12, .mul 12 0 12,
      .mul 12 1 12, .mul 12 0 12, .mul 12 6 12, .mul 12 0 12, .mul 12 1 12, .mul 12 0 12,
      .mul 12 5 12, .mul 12 0 12, .mul 12 1 12, .mul 12 0 12, .mul 12 2 12, .mul 12 0 12,
      .mul 12 5 12, .mul 12 0 12, .mul 12 5 12, .mul 12 0 12, .mul 12 6 12, .mul 12 0 12,
      .mul 12 6 12, .mul 12 0 12, .mul 12 6 12, .mul 12 0 12, .mul 12 6 12, .mul 12 0 12,
      .mul 12 6 12, .mul 12 0 12, .mul 12 5 12, .mul 12 0 12, .mul 12 2 12, .pow 1 3 13,
      .mul 13 0 13, .mul 13 6 13, .mul 13 0 13, .mul 13 4 13, .mul 13 0 13, .mul 13 1 13,
      .mul 13 0 13, .mul 13 5 13, .mul 13 0 13, .mul 13 3 13, .mul 13 0 13, .mul 13 1 13,
      .mul 13 0 13, .mul 13 3 13, .mul 13 0 13, .mul 13 3 13, .mul 13 0 13, .mul 13 2 13,
      .mul 13 0 13, .mul 13 3 13, .mul 13 0 13, .mul 13 1 13, .mul 13 0 13, .mul 13 3 13,
      .mul 13 0 13, .mul 13 3 13, .mul 13 0 13, .mul 13 6 13, .mul 13 0 13, .mul 13 3 13,
      .mul 13 0 13, .mul 13 3 13, .mul 13 0 13, .mul 13 1 13, .mul 13 0 13, .mul 13 3 13,
      .mul 13 0 13, .mul 13 3 13, .mul 13 0 13, .mul 13 6 13, .mul 13 0 13, .mul 13 1 13,
      .mul 13 0 13, .mul 13 6 13, .mul 13 0 13, .mul 13 1 13, .mul 13 0 13, .mul 13 5 13,
      .mul 13 0 13, .mul 13 1 13, .mul 13 0 13, .mul 13 2 13, .mul 13 0 13, .mul 13 5 13,
      .mul 13 0 13, .mul 13 5 13, .mul 13 0 13, .mul 13 6 13, .mul 13 0 13, .mul 13 6 13,
      .mul 13 0 13, .mul 13 6 13, .mul 13 0 13, .mul 13 6 13, .mul 13 0 13, .mul 13 6 13,
      .mul 13 0 13, .mul 13 5 13, .mul 13 0 13, .mul 13 2 13, .pow 1 4 14, .mul 14 0 14,
      .mul 14 6 14, .mul 14 0 14, .mul 14 1 14, .mul 14 0 14, .mul 14 6 14, .mul 14 0 14,
      .mul 14 1 14, .mul 14 0 14, .mul 14 6 14, .mul 14 0 14, .mul 14 1 14, .mul 14 0 14,
      .mul 14 3 14, .mul 14 0 14, .mul 14 1 14, .mul 14 0 14, .mul 14 3 14, .mul 14 0 14,
      .mul 14 3 14, .mul 14 0 14, .mul 14 6 14, .mul 14 0 14, .mul 14 3 14, .mul 14 0 14,
      .mul 14 3 14, .mul 14 0 14, .mul 14 1 14, .mul 14 0 14, .mul 14 3 14, .mul 14 0 14,
      .mul 14 3 14, .mul 14 0 14, .mul 14 1 14, .mul 14 0 14, .mul 14 4 14, .mul 14 0 14,
      .mul 14 4 14, .mul 14 0 14, .mul 14 1 14, .mul 14 0 14, .mul 14 6 14, .mul 14 0 14,
      .mul 14 5 14, .mul 14 0 14, .mul 14 6 14, .mul 14 0 14, .mul 14 6 14, .mul 14 0 14,
      .mul 14 6 14, .mul 14 0 14, .mul 14 6 14, .mul 14 0 14, .pow 1 3 15, .mul 15 0 15,
      .mul 15 1 15, .mul 15 0 15, .mul 15 5 15, .mul 15 0 15, .mul 15 5 15, .mul 15 0 15,
      .mul 15 5 15, .mul 15 0 15, .mul 15 3 15, .mul 15 0 15, .mul 15 3 15, .mul 15 0 15,
      .mul 15 1 15, .mul 15 0 15, .mul 15 3 15, .mul 15 0 15, .mul 15 3 15, .mul 15 0 15,
      .mul 15 2 15, .mul 15 0 15, .mul 15 3 15, .mul 15 0 15, .mul 15 1 15, .mul 15 0 15,
      .mul 15 3 15, .mul 15 0 15, .mul 15 3 15, .mul 15 0 15, .mul 15 2 15, .mul 15 0 15,
      .mul 15 3 15, .mul 15 0 15, .mul 15 1 15, .mul 15 0 15, .mul 15 3 15, .mul 15 0 15,
      .mul 15 3 15, .mul 15 0 15, .mul 15 6 15, .mul 15 0 15, .mul 15 2 15, .mul 15 0 15,
      .mul 15 1 15, .mul 15 0 15, .mul 15 3 15, .mul 15 0 15, .mul 15 1 15, .mul 15 0 15,
      .mul 15 3 15, .mul 15 0 15, .mul 15 3 15, .mul 15 0 15, .mul 15 2 15, .mul 15 0 15,
      .mul 15 3 15, .mul 15 0 15, .mul 15 1 15, .mul 15 0 15, .mul 15 3 15, .mul 15 0 15,
      .mul 15 3 15, .mul 15 0 15, .mul 15 6 15, .mul 15 0 15, .mul 15 2 15, .mul 15 0 15,
      .mul 15 3 15, .mul 15 0 15, .mul 15 1 15, .mul 15 0 15, .mul 15 6 15, .mul 15 0 15,
      .mul 15 1 15, .mul 15 0 15, .mul 15 1 15, .mul 15 0 15, .mul 15 1 15, .mul 15 0 15,
      .mul 15 1 15, .mul 15 0 15, .mul 15 1 15, .mul 15 0 15, .mul 15 1 15, .mul 15 0 15,
      .mul 15 1 15, .mul 15 0 15, .mul 15 2 15, .pow 1 0 16, .mul 16 3 16, .mul 16 0 16,
      .mul 16 1 16, .mul 16 0 16, .mul 16 6 16, .mul 16 0 16, .mul 16 6 16, .mul 16 0 16,
      .mul 16 2 16, .mul 16 0 16, .mul 16 1 16, .mul 16 0 16, .mul 16 6 16, .mul 16 0 16,
      .mul 16 5 16, .mul 16 0 16, .mul 16 5 16, .mul 16 0 16, .mul 16 2 16, .mul 16 0 16,
      .mul 16 5 16, .mul 16 0 16, .mul 16 1 16, .mul 16 0 16, .mul 16 4 16, .mul 16 0 16,
      .mul 16 4 16, .mul 16 0 16, .mul 16 6 16, .mul 16 0 16, .mul 16 4 16, .mul 16 0 16,
      .mul 16 4 16, .mul 16 0 16, .mul 16 1 16, .mul 16 0 16, .mul 16 4 16, .mul 16 0 16,
      .mul 16 4 16, .mul 16 0 16, .mul 16 6 16, .mul 16 0 16, .mul 16 4 16, .mul 16 0 16,
      .mul 16 5 16, .mul 16 0 16, .mul 16 4 16, .mul 16 0 16, .mul 16 4 16, .mul 16 0 16,
      .mul 16 6 16, .mul 16 0 16, .mul 16 4 16, .mul 16 0 16, .mul 16 6 16, .mul 16 0 16,
      .mul 16 6 16, .mul 16 0 16, .mul 16 4 16, .mul 16 0 16, .mul 16 4 16, .mul 16 0 16,
      .mul 16 6 16, .mul 16 0 16, .mul 16 4 16, .mul 16 0 16, .mul 16 5 16, .mul 16 0 16,
      .mul 16 4 16, .mul 16 0 16, .mul 16 4 16, .mul 16 0 16, .mul 16 6 16, .mul 16 0 16,
      .mul 16 4 16, .mul 16 0 16, .mul 16 2 16, .mul 16 0 16, .mul 16 6 16, .mul 16 0 16,
      .mul 16 4 16, .mul 16 0 16, .mul 16 6 16, .mul 16 0 16, .mul 16 4 16, .mul 16 0 16,
      .mul 16 1 16]
  facts := [
      MFact.ord 7 3,
      MFact.ord 8 3,
      MFact.eq [(7, 1), (8, 1), (7, 2), (8, 2), (7, 1)]
        [(7, 1), (7, 1), (8, 1), (7, 2), (8, 2)],
      MFact.eq [(7, 1), (8, 1), (7, 2), (8, 2), (8, 1)]
        [(8, 1), (7, 1), (8, 1), (7, 2), (8, 2)],
      MFact.ne [(7, 1), (8, 1), (7, 2), (8, 2)]
        [] 0,
      MFact.ord 9 6,
      MFact.conj 9 [(7, 1), (8, 1), (7, 2), (8, 2)]
        [(7, 1), (8, 1), (7, 2), (8, 2), (7, 1), (8, 1), (7, 2), (8, 2)],
      MFact.conj 9 [(7, 1)]
        [(7, 1), (8, 1), (7, 2), (8, 2), (7, 1), (8, 1), (7, 2), (8, 2), (7, 1), (7, 1)],
      MFact.ord 10 4,
      MFact.conj 10 [(7, 1), (8, 1), (7, 2), (8, 2)]
        [(7, 1), (8, 1), (7, 2), (8, 2), (7, 1), (8, 1), (7, 2), (8, 2)],
      MFact.conj 10 [(7, 1)]
        [(7, 1)],
      MFact.ord 11 6,
      MFact.conj 11 [(7, 1), (8, 1), (7, 2), (8, 2)]
        [(7, 1), (8, 1), (7, 2), (8, 2), (7, 1), (8, 1), (7, 2), (8, 2)],
      MFact.conj 11 [(8, 1)]
        [(7, 1), (8, 1), (7, 2), (8, 2), (7, 1), (8, 1), (7, 2), (8, 2), (8, 1), (8, 1)],
      MFact.ord 12 6,
      MFact.conj 12 [(7, 1), (8, 1), (7, 2), (8, 2)]
        [(7, 1), (8, 1), (7, 2), (8, 2), (7, 1), (8, 1), (7, 2), (8, 2)],
      MFact.conj 12 [(8, 1)]
        [(8, 1)],
      MFact.ord 13 6,
      MFact.conj 13 [(7, 1), (8, 1), (7, 2), (8, 2)]
        [(7, 1), (8, 1), (7, 2), (8, 2), (7, 1), (8, 1), (7, 2), (8, 2)],
      MFact.conj 13 [(7, 1), (8, 1)]
        [(7, 1), (8, 1), (7, 2), (8, 2), (7, 1), (8, 1), (7, 2), (8, 2), (7, 1), (8, 1), (7, 1),
        (8, 1)],
      MFact.ord 14 6,
      MFact.conj 14 [(7, 1), (8, 1), (7, 2), (8, 2)]
        [(7, 1), (8, 1), (7, 2), (8, 2), (7, 1), (8, 1), (7, 2), (8, 2)],
      MFact.conj 14 [(7, 1), (8, 1)]
        [(7, 1), (8, 1)],
      MFact.ord 15 6,
      MFact.conj 15 [(7, 1), (8, 1), (7, 2), (8, 2)]
        [(7, 1), (8, 1), (7, 2), (8, 2), (7, 1), (8, 1), (7, 2), (8, 2)],
      MFact.conj 15 [(7, 1), (8, 2)]
        [(7, 1), (8, 1), (7, 2), (8, 2), (7, 1), (8, 1), (7, 2), (8, 2), (7, 1), (8, 2), (7, 1),
        (8, 2)],
      MFact.ord 16 4,
      MFact.conj 16 [(7, 1), (8, 1), (7, 2), (8, 2)]
        [(7, 1), (8, 1), (7, 2), (8, 2), (7, 1), (8, 1), (7, 2), (8, 2)],
      MFact.conj 16 [(7, 1), (8, 2)]
        [(7, 1), (8, 2)]]

end CFSG.RankThree.Asc83Table.He
