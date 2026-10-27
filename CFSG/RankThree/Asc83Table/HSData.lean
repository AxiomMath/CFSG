module

public import CFSG.RankThree.Asc83Table.MatCertDefs

public section

namespace CFSG.RankThree.Asc83Table.HS

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native

@[expose] def hsCert : MCert where
  nregs := 9
  prog := [
      .pow 2 1 2, .pow 3 1 3, .pow 4 1 4, .pow 1 0 5, .mul 5 2 5, .mul 5 0 5, .mul 5 3 5,
      .mul 5 0 5, .mul 5 3 5, .mul 5 0 5, .mul 5 1 5, .mul 5 0 5, .mul 5 4 5, .mul 5 0 5,
      .mul 5 2 5, .mul 5 0 5, .mul 5 2 5, .mul 5 0 5, .mul 5 4 5, .mul 5 0 5, .mul 5 2 5,
      .mul 5 0 5, .mul 5 1 5, .mul 5 0 5, .mul 5 1 5, .mul 5 0 5, .mul 5 2 5, .mul 5 0 5,
      .mul 5 2 5, .pow 1 0 6, .mul 6 4 6, .mul 6 0 6, .mul 6 1 6, .mul 6 0 6, .mul 6 2 6,
      .mul 6 0 6, .mul 6 1 6, .mul 6 0 6, .mul 6 3 6, .mul 6 0 6, .mul 6 4 6, .mul 6 0 6,
      .mul 6 1 6, .mul 6 0 6, .mul 6 4 6, .mul 6 0 6, .mul 6 3 6, .mul 6 0 6, .mul 6 3 6,
      .mul 6 0 6, .mul 6 4 6, .mul 6 0 6, .mul 6 3 6, .mul 6 0 6, .mul 6 1 6, .pow 1 2 7,
      .mul 7 0 7, .mul 7 3 7, .mul 7 0 7, .mul 7 2 7, .mul 7 0 7, .mul 7 3 7, .mul 7 0 7,
      .mul 7 3 7, .mul 7 0 7, .mul 7 1 7, .mul 7 0 7, .mul 7 4 7, .mul 7 0 7, .mul 7 4 7,
      .mul 7 0 7, .mul 7 3 7, .mul 7 0 7, .mul 7 3 7, .mul 7 0 7, .mul 7 1 7, .mul 7 0 7,
      .mul 7 4 7, .mul 7 0 7, .mul 7 4 7, .mul 7 0 7, .mul 7 4 7, .mul 7 0 7, .mul 7 2 7,
      .mul 7 0 7, .mul 7 1 7, .pow 1 2 8, .mul 8 0 8, .mul 8 3 8, .mul 8 0 8, .mul 8 2 8,
      .mul 8 0 8, .mul 8 3 8, .mul 8 0 8, .mul 8 4 8, .mul 8 0 8, .mul 8 4 8, .mul 8 0 8,
      .mul 8 2 8, .mul 8 0 8, .mul 8 4 8, .mul 8 0 8, .mul 8 4 8, .mul 8 0 8, .mul 8 2 8,
      .mul 8 0 8, .mul 8 3 8, .mul 8 0 8, .mul 8 3 8, .mul 8 0 8, .mul 8 4 8, .mul 8 0 8,
      .mul 8 1 8, .mul 8 0 8, .mul 8 2 8, .mul 8 0 8, .mul 8 2 8, .mul 8 0 8, .mul 8 1 8,
      .mul 8 0 8, .mul 8 3 8, .mul 8 0 8, .mul 8 1 8, .mul 8 0 8, .mul 8 2 8, .mul 8 0 8,
      .mul 8 3 8]
  facts := [
      MFact.ord 5 3,
      MFact.ord 6 3,
      MFact.ord 7 8,
      MFact.ord 8 6,
      MFact.eq [(5, 1), (6, 1)] [(6, 1), (5, 1)],
      MFact.ne [(5, 1)] [] 0,
      MFact.ne [(6, 1)] [] 0,
      MFact.ne [(6, 1)] [(5, 1)] 0,
      MFact.ne [(6, 1)] [(5, 2)] 0,
      MFact.conj 7 [(5, 1)] [(5, 0), (6, 1)],
      MFact.conj 7 [(6, 1)] [(5, 1), (6, 1)],
      MFact.conj 8 [(5, 1)] [(5, 1), (6, 1)],
      MFact.conj 8 [(6, 1)] [(5, 0), (6, 2)]]

end CFSG.RankThree.Asc83Table.HS
