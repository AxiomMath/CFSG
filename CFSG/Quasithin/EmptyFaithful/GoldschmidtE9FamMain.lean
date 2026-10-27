module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE9FamDefs

public section

namespace CFSG.Quasithin.E9

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin

theorem famE9_of_dich (hBlkL2 : DichE9BlockL2) (hBlkA5 : DichE9BlockA5) (hL2 : DichE9L2)
    (hSz : DichE9Sz) (hU3 : DichE9U3) (hL3 : DichE9L3) (hSp4 : DichE9Sp4) : FamE9 := by
  intro G _ _ X S L hStd hant
  rcases hant with ⟨hchar, hth, hbl, hty⟩ | ⟨hco, hZ, hz, hA | hB⟩
  · rcases hty with h5 | ⟨n, hn, hLn⟩
    · exact Or.inr (Or.inl (hBlkA5 G X S L hStd hth hchar hbl h5))
    · rcases hBlkL2 G X S L hStd hth hchar hbl ⟨n, hn, hLn⟩ with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  · rcases hA with hBender | hSz8
    · rcases hBender with ⟨n, hn, h⟩ | ⟨e, h⟩ | ⟨n, hn, h⟩
      · rcases hL2 G X S L hStd hco hZ ⟨n, hn, h⟩ with h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inl h')
      · exact Or.inl (hSz G X S L hStd hco hZ (Or.inl ⟨e, h⟩))
      · rcases hU3 G X S L hStd hco hZ ⟨n, hn, h⟩ with h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inr h')
    · exact Or.inl (hSz G X S L hStd hco hZ (Or.inr hSz8))
  · rcases hB with ⟨n, hn, h⟩ | ⟨n, hn, h⟩ | h
    · rcases hL3 G X S L hStd hz hco hZ (Or.inl ⟨n, hn, h⟩) with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
    · rcases hSp4 G X S L hStd hco hZ ⟨n, hn, h⟩ with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
    · rcases hL3 G X S L hStd hz hco hZ (Or.inr h) with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')

end CFSG.Quasithin.E9
