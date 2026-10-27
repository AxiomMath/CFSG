module

public import CFSG.RankThree.PartOne.F106.FiveRank
public import CFSG.RankThree.PartOne.F106.ConvItems
public import CFSG.RankThree.PartOne.F106.ConvOdd
public import CFSG.RankThree.PartOne.N143.Weyl613Bridge
public import CFSG.RankThree.PartOne.S12K.Rigidity

public section

namespace CFSG.RankThree.PartOne.F106

open CFSG.RankThree.PartOne.N143 CFSG.RankThree.PartOne.S12K

section Certs


theorem evenListConverse_of : EvenListConverse := by
  intro X _ _ hs _ hEven hList
  obtain ⟨t, n, f, hadm, hmodel⟩ := hEven
  obtain ⟨-, hcard⟩ := card_of_lieModel_two hmodel
  rcases hList with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact ⟨t, n, f, hadm, hmodel, smallEvenParams_of_odd_item hadm hcard (Or.inl h1)⟩
  · exact ⟨t, n, f, hadm, hmodel,
      smallEvenParams_of_odd_item hadm hcard (Or.inr (Or.inl h2))⟩
  · exact ⟨t, n, f, hadm, hmodel,
      smallEvenParams_of_finite_item hs hadm hcard (Or.inl h3)⟩
  · exact ⟨t, n, f, hadm, hmodel,
      smallEvenParams_of_odd_item hadm hcard (Or.inr (Or.inr h4))⟩
  · exact ⟨t, n, f, hadm, hmodel,
      smallEvenParams_of_finite_item hs hadm hcard (Or.inr (Or.inl h5))⟩
  · exact ⟨t, n, f, hadm, hmodel,
      smallEvenParams_of_finite_item hs hadm hcard (Or.inr (Or.inr h6))⟩
  · exact evenLieTypeSmall_of_item789 (Or.inl h7)
  · exact evenLieTypeSmall_of_item789 (Or.inr (Or.inl h8))
  · exact evenLieTypeSmall_of_item789 (Or.inr (Or.inr h9))

end Certs

end CFSG.RankThree.PartOne.F106
