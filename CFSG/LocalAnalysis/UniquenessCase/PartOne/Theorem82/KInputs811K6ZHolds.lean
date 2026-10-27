module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811
import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Mult

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

theorem k6ZL4_holds :
    K6ZL4 := by
  intro Y _ _ r hY hr
  obtain ⟨hq, -, hr', -, hm⟩ := hY
  have h2 : IsPGroup 2 (Subgroup.center Y) := by
    refine CFSG.ComponentClassification.CatFactsL4U4.Cover82.multiplierL4U4 Y hq r 1 hr'
      (by omega) le_rfl ?_
    rcases hm with ⟨-, hm⟩ | ⟨-, hm⟩
    · exact Or.inl hm
    · exact Or.inr ⟨hm, by rw [pow_one]; omega⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h2
  intro hdvd
  rw [hk] at hdvd
  have := (Nat.prime_dvd_prime_iff_eq hr' Nat.prime_two).mp (hr'.dvd_of_dvd_pow hdvd)
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
