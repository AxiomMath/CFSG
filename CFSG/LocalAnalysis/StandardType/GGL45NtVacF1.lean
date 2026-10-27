module

public import CFSG.LocalAnalysis.StandardType.GGL45NtDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggL45NtVacOn_trivialF :
    GGL45NtVacOn fun p lab => GGL45FamNonTorsion p lab ∧
      (lab.tag = .B2der ∨ lab.tag = .G2der ∨ lab.tag = .twF4der) := by
  intro p hp _hp2 lab hlab _hkg hS Q hQ
  obtain ⟨tag, rank, n⟩ := lab
  rcases hS.2 with hB2 | hG2 | hF4
  ·
    subst hB2
    dsimp only [LargeEvenInLambda2] at hlab
    obtain ⟨-, hn⟩ := hlab.2
    dsimp only [CFSG.StandardType.LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, hf, hfin, hK, hQ'⟩ := hQ
    refine ⟨K, hf, hfin, hK, hQ', Or.inl ?_⟩
    intro f hfF
    rw [matFieldImage_eq_one_of_card_two hK _ hfF, orderOf_one]
    exact fun h => hp.ne_one h.symm
  ·
    subst hG2
    dsimp only [LargeEvenInLambda2] at hlab
    obtain ⟨-, hn⟩ := hlab.2
    dsimp only [CFSG.StandardType.LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, hf, hfin, hK, hQ'⟩ := hQ
    refine ⟨K, hf, hfin, hK, hQ', Or.inl ?_⟩
    intro f hfF
    rw [chevFieldImage_eq_one_of_card_two hK _ hfF, orderOf_one]
    exact fun h => hp.ne_one h.symm
  ·
    subst hF4
    dsimp only [LargeEvenInLambda2] at hlab
    obtain ⟨-, hn⟩ := hlab.2
    dsimp only [CFSG.StandardType.LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, hf, hfin, hK, hQ'⟩ := hQ
    have hK2 : Nat.card K = 2 := by simpa [hn] using hK
    refine ⟨K, hf, hfin, hK, hQ', Or.inl ?_⟩
    intro f hfF
    rw [chevFieldImage_eq_one_of_card_two hK2 _ hfF, orderOf_one]
    exact fun h => hp.ne_one h.symm

end CFSG.StandardType
