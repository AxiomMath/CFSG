module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3IrrCountA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3IrrCountB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W] {A L T : Subgroup (MulAut W)}

theorem ThreeNat.odd_card_irrSet (h : ThreeNat A L T) : Odd (Nat.card ↥(irrSet L)) :=
  s16t3_odd_card_irr_of_sum_three h.elem h.quasi h.comm h.sum fun I₁ h₁ I₂ h₂ => by
    obtain ⟨g, hg, hgI⟩ := h.trans I₁ h₁ I₂ h₂
    exact ⟨g, hg.2, hgI⟩

theorem ThreeNat.exists_stable_irr (h : ThreeNat A L T)
    (hodd : Odd (Nat.card ↥(irrSet L))) : ∃ I ∈ irrSet L, StableUnder T I :=
  s16t3_exists_stable_irr h hodd

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
