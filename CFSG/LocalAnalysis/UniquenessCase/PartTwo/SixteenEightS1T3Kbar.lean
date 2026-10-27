module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3KbarA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W] {A L T : Subgroup (MulAut W)}

theorem ThreeNat.card_irrSet_eq (h : ThreeNat A L T) :
    Nat.card ↥(irrSet L) = 3 ∨ Nat.card ↥(irrSet L) = 7 :=
  s16t3_card_irr_of_sum_three h.elem h.quasi h.comm h.sum fun I₁ h₁ I₂ h₂ => by
    obtain ⟨g, hg, hI⟩ := h.trans I₁ h₁ I₂ h₂
    exact ⟨g, hg.2, hI⟩

theorem ThreeNat.structure_of_seven (h : ThreeNat A L T) (h7 : Nat.card ↥(irrSet L) = 7) :
    ∃ N : Subgroup (MulAut W), N ≤ A ∧ L ≤ N ∧
      (∀ a ∈ N, ∀ I ∈ irrSet L, I.map a.toMonoidHom = I) ∧
      (∀ n ∈ N, ∀ k ∈ s1t3KBar A L, n * k = k * n) ∧ N ⊓ s1t3KBar A L = ⊥ ∧ N ⊔ s1t3KBar A L = A ∧
      (Nat.card ↥(s1t3KBar A L) = 7 ∨ Nat.card ↥(s1t3KBar A L) = 21 ∨
        (Nat.card ↥(s1t3KBar A L) = 168 ∧ IsSimpleGroup ↥(s1t3KBar A L))) :=
  s16t3_structure_of_seven h h7

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
