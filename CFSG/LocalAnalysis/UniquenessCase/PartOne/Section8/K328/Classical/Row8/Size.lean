module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Rows
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Classical.Row8.Pos
import CFSG.Adapters.LieModelSmallOrders

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

open CFSG.Open

private theorem k328r8s_pos_card {K : Type} [Group K] [Finite K] {Z X : Subgroup K}
    (h : Pos K Z X) : Nat.card X = 60480 ∨ Nat.card X = 16547328 := by
  obtain ⟨-, -, -, -, -, hcen, hlie⟩ := h
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥X)
  rw [hcen] at hmul
  rcases hlie with hl | hl
  · left
    rw [hmul, hl.card_psl_three_four]
  · right
    rw [hmul, CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_eight
      (hl.statedClassicalModel (by decide))]

theorem row8_size (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 8) (b c : F)
    (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (α : F) (hα : α ^ 2 + α = 1 + c / b ^ 2) :
    let e : Fin 3 → (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) := fun i => bv F (Sum.inl i)
    let f : Fin 3 → (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) := fun i => bv F (Sum.inr (Sum.inl i))
    let u : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F := bv F (Sum.inr (Sum.inr 0))
    let v : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F := bv F (Sum.inr (Sum.inr 1))
    ∀ z₀ t₀ : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F,
    (z₀ : Matrix _ _ F) = ofColumns F (Sum.elim ![e 0 + f 1, f 0 + e 1, e 2]
      (Sum.elim ![e 1, e 0, f 2] ![α • u + b⁻¹ • v, (c / b) • u + (α + 1) • v])) →
    (t₀ : Matrix _ _ F) = ofColumns F (Sum.elim ![e 1, e 0 + e 1, e 2]
      (Sum.elim ![f 0 + f 1, f 0, f 2] ![u, v])) →
    SizeLeaf (StatedOmega (StatedQuadMinus 4 F b c)) z₀ := by
  intro e f u v z₀ t₀ hz ht hz₀ X hXstd hpos
  have hXH : X ≤ StatedOmega (StatedQuadMinus 4 F b c) := hXstd.trans (stdComp_le _ _)
  have hXcard : Nat.card X = 60480 ∨ Nat.card X = 16547328 := by
    have h := k328r8s_pos_card hpos
    rwa [card_subgroupOf_of_le hXH] at h
  have hstd : Nat.card (stdComp (StatedOmega (StatedQuadMinus 4 F b c)) z₀) = 16547328 :=
    row8_card_stdComp F hF b c hbc α hα z₀ hz
  have hdvd : Nat.card X ∣ Nat.card (stdComp (StatedOmega (StatedQuadMinus 4 F b c)) z₀) :=
    Subgroup.card_dvd_of_le hXstd
  rw [hstd] at hdvd
  rcases hXcard with h | h
  · rw [h] at hdvd
    exact absurd hdvd (by norm_num)
  · rw [h, hstd]

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328
