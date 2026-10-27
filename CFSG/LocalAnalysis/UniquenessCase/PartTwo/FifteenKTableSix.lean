module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKTableDefs
public import CFSG.LieType.Universal.Spin.Forms

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.LieType.Universal.Spin

section Chain

variable {M : Type} [AddCommGroup M] [Fintype M] [DecidableEq M]

private def s15k_tsix_P4 (Q : M → ZMod 2) (z a₀ b₀ a₁ : M) : Prop :=
  ∃ b₁ : M, Q b₁ = 1 ∧ QuadraticMap.polar Q z b₁ = 0 ∧ QuadraticMap.polar Q a₀ b₁ = 0 ∧
    QuadraticMap.polar Q b₀ b₁ = 0 ∧ QuadraticMap.polar Q a₁ b₁ = 1

private instance (Q : M → ZMod 2) (z a₀ b₀ a₁ : M) : Decidable (s15k_tsix_P4 Q z a₀ b₀ a₁) := by
  unfold s15k_tsix_P4
  infer_instance

private def s15k_tsix_P3 (Q : M → ZMod 2) (z a₀ b₀ : M) : Prop :=
  ∃ a₁ : M, Q a₁ = 1 ∧ QuadraticMap.polar Q z a₁ = 0 ∧ QuadraticMap.polar Q a₀ a₁ = 0 ∧
    QuadraticMap.polar Q b₀ a₁ = 0 ∧ s15k_tsix_P4 Q z a₀ b₀ a₁

private instance (Q : M → ZMod 2) (z a₀ b₀ : M) : Decidable (s15k_tsix_P3 Q z a₀ b₀) := by
  unfold s15k_tsix_P3
  infer_instance

private def s15k_tsix_P2 (Q : M → ZMod 2) (z a₀ : M) : Prop :=
  ∃ b₀ : M, Q b₀ = 1 ∧ QuadraticMap.polar Q z b₀ = 0 ∧ QuadraticMap.polar Q a₀ b₀ = 1 ∧
    s15k_tsix_P3 Q z a₀ b₀

private instance (Q : M → ZMod 2) (z a₀ : M) : Decidable (s15k_tsix_P2 Q z a₀) := by
  unfold s15k_tsix_P2
  infer_instance

private def s15k_tsix_P1 (Q : M → ZMod 2) (z : M) : Prop :=
  ∃ a₀ : M, Q a₀ = 1 ∧ QuadraticMap.polar Q z a₀ = 0 ∧ s15k_tsix_P2 Q z a₀

private instance (Q : M → ZMod 2) (z : M) : Decidable (s15k_tsix_P1 Q z) := by
  unfold s15k_tsix_P1
  infer_instance

private theorem s15k_tsix_planePair {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} {z : V} (h : s15k_tsix_P1 (M := V) Q z) :
    s15kPlanePair Q z := by
  obtain ⟨a₀, ha₀, hza₀, b₀, hb₀, hzb₀, hab₀, a₁, ha₁, hza₁, h0a₁, h0b₁, b₁, hb₁, hzb₁, h1, h2,
    h3⟩ := h
  exact ⟨a₀, b₀, a₁, b₁, ha₀, hb₀, hab₀, ha₁, hb₁, h3, h0a₁, h1, h0b₁, h2, hza₀, hzb₀, hza₁, hzb₁⟩

private def s15k_tsix_R2 (Q : M → ZMod 2) (z a₀ : M) : Prop :=
  ∃ b₀ : M, Q b₀ = 1 ∧ QuadraticMap.polar Q z b₀ = 0 ∧ QuadraticMap.polar Q a₀ b₀ = 1

private instance (Q : M → ZMod 2) (z a₀ : M) : Decidable (s15k_tsix_R2 Q z a₀) := by
  unfold s15k_tsix_R2
  infer_instance

private def s15k_tsix_R1 (Q : M → ZMod 2) (z : M) : Prop :=
  ∃ a₀ : M, Q a₀ = 1 ∧ QuadraticMap.polar Q z a₀ = 0 ∧ s15k_tsix_R2 Q z a₀

private instance (Q : M → ZMod 2) (z : M) : Decidable (s15k_tsix_R1 Q z) := by
  unfold s15k_tsix_R1
  infer_instance

private theorem s15k_tsix_plane {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} {z : V} (h : s15k_tsix_R1 (M := V) Q z) : s15kPlane Q z := by
  obtain ⟨a₀, ha₀, hza₀, b₀, hb₀, hzb₀, hab₀⟩ := h
  exact ⟨a₀, b₀, ha₀, hb₀, hab₀, hza₀, hzb₀⟩

end Chain

private theorem s15k_tsix_plus_all :
    ∀ z : Fin 3 ⊕ Fin 3 → ZMod 2, s15k_tsix_P1 (StatedQuadPlus 3 (ZMod 2)) z := by
  decide +kernel

theorem s15k_table_plus_three (z : Fin 3 ⊕ Fin 3 → ZMod 2) :
    s15kPlanePair (quadPlus 3 (ZMod 2)) z := by
  apply s15k_tsix_planePair
  rw [coe_quadPlus]
  exact s15k_tsix_plus_all z

private theorem s15k_tsix_minus_four_all :
    ∀ z : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → ZMod 2, s15k_tsix_P1 (StatedQuadMinus 4 (ZMod 2) 1 1) z := by
  decide +kernel

theorem s15k_table_minus_four (z : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → ZMod 2) :
    s15kPlanePair (quadMinus 4 (ZMod 2) 1 1) z := by
  apply s15k_tsix_planePair
  rw [coe_quadMinus]
  exact s15k_tsix_minus_four_all z

private theorem s15k_tsix_minus_three_all :
    ∀ z : Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 2, s15k_tsix_R1 (StatedQuadMinus 3 (ZMod 2) 1 1) z := by
  decide +kernel

theorem s15k_table_minus_three (z : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → ZMod 2) :
    s15kPlane (quadMinus 3 (ZMod 2) 1 1) z := by
  apply s15k_tsix_plane
  rw [coe_quadMinus]
  exact s15k_tsix_minus_three_all z

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
