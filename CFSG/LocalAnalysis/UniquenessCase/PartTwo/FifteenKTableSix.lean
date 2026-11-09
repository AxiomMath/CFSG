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

private def s15k_witOK (Q : M → ZMod 2) (z a₀ b₀ a₁ b₁ : M) : Prop :=
  Q a₀ = 1 ∧ QuadraticMap.polar Q z a₀ = 0 ∧
    Q b₀ = 1 ∧ QuadraticMap.polar Q z b₀ = 0 ∧ QuadraticMap.polar Q a₀ b₀ = 1 ∧
    Q a₁ = 1 ∧ QuadraticMap.polar Q z a₁ = 0 ∧ QuadraticMap.polar Q a₀ a₁ = 0 ∧
    QuadraticMap.polar Q b₀ a₁ = 0 ∧
    Q b₁ = 1 ∧ QuadraticMap.polar Q z b₁ = 0 ∧ QuadraticMap.polar Q a₀ b₁ = 0 ∧
    QuadraticMap.polar Q b₀ b₁ = 0 ∧ QuadraticMap.polar Q a₁ b₁ = 1

private instance (Q : M → ZMod 2) (z a₀ b₀ a₁ b₁ : M) :
    Decidable (s15k_witOK Q z a₀ b₀ a₁ b₁) := by
  unfold s15k_witOK
  infer_instance

private theorem s15k_P1_of_witOK {Q : M → ZMod 2} {z a₀ b₀ a₁ b₁ : M}
    (h : s15k_witOK Q z a₀ b₀ a₁ b₁) : s15k_tsix_P1 Q z := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  unfold s15k_tsix_P1 s15k_tsix_P2 s15k_tsix_P3 s15k_tsix_P4
  exact ⟨a₀, h1, h2, b₀, h3, h4, h5, a₁, h6, h7, h8, h9, b₁, h10, h11, h12, h13, h14⟩

end Chain

private theorem s15k_tsix_plus_all :
    ∀ z : Fin 3 ⊕ Fin 3 → ZMod 2, s15k_tsix_P1 (StatedQuadPlus 3 (ZMod 2)) z := by
  decide +kernel

theorem s15k_table_plus_three (z : Fin 3 ⊕ Fin 3 → ZMod 2) :
    s15kPlanePair (quadPlus 3 (ZMod 2)) z := by
  apply s15k_tsix_planePair
  rw [coe_quadPlus]
  exact s15k_tsix_plus_all z

private def s15k_bit : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → ℕ
  | Sum.inl i => i.val
  | Sum.inr (Sum.inl j) => 3 + j.val
  | Sum.inr (Sum.inr k) => 6 + k.val

private def s15k_vec (n : ℕ) : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → ZMod 2 :=
  fun c => if n.testBit (s15k_bit c) then 1 else 0

private def s15k_code (z : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → ZMod 2) : ℕ :=
  (z (Sum.inl 0)).val + 2 * (z (Sum.inl 1)).val + 4 * (z (Sum.inl 2)).val +
    8 * (z (Sum.inr (Sum.inl 0))).val + 16 * (z (Sum.inr (Sum.inl 1))).val +
    32 * (z (Sum.inr (Sum.inl 2))).val + 64 * (z (Sum.inr (Sum.inr 0))).val +
    128 * (z (Sum.inr (Sum.inr 1))).val

private def s15k_witTab : List (ℕ × ℕ × ℕ × ℕ) := [
  (9, 19, 11, 18), (18, 38, 22, 36), (9, 37, 13, 36), (25, 37, 29, 36), (9, 19, 11, 18),
  (18, 43, 19, 41), (9, 51, 11, 50), (25, 43, 26, 41), (18, 38, 22, 36), (11, 18, 13, 36),
  (19, 38, 23, 36), (9, 19, 15, 36), (18, 39, 22, 37), (9, 37, 15, 18), (19, 39, 23, 37),
  (9, 19, 11, 50), (9, 37, 13, 36), (11, 37, 15, 36), (9, 19, 22, 36), (11, 18, 23, 36),
  (9, 39, 13, 38), (11, 39, 15, 38), (9, 19, 18, 43), (11, 18, 19, 41), (11, 39, 15, 36),
  (9, 19, 29, 36), (11, 18, 30, 36), (9, 39, 13, 36), (11, 37, 15, 38), (9, 19, 25, 43),
  (11, 18, 26, 41), (9, 37, 13, 38), (9, 19, 11, 18), (13, 19, 15, 18), (9, 23, 11, 22),
  (13, 23, 15, 22), (9, 19, 11, 18), (13, 19, 15, 18), (9, 23, 11, 22), (13, 23, 15, 22),
  (13, 23, 15, 18), (9, 23, 11, 18), (13, 19, 15, 22), (9, 19, 11, 22), (13, 23, 15, 18),
  (9, 23, 11, 18), (13, 19, 15, 22), (9, 19, 11, 22), (9, 23, 15, 22), (11, 22, 13, 23),
  (9, 19, 15, 18), (11, 18, 13, 19), (9, 23, 15, 22), (11, 22, 13, 23), (9, 19, 15, 18),
  (11, 18, 13, 19), (11, 22, 13, 19), (9, 19, 15, 22), (11, 18, 13, 23), (9, 23, 15, 18),
  (11, 22, 13, 19), (9, 19, 15, 22), (11, 18, 13, 23), (9, 23, 15, 18), (9, 19, 11, 18),
  (18, 38, 22, 36), (9, 37, 13, 36), (25, 37, 29, 36), (9, 19, 11, 18), (18, 43, 19, 41),
  (9, 51, 11, 50), (25, 43, 26, 41), (18, 38, 22, 36), (9, 129, 18, 38), (19, 38, 23, 36),
  (9, 19, 11, 182), (18, 39, 22, 37), (9, 37, 13, 182), (19, 39, 23, 37), (9, 19, 11, 50),
  (9, 37, 13, 36), (11, 37, 15, 36), (9, 19, 18, 175), (11, 18, 19, 173), (9, 39, 13, 38),
  (11, 39, 15, 38), (9, 19, 18, 43), (11, 18, 19, 41), (11, 39, 15, 36), (9, 19, 25, 175),
  (11, 18, 26, 173), (9, 39, 13, 36), (11, 37, 15, 38), (9, 19, 25, 43), (11, 18, 26, 41),
  (9, 37, 13, 38), (9, 19, 11, 18), (13, 19, 15, 18), (9, 23, 11, 22), (13, 23, 15, 22),
  (9, 19, 11, 18), (13, 19, 15, 18), (9, 23, 11, 22), (13, 23, 15, 22), (13, 23, 15, 18),
  (9, 23, 11, 18), (13, 19, 15, 22), (9, 19, 11, 22), (13, 23, 15, 18), (9, 23, 11, 18),
  (13, 19, 15, 22), (9, 19, 11, 22), (9, 23, 15, 22), (11, 22, 13, 23), (9, 19, 15, 18),
  (11, 18, 13, 19), (9, 23, 15, 22), (11, 22, 13, 23), (9, 19, 15, 18), (11, 18, 13, 19),
  (11, 22, 13, 19), (9, 19, 15, 22), (11, 18, 13, 23), (9, 23, 15, 18), (11, 22, 13, 19),
  (9, 19, 15, 22), (11, 18, 13, 23), (9, 23, 15, 18), (9, 19, 11, 18), (18, 38, 22, 36),
  (9, 37, 13, 36), (25, 37, 29, 36), (9, 19, 11, 18), (18, 43, 19, 41), (9, 51, 11, 50),
  (25, 43, 26, 41), (18, 38, 22, 36), (9, 65, 18, 38), (19, 38, 23, 36), (9, 19, 11, 118),
  (18, 39, 22, 37), (9, 37, 13, 118), (19, 39, 23, 37), (9, 19, 11, 50), (9, 37, 13, 36),
  (11, 37, 15, 36), (9, 19, 18, 111), (11, 18, 19, 109), (9, 39, 13, 38), (11, 39, 15, 38),
  (9, 19, 18, 43), (11, 18, 19, 41), (11, 39, 15, 36), (9, 19, 25, 111), (11, 18, 26, 109),
  (9, 39, 13, 36), (11, 37, 15, 38), (9, 19, 25, 43), (11, 18, 26, 41), (9, 37, 13, 38),
  (9, 19, 11, 18), (13, 19, 15, 18), (9, 23, 11, 22), (13, 23, 15, 22), (9, 19, 11, 18),
  (13, 19, 15, 18), (9, 23, 11, 22), (13, 23, 15, 22), (13, 23, 15, 18), (9, 23, 11, 18),
  (13, 19, 15, 22), (9, 19, 11, 22), (13, 23, 15, 18), (9, 23, 11, 18), (13, 19, 15, 22),
  (9, 19, 11, 22), (9, 23, 15, 22), (11, 22, 13, 23), (9, 19, 15, 18), (11, 18, 13, 19),
  (9, 23, 15, 22), (11, 22, 13, 23), (9, 19, 15, 18), (11, 18, 13, 19), (11, 22, 13, 19),
  (9, 19, 15, 22), (11, 18, 13, 23), (9, 23, 15, 18), (11, 22, 13, 19), (9, 19, 15, 22),
  (11, 18, 13, 23), (9, 23, 15, 18), (9, 19, 11, 18), (18, 38, 22, 36), (9, 37, 13, 36),
  (25, 37, 29, 36), (9, 19, 11, 18), (18, 43, 19, 41), (9, 51, 11, 50), (25, 43, 26, 41),
  (18, 38, 22, 36), (9, 65, 18, 38), (19, 38, 23, 36), (9, 19, 11, 118), (18, 39, 22, 37),
  (9, 37, 13, 118), (19, 39, 23, 37), (9, 19, 11, 50), (9, 37, 13, 36), (11, 37, 15, 36),
  (9, 19, 18, 111), (11, 18, 19, 109), (9, 39, 13, 38), (11, 39, 15, 38), (9, 19, 18, 43),
  (11, 18, 19, 41), (11, 39, 15, 36), (9, 19, 25, 111), (11, 18, 26, 109), (9, 39, 13, 36),
  (11, 37, 15, 38), (9, 19, 25, 43), (11, 18, 26, 41), (9, 37, 13, 38), (9, 19, 11, 18),
  (13, 19, 15, 18), (9, 23, 11, 22), (13, 23, 15, 22), (9, 19, 11, 18), (13, 19, 15, 18),
  (9, 23, 11, 22), (13, 23, 15, 22), (13, 23, 15, 18), (9, 23, 11, 18), (13, 19, 15, 22),
  (9, 19, 11, 22), (13, 23, 15, 18), (9, 23, 11, 18), (13, 19, 15, 22), (9, 19, 11, 22),
  (9, 23, 15, 22), (11, 22, 13, 23), (9, 19, 15, 18), (11, 18, 13, 19), (9, 23, 15, 22),
  (11, 22, 13, 23), (9, 19, 15, 18), (11, 18, 13, 19), (11, 22, 13, 19), (9, 19, 15, 22),
  (11, 18, 13, 23), (9, 23, 15, 18), (11, 22, 13, 19), (9, 19, 15, 22), (11, 18, 13, 23),
  (9, 23, 15, 18)
]

private def s15k_wit (z : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → ZMod 2) : ℕ × ℕ × ℕ × ℕ :=
  s15k_witTab.getD (s15k_code z) (0, 0, 0, 0)

private theorem s15k_tsix_minus_four_wit :
    ∀ z : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → ZMod 2, s15k_witOK (StatedQuadMinus 4 (ZMod 2) 1 1) z
      (s15k_vec (s15k_wit z).1) (s15k_vec (s15k_wit z).2.1) (s15k_vec (s15k_wit z).2.2.1)
      (s15k_vec (s15k_wit z).2.2.2) := by
  decide +kernel

private theorem s15k_tsix_minus_four_all :
    ∀ z : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → ZMod 2, s15k_tsix_P1 (StatedQuadMinus 4 (ZMod 2) 1 1) z :=
  fun z => s15k_P1_of_witOK (s15k_tsix_minus_four_wit z)

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
