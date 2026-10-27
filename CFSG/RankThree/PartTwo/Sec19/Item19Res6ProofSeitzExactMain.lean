module

public import CFSG.RankThree.PartTwo.Sec19.Item19Res6ProofSeitzExactBlocks
public import CFSG.RankThree.PartTwo.Sec19.Item19Res6ProofSeitzExactLarge
public import CFSG.LieType.SeitzGeneration.OuterGeneric

public section

open scoped commutatorElement MatrixGroups
open Matrix CFSG.LieType.SeitzGeneration CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Phan

namespace CFSG.RankThree.PartTwo.Sec19

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem exactA9_coord_mem (h : UnitaryFieldData ℓ f K) {w α a : K} (hw3 : w ^ 3 = 1)
    (ha : orderOf a = ℓ ^ f + 1) {v : Fin 3 → K} {j : Fin 3} (hv : v = Pi.single j 1) :
    ∃ g ∈ Subgroup.closure (outerHeisExactFix ℓ f K w α),
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = homMat h a (a⁻¹ ^ 2 - a) v := by
  subst hv
  obtain ⟨g, hg⟩ := exists_coord_homology h ha j
  exact ⟨g, coord_homology_mem_exactClosure h hw3 j hg, hg⟩

theorem exactA9_conj_mem (h : UnitaryFieldData ℓ f K) {Q : Subgroup (unitarySU ℓ f K 3)}
    {a κ : K} {y : unitarySU ℓ f K 3} {v : Fin 3 → K} (hyQ : y ∈ Q)
    (hv : ∃ g ∈ Q, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = homMat h a κ v) :
    ∃ g ∈ Q, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      homMat h a κ (((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v) := by
  obtain ⟨g, hgQ, hg⟩ := hv
  exact conj_homology_mem h hyQ hgQ hg

theorem exactA9_norm_mul (h : UnitaryFieldData ℓ f K) {α : K} (hNα : h.bar α * α = 1) (c : K) :
    h.bar (α * c) * (α * c) = h.bar c * c := by
  rw [map_mul]
  linear_combination (h.bar c * c) * hNα

theorem eq_top_of_columns (h : UnitaryFieldData ℓ f K)
    (hq3 : 3 ∣ ℓ ^ f + 1) (hℓ3 : ℓ ≠ 3) (h17 : 17 ≤ ℓ ^ f) (hq : ℓ ^ f ≠ 2)
    {a : K} (ha : orderOf a = ℓ ^ f + 1) {Q : Subgroup (unitarySU ℓ f K 3)}
    (hE0 : ∃ g ∈ Q, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      homMat h a (a⁻¹ ^ 2 - a) ![1, 0, 0])
    (hE1 : ∃ g ∈ Q, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      homMat h a (a⁻¹ ^ 2 - a) ![0, 1, 0])
    (hE2 : ∃ g ∈ Q, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      homMat h a (a⁻¹ ^ 2 - a) ![0, 0, 1])
    {w : Fin 3 → K}
    (hwN : h.bar (w 0) * w 0 + h.bar (w 1) * w 1 + h.bar (w 2) * w 2 = 1)
    (hw0 : w 0 ≠ 0) (hw1 : w 1 ≠ 0) (hw2 : w 2 ≠ 0) (hn2 : h.bar (w 2) * w 2 ≠ 1)
    (hgw : ∃ g ∈ Q, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      homMat h a (a⁻¹ ^ 2 - a) w)
    {z : Fin 3 → K}
    (hzN : h.bar (z 0) * z 0 + h.bar (z 1) * z 1 + h.bar (z 2) * z 2 = 1)
    (hz0 : z 0 ≠ 0) (hz1 : z 1 ≠ 0) (hz2 : z 2 ≠ 0) (hn0 : h.bar (z 0) * z 0 ≠ 1)
    (hgz : ∃ g ∈ Q, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      homMat h a (a⁻¹ ^ 2 - a) z) :
    Q = ⊤ := by
  obtain ⟨s, hs⟩ := exists_shift_su h
  have hB := heisB12_le_of_generic_homology h hq3 hℓ3 h17 ha hE0 hE2 hwN hw0 hw1 hw2 hn2 hgw
  have hB' := heisB12_conj_le_of_generic_homology h hq3 hℓ3 h17 ha s hs hE1 hE0 hzN hz0 hz1 hz2
    hn0 hgz
  exact eq_top_of_heisB12_conj_le h hq hs hB hB'

theorem exactA9_case0 (h : UnitaryFieldData ℓ f K)
    (hq3 : 3 ∣ ℓ ^ f + 1) (hℓ3 : ℓ ≠ 3) (h17 : 17 ≤ ℓ ^ f) (hq : ℓ ^ f ≠ 2)
    {a : K} (ha : orderOf a = ℓ ^ f + 1) {Q : Subgroup (unitarySU ℓ f K 3)}
    (hE0 : ∃ g ∈ Q, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      homMat h a (a⁻¹ ^ 2 - a) ![1, 0, 0])
    (hE1 : ∃ g ∈ Q, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      homMat h a (a⁻¹ ^ 2 - a) ![0, 1, 0])
    (hE2 : ∃ g ∈ Q, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      homMat h a (a⁻¹ ^ 2 - a) ![0, 0, 1])
    {y : unitarySU ℓ f K 3} (hyQ : y ∈ Q) {α c0 c1 c2 : K}
    (hy : ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = circMat α c0 c1 c2)
    (hα0 : α ≠ 0) (hc0 : c0 ≠ 0) (hc1 : c1 ≠ 0) (hc2 : c2 ≠ 0)
    (hk : h.bar c0 * c0 ≠ 1) : Q = ⊤ := by
  have hcol0 : ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] =
      ![c0, c1, c2] := by
    rw [hy]
    exact (circ_column_facts α c0 c1 c2).1
  have hcol2 : ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 0, 1] =
      ![α * c1, α * c2, c0] := by
    rw [hy]
    exact (circ_column_facts α c0 c1 c2).2.2
  have hN0 := col_norm_sum h y ![1, 0, 0] (by simp)
  have hN2 := col_norm_sum h y ![0, 0, 1] (by simp)
  rw [hcol0] at hN0
  rw [hcol2] at hN2
  have hgw := exactA9_conj_mem h hyQ hE2
  have hgz := exactA9_conj_mem h hyQ hE0
  rw [hcol2] at hgw
  rw [hcol0] at hgz
  exact eq_top_of_columns h hq3 hℓ3 h17 hq ha hE0 hE1 hE2 (w := ![α * c1, α * c2, c0])
    hN2 (by simp [hα0, hc1]) (by simp [hα0, hc2]) hc0 hk hgw
    (z := ![c0, c1, c2]) hN0 hc0 hc1 hc2 hk hgz

theorem exactA9_case1 (h : UnitaryFieldData ℓ f K)
    (hq3 : 3 ∣ ℓ ^ f + 1) (hℓ3 : ℓ ≠ 3) (h17 : 17 ≤ ℓ ^ f) (hq : ℓ ^ f ≠ 2)
    {a : K} (ha : orderOf a = ℓ ^ f + 1) {α : K} (hNα : h.bar α * α = 1)
    {Q : Subgroup (unitarySU ℓ f K 3)}
    (hE0 : ∃ g ∈ Q, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      homMat h a (a⁻¹ ^ 2 - a) ![1, 0, 0])
    (hE1 : ∃ g ∈ Q, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      homMat h a (a⁻¹ ^ 2 - a) ![0, 1, 0])
    (hE2 : ∃ g ∈ Q, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      homMat h a (a⁻¹ ^ 2 - a) ![0, 0, 1])
    {y : unitarySU ℓ f K 3} (hyQ : y ∈ Q) {c0 c1 c2 : K}
    (hy : ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = circMat α c0 c1 c2)
    (hα0 : α ≠ 0) (hc0 : c0 ≠ 0) (hc1 : c1 ≠ 0) (hc2 : c2 ≠ 0)
    (hk : h.bar c1 * c1 ≠ 1) : Q = ⊤ := by
  have hcol1 : ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 1, 0] =
      ![α * c2, c0, c1] := by
    rw [hy]
    exact (circ_column_facts α c0 c1 c2).2.1
  have hcol2 : ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 0, 1] =
      ![α * c1, α * c2, c0] := by
    rw [hy]
    exact (circ_column_facts α c0 c1 c2).2.2
  have hN1 := col_norm_sum h y ![0, 1, 0] (by simp)
  have hN2 := col_norm_sum h y ![0, 0, 1] (by simp)
  rw [hcol1] at hN1
  rw [hcol2] at hN2
  have hgw := exactA9_conj_mem h hyQ hE1
  have hgz := exactA9_conj_mem h hyQ hE2
  rw [hcol1] at hgw
  rw [hcol2] at hgz
  have hn0 : h.bar (α * c1) * (α * c1) ≠ 1 := by
    rw [exactA9_norm_mul h hNα c1]
    exact hk
  exact eq_top_of_columns h hq3 hℓ3 h17 hq ha hE0 hE1 hE2 (w := ![α * c2, c0, c1])
    hN1 (by simp [hα0, hc2]) hc0 hc1 hk hgw (z := ![α * c1, α * c2, c0]) hN2
    (by simp [hα0, hc1]) (by simp [hα0, hc2]) hc0 hn0 hgz

theorem exactA9_case2 (h : UnitaryFieldData ℓ f K)
    (hq3 : 3 ∣ ℓ ^ f + 1) (hℓ3 : ℓ ≠ 3) (h17 : 17 ≤ ℓ ^ f) (hq : ℓ ^ f ≠ 2)
    {a : K} (ha : orderOf a = ℓ ^ f + 1) {α : K} (hNα : h.bar α * α = 1)
    {Q : Subgroup (unitarySU ℓ f K 3)}
    (hE0 : ∃ g ∈ Q, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      homMat h a (a⁻¹ ^ 2 - a) ![1, 0, 0])
    (hE1 : ∃ g ∈ Q, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      homMat h a (a⁻¹ ^ 2 - a) ![0, 1, 0])
    (hE2 : ∃ g ∈ Q, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      homMat h a (a⁻¹ ^ 2 - a) ![0, 0, 1])
    {y : unitarySU ℓ f K 3} (hyQ : y ∈ Q) {c0 c1 c2 : K}
    (hy : ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = circMat α c0 c1 c2)
    (hα0 : α ≠ 0) (hc0 : c0 ≠ 0) (hc1 : c1 ≠ 0) (hc2 : c2 ≠ 0)
    (hk : h.bar c2 * c2 ≠ 1) : Q = ⊤ := by
  have hcol0 : ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] =
      ![c0, c1, c2] := by
    rw [hy]
    exact (circ_column_facts α c0 c1 c2).1
  have hcol1 : ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 1, 0] =
      ![α * c2, c0, c1] := by
    rw [hy]
    exact (circ_column_facts α c0 c1 c2).2.1
  have hN0 := col_norm_sum h y ![1, 0, 0] (by simp)
  have hN1 := col_norm_sum h y ![0, 1, 0] (by simp)
  rw [hcol0] at hN0
  rw [hcol1] at hN1
  have hgw := exactA9_conj_mem h hyQ hE0
  have hgz := exactA9_conj_mem h hyQ hE1
  rw [hcol0] at hgw
  rw [hcol1] at hgz
  have hn0 : h.bar (α * c2) * (α * c2) ≠ 1 := by
    rw [exactA9_norm_mul h hNα c2]
    exact hk
  exact eq_top_of_columns h hq3 hℓ3 h17 hq ha hE0 hE1 hE2 (w := ![c0, c1, c2])
    hN0 hc0 hc1 hc2 hk hgw (z := ![α * c2, c0, c1]) hN1
    (by simp [hα0, hc2]) hc0 hc1 hn0 hgz

theorem exactClosure_eq_top_of_large (h : UnitaryFieldData ℓ f K)
    (hq3 : 3 ∣ ℓ ^ f + 1) (h17 : 17 ≤ ℓ ^ f) {w α : K} (hw : IsPrimitiveRoot w 3)
    (hαN : α ^ (ℓ ^ f + 1) = 1) (hnc : ¬ ∃ μ : K, μ ^ 3 = α) :
    Subgroup.closure (outerHeisExactFix ℓ f K w α) = ⊤ := by
  have hℓ3 : ℓ ≠ 3 := by
    rintro rfl
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · norm_num at hq3
    · have h3 : (3 : ℕ) ∣ 3 ^ f := dvd_pow_self 3 hf.ne'
      omega
  have hq : ℓ ^ f ≠ 2 := by omega
  obtain ⟨a, ha⟩ := exists_orderOf_eq h
  have hNα : h.bar α * α = 1 := by
    rw [bar_mul_self_eq_pow h α, hαN]
  have hα0 : α ≠ 0 := by
    rintro rfl
    simp at hNα
  obtain ⟨y, -, c0, c1, c2, hy, hc0, hc1, hc2, hnorm⟩ :=
    exists_generic_element h hq3 hq hw hαN hnc
  have hw3 : w ^ 3 = 1 := hw.pow_eq_one
  have hyQ : y ∈ Subgroup.closure (outerHeisExactFix ℓ f K w α) :=
    circ_mem_exactClosure hy
  have hE0 : ∃ g ∈ Subgroup.closure (outerHeisExactFix ℓ f K w α),
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        homMat h a (a⁻¹ ^ 2 - a) ![1, 0, 0] :=
    exactA9_coord_mem h hw3 ha (j := 0) (by ext i; fin_cases i <;> simp [Pi.single_apply])
  have hE1 : ∃ g ∈ Subgroup.closure (outerHeisExactFix ℓ f K w α),
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        homMat h a (a⁻¹ ^ 2 - a) ![0, 1, 0] :=
    exactA9_coord_mem h hw3 ha (j := 1) (by ext i; fin_cases i <;> simp [Pi.single_apply])
  have hE2 : ∃ g ∈ Subgroup.closure (outerHeisExactFix ℓ f K w α),
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        homMat h a (a⁻¹ ^ 2 - a) ![0, 0, 1] :=
    exactA9_coord_mem h hw3 ha (j := 2) (by ext i; fin_cases i <;> simp [Pi.single_apply])
  by_cases hk0 : h.bar c0 * c0 ≠ 1
  · exact exactA9_case0 h hq3 hℓ3 h17 hq ha hE0 hE1 hE2 hyQ hy hα0 hc0 hc1 hc2 hk0
  by_cases hk1 : h.bar c1 * c1 ≠ 1
  · exact exactA9_case1 h hq3 hℓ3 h17 hq ha hNα hE0 hE1 hE2 hyQ hy hα0 hc0 hc1 hc2 hk1
  by_cases hk2 : h.bar c2 * c2 ≠ 1
  · exact exactA9_case2 h hq3 hℓ3 h17 hq ha hNα hE0 hE1 hE2 hyQ hy hα0 hc0 hc1 hc2 hk2
  exact (hnorm ⟨not_not.1 hk0, not_not.1 hk1, not_not.1 hk2⟩).elim

end CFSG.RankThree.PartTwo.Sec19
