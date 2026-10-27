module

public import CFSG.RankThree.PartOne.KGD.D4A2Frame
public import CFSG.RankThree.Chevalley.SteinbergBID4RootSL2Shape
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.PartOne.SEITZ7.D4Swap

public noncomputable section

namespace CFSG.RankThree.PartOne.D4RC

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KGD CFSG.RankThree.PartOne.SEITZ7 Matrix
open scoped MatrixGroups

variable {L : Type} [Field L]

abbrev rsE0 : Fin Tag.D4.rank → ℤ := Pi.single 0 1
abbrev rsE2 : Fin Tag.D4.rank → ℤ := Pi.single 2 1

@[expose] def rsLie (N : Matrix (Fin 3) (Fin 3) L) : RootModule Tag.D4 L :=
  N 0 1 • rootVec Tag.D4 L rsE0 + N 1 0 • rootVec Tag.D4 L (-rsE0) +
    N 1 2 • rootVec Tag.D4 L rsE2 + N 2 1 • rootVec Tag.D4 L (-rsE2) +
    N 0 2 • rootVec Tag.D4 L (rsE0 + rsE2) + N 2 0 • rootVec Tag.D4 L (-(rsE0 + rsE2)) +
    N 0 0 • hVec Tag.D4 L 2 + N 1 1 • (hVec Tag.D4 L 0 + hVec Tag.D4 L 2) +
    N 2 2 • hVec Tag.D4 L 0

theorem rsLie_single01 : rsLie (Matrix.single 0 1 (1 : L)) = rootVec Tag.D4 L rsE0 := by
  simp [rsLie]

theorem rs_isRoot_iff (v : Fin Tag.D4.rank → ℤ) :
    IsRoot Tag.D4 v ↔ ∃ k : Fin 24, d4RootVec k = v :=
  isRoot_iff_exists_d4RootVec

theorem rs_root_e02 : IsRoot Tag.D4 (rsE0 + rsE2) :=
  (rs_isRoot_iff _).2 (by decide)

theorem rs_root_ne02 : IsRoot Tag.D4 (-(rsE0 + rsE2)) :=
  (rs_isRoot_iff _).2 (by decide)

theorem rs_not_root {v : Fin Tag.D4.rank → ℤ} (h : ∀ k : Fin 24, d4RootVec k ≠ v) :
    rootVec Tag.D4 L v = 0 :=
  rootVec_eq_zero_of_not_D4 fun hv => by
    obtain ⟨k, hk⟩ := (rs_isRoot_iff v).1 hv
    exact h k hk

section CharTwo

variable [CharP L 2]

theorem rs_two : (2 : L) = 0 := CharTwo.two_eq_zero

theorem rsLie_x0 (c : L) (N : Matrix (Fin 3) (Fin 3) L) :
    xOp Tag.D4 L 0 c (rsLie N) =
      rsLie ((1 + Matrix.single 0 1 c) * N * (1 + Matrix.single 0 1 c)) := by
  have h1 : xOp Tag.D4 L 0 c (rootVec Tag.D4 L rsE0) = rootVec Tag.D4 L rsE0 :=
    xOp_rootVec_single_D4 0 c
  have h2 : xOp Tag.D4 L 0 c (rootVec Tag.D4 L (-rsE0)) = rootVec Tag.D4 L (-rsE0) +
      c • hVec Tag.D4 L 0 + c ^ 2 • rootVec Tag.D4 L rsE0 := xOp_rootVec_neg_single_D4 0 c
  have h3 : xOp Tag.D4 L 0 c (rootVec Tag.D4 L rsE2) = rootVec Tag.D4 L rsE2 +
      c • rootVec Tag.D4 L (rsE0 + rsE2) := by
    rw [xOp_rootVec_D4 0 c (isRoot_single _ 2) (by decide) (by decide), add_comm rsE2]
  have h4 : xOp Tag.D4 L 0 c (rootVec Tag.D4 L (-rsE2)) = rootVec Tag.D4 L (-rsE2) := by
    rw [xOp_rootVec_D4 0 c (isRoot_neg_single _ 2) (by decide) (by decide),
      rs_not_root (v := -rsE2 + Pi.single 0 1) (by decide), smul_zero, add_zero]
  have h5 : xOp Tag.D4 L 0 c (rootVec Tag.D4 L (rsE0 + rsE2)) =
      rootVec Tag.D4 L (rsE0 + rsE2) := by
    rw [xOp_rootVec_D4 0 c rs_root_e02 (by decide) (by decide),
      rs_not_root (v := rsE0 + rsE2 + Pi.single 0 1) (by decide), smul_zero, add_zero]
  have h6 : xOp Tag.D4 L 0 c (rootVec Tag.D4 L (-(rsE0 + rsE2))) =
      rootVec Tag.D4 L (-(rsE0 + rsE2)) + c • rootVec Tag.D4 L (-rsE2) := by
    rw [xOp_rootVec_D4 0 c rs_root_ne02 (by decide) (by decide)]
    congr 3
    decide
  have h7 : xOp Tag.D4 L 0 c (hVec Tag.D4 L 2) = hVec Tag.D4 L 2 + c • rootVec Tag.D4 L rsE0 := by
    have hc : (Tag.D4.cartan 2 0).natAbs = 1 := by decide
    rw [xOp_hVec_D4, hc, Nat.cast_one, one_mul]
  have h8 : xOp Tag.D4 L 0 c (hVec Tag.D4 L 0) = hVec Tag.D4 L 0 := by
    have hc : (Tag.D4.cartan 0 0).natAbs = 2 := by decide
    rw [xOp_hVec_D4, hc, Nat.cast_ofNat, rs_two, zero_mul, zero_smul, add_zero]
  simp only [rsLie, map_add, map_smul, h1, h2, h3, h4, h5, h6, h7, h8]
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply]
  simp
  match_scalars <;> first | ring1 | (ring_nf; simp [rs_two])

theorem rsLie_y0 (c : L) (N : Matrix (Fin 3) (Fin 3) L) :
    yOp Tag.D4 L 0 c (rsLie N) =
      rsLie ((1 + Matrix.single 1 0 c) * N * (1 + Matrix.single 1 0 c)) := by
  have h1 : yOp Tag.D4 L 0 c (rootVec Tag.D4 L rsE0) = rootVec Tag.D4 L rsE0 +
      c • hVec Tag.D4 L 0 + c ^ 2 • rootVec Tag.D4 L (-rsE0) := yOp_rootVec_single_D4 0 c
  have h2 : yOp Tag.D4 L 0 c (rootVec Tag.D4 L (-rsE0)) = rootVec Tag.D4 L (-rsE0) :=
    yOp_rootVec_neg_single_D4 0 c
  have h3 : yOp Tag.D4 L 0 c (rootVec Tag.D4 L rsE2) = rootVec Tag.D4 L rsE2 := by
    rw [yOp_rootVec_D4 0 c (isRoot_single _ 2) (by decide) (by decide),
      rs_not_root (v := rsE2 - Pi.single 0 1) (by decide), smul_zero, add_zero]
  have h4 : yOp Tag.D4 L 0 c (rootVec Tag.D4 L (-rsE2)) = rootVec Tag.D4 L (-rsE2) +
      c • rootVec Tag.D4 L (-(rsE0 + rsE2)) := by
    rw [yOp_rootVec_D4 0 c (isRoot_neg_single _ 2) (by decide) (by decide)]
    congr 3
    decide
  have h5 : yOp Tag.D4 L 0 c (rootVec Tag.D4 L (rsE0 + rsE2)) =
      rootVec Tag.D4 L (rsE0 + rsE2) + c • rootVec Tag.D4 L rsE2 := by
    rw [yOp_rootVec_D4 0 c rs_root_e02 (by decide) (by decide)]
    congr 3
    decide
  have h6 : yOp Tag.D4 L 0 c (rootVec Tag.D4 L (-(rsE0 + rsE2))) =
      rootVec Tag.D4 L (-(rsE0 + rsE2)) := by
    rw [yOp_rootVec_D4 0 c rs_root_ne02 (by decide) (by decide),
      rs_not_root (v := -(rsE0 + rsE2) - Pi.single 0 1) (by decide), smul_zero, add_zero]
  have h7 : yOp Tag.D4 L 0 c (hVec Tag.D4 L 2) =
      hVec Tag.D4 L 2 + c • rootVec Tag.D4 L (-rsE0) := by
    have hc : (Tag.D4.cartan 2 0).natAbs = 1 := by decide
    rw [yOp_hVec_D4, hc, Nat.cast_one, one_mul]
  have h8 : yOp Tag.D4 L 0 c (hVec Tag.D4 L 0) = hVec Tag.D4 L 0 := by
    have hc : (Tag.D4.cartan 0 0).natAbs = 2 := by decide
    rw [yOp_hVec_D4, hc, Nat.cast_ofNat, rs_two, zero_mul, zero_smul, add_zero]
  simp only [rsLie, map_add, map_smul, h1, h2, h3, h4, h5, h6, h7, h8]
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply]
  simp
  match_scalars <;> first | ring1 | (ring_nf; simp [rs_two])

theorem rsLie_x2 (c : L) (N : Matrix (Fin 3) (Fin 3) L) :
    xOp Tag.D4 L 2 c (rsLie N) =
      rsLie ((1 + Matrix.single 1 2 c) * N * (1 + Matrix.single 1 2 c)) := by
  have h1 : xOp Tag.D4 L 2 c (rootVec Tag.D4 L rsE0) = rootVec Tag.D4 L rsE0 +
      c • rootVec Tag.D4 L (rsE0 + rsE2) := by
    rw [xOp_rootVec_D4 2 c (isRoot_single _ 0) (by decide) (by decide)]
  have h2 : xOp Tag.D4 L 2 c (rootVec Tag.D4 L (-rsE0)) = rootVec Tag.D4 L (-rsE0) := by
    rw [xOp_rootVec_D4 2 c (isRoot_neg_single _ 0) (by decide) (by decide),
      rs_not_root (v := -rsE0 + Pi.single 2 1) (by decide), smul_zero, add_zero]
  have h3 : xOp Tag.D4 L 2 c (rootVec Tag.D4 L rsE2) = rootVec Tag.D4 L rsE2 :=
    xOp_rootVec_single_D4 2 c
  have h4 : xOp Tag.D4 L 2 c (rootVec Tag.D4 L (-rsE2)) = rootVec Tag.D4 L (-rsE2) +
      c • hVec Tag.D4 L 2 + c ^ 2 • rootVec Tag.D4 L rsE2 := xOp_rootVec_neg_single_D4 2 c
  have h5 : xOp Tag.D4 L 2 c (rootVec Tag.D4 L (rsE0 + rsE2)) =
      rootVec Tag.D4 L (rsE0 + rsE2) := by
    rw [xOp_rootVec_D4 2 c rs_root_e02 (by decide) (by decide),
      rs_not_root (v := rsE0 + rsE2 + Pi.single 2 1) (by decide), smul_zero, add_zero]
  have h6 : xOp Tag.D4 L 2 c (rootVec Tag.D4 L (-(rsE0 + rsE2))) =
      rootVec Tag.D4 L (-(rsE0 + rsE2)) + c • rootVec Tag.D4 L (-rsE0) := by
    rw [xOp_rootVec_D4 2 c rs_root_ne02 (by decide) (by decide)]
    congr 3
    decide
  have h7 : xOp Tag.D4 L 2 c (hVec Tag.D4 L 2) = hVec Tag.D4 L 2 := by
    have hc : (Tag.D4.cartan 2 2).natAbs = 2 := by decide
    rw [xOp_hVec_D4, hc, Nat.cast_ofNat, rs_two, zero_mul, zero_smul, add_zero]
  have h8 : xOp Tag.D4 L 2 c (hVec Tag.D4 L 0) = hVec Tag.D4 L 0 + c • rootVec Tag.D4 L rsE2 := by
    have hc : (Tag.D4.cartan 0 2).natAbs = 1 := by decide
    rw [xOp_hVec_D4, hc, Nat.cast_one, one_mul]
  simp only [rsLie, map_add, map_smul, h1, h2, h3, h4, h5, h6, h7, h8]
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply]
  simp
  match_scalars <;> first | ring1 | (ring_nf; simp [rs_two])

theorem rsLie_y2 (c : L) (N : Matrix (Fin 3) (Fin 3) L) :
    yOp Tag.D4 L 2 c (rsLie N) =
      rsLie ((1 + Matrix.single 2 1 c) * N * (1 + Matrix.single 2 1 c)) := by
  have h1 : yOp Tag.D4 L 2 c (rootVec Tag.D4 L rsE0) = rootVec Tag.D4 L rsE0 := by
    rw [yOp_rootVec_D4 2 c (isRoot_single _ 0) (by decide) (by decide),
      rs_not_root (v := rsE0 - Pi.single 2 1) (by decide), smul_zero, add_zero]
  have h2 : yOp Tag.D4 L 2 c (rootVec Tag.D4 L (-rsE0)) = rootVec Tag.D4 L (-rsE0) +
      c • rootVec Tag.D4 L (-(rsE0 + rsE2)) := by
    rw [yOp_rootVec_D4 2 c (isRoot_neg_single _ 0) (by decide) (by decide)]
    congr 3
    decide
  have h3 : yOp Tag.D4 L 2 c (rootVec Tag.D4 L rsE2) = rootVec Tag.D4 L rsE2 +
      c • hVec Tag.D4 L 2 + c ^ 2 • rootVec Tag.D4 L (-rsE2) := yOp_rootVec_single_D4 2 c
  have h4 : yOp Tag.D4 L 2 c (rootVec Tag.D4 L (-rsE2)) = rootVec Tag.D4 L (-rsE2) :=
    yOp_rootVec_neg_single_D4 2 c
  have h5 : yOp Tag.D4 L 2 c (rootVec Tag.D4 L (rsE0 + rsE2)) =
      rootVec Tag.D4 L (rsE0 + rsE2) + c • rootVec Tag.D4 L rsE0 := by
    rw [yOp_rootVec_D4 2 c rs_root_e02 (by decide) (by decide)]
    congr 3
    decide
  have h6 : yOp Tag.D4 L 2 c (rootVec Tag.D4 L (-(rsE0 + rsE2))) =
      rootVec Tag.D4 L (-(rsE0 + rsE2)) := by
    rw [yOp_rootVec_D4 2 c rs_root_ne02 (by decide) (by decide),
      rs_not_root (v := -(rsE0 + rsE2) - Pi.single 2 1) (by decide), smul_zero, add_zero]
  have h7 : yOp Tag.D4 L 2 c (hVec Tag.D4 L 2) = hVec Tag.D4 L 2 := by
    have hc : (Tag.D4.cartan 2 2).natAbs = 2 := by decide
    rw [yOp_hVec_D4, hc, Nat.cast_ofNat, rs_two, zero_mul, zero_smul, add_zero]
  have h8 : yOp Tag.D4 L 2 c (hVec Tag.D4 L 0) =
      hVec Tag.D4 L 0 + c • rootVec Tag.D4 L (-rsE2) := by
    have hc : (Tag.D4.cartan 0 2).natAbs = 1 := by decide
    rw [yOp_hVec_D4, hc, Nat.cast_one, one_mul]
  simp only [rsLie, map_add, map_smul, h1, h2, h3, h4, h5, h6, h7, h8]
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply]
  simp
  match_scalars <;> first | ring1 | (ring_nf; simp [rs_two])

theorem rs_inv_transvection {a b : Fin 3} (hab : a ≠ b) (c : L) :
    (1 + Matrix.single a b c)⁻¹ = 1 + Matrix.single a b c := by
  refine Matrix.inv_eq_right_inv ?_
  have hss : Matrix.single a b c * Matrix.single a b c = 0 :=
    Matrix.single_mul_single_of_ne c a b a hab.symm c
  rw [add_mul, one_mul, mul_add, mul_one, hss, add_zero, add_assoc, CharTwo.add_self_eq_zero,
    add_zero]

omit [CharP L 2] in
theorem rs_unit_neg {i : Fin Tag.D4.rank} (c : L) :
    (xUnit Tag.D4 L i c)⁻¹ = xUnit Tag.D4 L i (-c) ∧
      (yUnit Tag.D4 L i c)⁻¹ = yUnit Tag.D4 L i (-c) :=
  ⟨Units.ext (coe_xUnit_inv i c), Units.ext (coe_yUnit_inv i c)⟩

theorem rsLie_gen {i : Fin Tag.D4.rank} (hi : i ∈ d4SuppA2) (c : L) (N : Matrix (Fin 3) (Fin 3) L) :
    ((xUnit Tag.D4 L i c : ModGL Tag.D4 L) : Module.End L (RootModule Tag.D4 L)) (rsLie N) =
        rsLie (d4A2Mat (xUnit Tag.D4 L i c) * N * (d4A2Mat (xUnit Tag.D4 L i c))⁻¹) ∧
      ((yUnit Tag.D4 L i c : ModGL Tag.D4 L) : Module.End L (RootModule Tag.D4 L)) (rsLie N) =
        rsLie (d4A2Mat (yUnit Tag.D4 L i c) * N * (d4A2Mat (yUnit Tag.D4 L i c))⁻¹) := by
  rcases (mem_d4SuppA2 i).1 hi with rfl | rfl
  · rw [coe_xUnit, coe_yUnit, d4A2Mat_x0, d4A2Mat_y0, rs_inv_transvection (by decide),
      rs_inv_transvection (by decide)]
    exact ⟨rsLie_x0 c N, rsLie_y0 c N⟩
  · rw [coe_xUnit, coe_yUnit, d4A2Mat_x2, d4A2Mat_y2, rs_inv_transvection (by decide),
      rs_inv_transvection (by decide)]
    exact ⟨rsLie_x2 c N, rsLie_y2 c N⟩

theorem rsLie_conj_of_mem {g : ModGL Tag.D4 L} (hg : g ∈ subsystemGroup Tag.D4 L d4SuppA2) :
    ∀ N : Matrix (Fin 3) (Fin 3) L, (g : Module.End L (RootModule Tag.D4 L)) (rsLie N) =
      rsLie (d4A2Mat g * N * (d4A2Mat g)⁻¹) := by
  induction hg using Subgroup.closure_induction'' with
  | mem g hg =>
    obtain ⟨i, hi, c, rfl | rfl⟩ := hg
    · exact fun N => (rsLie_gen hi c N).1
    · exact fun N => (rsLie_gen hi c N).2
  | inv_mem g hg =>
    obtain ⟨i, hi, c, rfl | rfl⟩ := hg
    · rw [(rs_unit_neg c).1]
      exact fun N => (rsLie_gen hi (-c) N).1
    · rw [(rs_unit_neg c).2]
      exact fun N => (rsLie_gen hi (-c) N).2
  | one =>
    intro N
    rw [d4A2Mat_one, inv_one, mul_one, one_mul, Units.val_one, Module.End.one_apply]
  | mul g h hg hh ihg ihh =>
    intro N
    rw [Units.val_mul, Module.End.mul_apply, ihh, ihg, d4A2Mat_mul hh, Matrix.mul_inv_rev]
    simp only [Matrix.mul_assoc]

theorem rsLie_conj (M : SL(3, L)) (N : Matrix (Fin 3) (Fin 3) L) :
    ((d4rhoStd L M : ModGL Tag.D4 L) : Module.End L (RootModule Tag.D4 L)) (rsLie N) =
      rsLie ((M : Matrix (Fin 3) (Fin 3) L) * N * (M : Matrix (Fin 3) (Fin 3) L)⁻¹) := by
  rw [rsLie_conj_of_mem (d4rhoStd_mem M) N, d4A2Mat_d4rhoStd]

theorem rsLie_rootVec (M : SL(3, L)) :
    ((d4rhoStd L M : ModGL Tag.D4 L) : Module.End L (RootModule Tag.D4 L))
        (rootVec Tag.D4 L rsE0) =
      rsLie ((M : Matrix (Fin 3) (Fin 3) L) * Matrix.single 0 1 1 *
        (M : Matrix (Fin 3) (Fin 3) L)⁻¹) := by
  rw [← rsLie_single01, rsLie_conj]

end CharTwo

end CFSG.RankThree.PartOne.D4RC
