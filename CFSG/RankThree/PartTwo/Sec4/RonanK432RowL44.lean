module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Rows
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Transport
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Wreath
public import CFSG.RankThree.PartTwo.KFacts.KS21SylowL44
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Sylow

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.Item434Kit
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  (higher_linear_outer_order_divides_field_gcd_bound)
open Matrix

abbrev SL4 : Type := SpecialLinearGroup (Fin 4) (GaloisField 2 2)

noncomputable def zeta : GaloisField 2 2 :=
  ((KFacts.KS21.L44.exists_omega_data.choose : (GaloisField 2 2)ˣ) : GaloisField 2 2)

theorem zeta_spec : zeta ^ 3 = 1 ∧ zeta ^ 2 + zeta + 1 = 0 := by
  obtain ⟨-, h3, hq⟩ := KFacts.KS21.L44.exists_omega_data.choose_spec
  refine ⟨?_, hq⟩
  rw [zeta, ← Units.val_pow_eq_pow_val, h3, Units.val_one]

theorem zeta_ne_zero : zeta ≠ 0 := by
  intro h
  have h3 := zeta_spec.1
  rw [h] at h3
  norm_num at h3

theorem zeta_ne_one : zeta ≠ 1 := by
  intro h
  have hq := zeta_spec.2
  rw [h] at hq
  have h2 : (2 : GaloisField 2 2) = 0 := KFacts.KS21.L44.two_eq_zero
  have : (1 : GaloisField 2 2) = 0 := by linear_combination hq - h2
  exact one_ne_zero this

theorem zeta_sq_ne_one : zeta ^ 2 ≠ 1 := by
  intro h
  have hq := zeta_spec.2
  have h2 : (2 : GaloisField 2 2) = 0 := KFacts.KS21.L44.two_eq_zero
  exact zeta_ne_zero (by linear_combination hq - h - h2)

theorem zeta_pow_eq_zero {a : ℕ} (ha : a < 3) (h : zeta ^ a = 1) : a = 0 := by
  interval_cases a
  · rfl
  · rw [pow_one] at h
    exact absurd h zeta_ne_one
  · exact absurd h zeta_sq_ne_one

theorem zeta_mul_sq : zeta * zeta ^ 2 = 1 := by
  rw [← pow_succ', zeta_spec.1]

theorem zeta_sq_mul_sq : zeta ^ 2 * zeta ^ 2 = zeta := by
  linear_combination zeta * zeta_spec.1

theorem zeta_sq_mul_sq_mul_sq : zeta ^ 2 * zeta ^ 2 * zeta ^ 2 = 1 := by
  linear_combination (zeta ^ 3 + 1) * zeta_spec.1

theorem zeta_sq_cube : (zeta ^ 2) ^ 3 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, zeta_spec.1, one_pow]

@[expose] noncomputable def dz : Fin 3 → Fin 4 → GaloisField 2 2 :=
  ![![zeta, 1, 1, zeta ^ 2], ![1, zeta, 1, zeta ^ 2], ![1, 1, zeta, zeta ^ 2]]

theorem dz_cube (i : Fin 3) (k : Fin 4) : dz i k ^ 3 = 1 := by
  fin_cases i <;> fin_cases k <;> simp [dz, zeta_spec.1, zeta_sq_cube]

theorem prod_dz (i : Fin 3) : ∏ k, dz i k = 1 := by
  fin_cases i <;> simp [dz, Fin.prod_univ_four, zeta_mul_sq]

@[expose] noncomputable def zL (i : Fin 3) : SL4 :=
  ⟨Matrix.diagonal (dz i), by rw [Matrix.det_diagonal, prod_dz]⟩

theorem coe_zL (i : Fin 3) : ((zL i : SL4) : Matrix (Fin 4) (Fin 4) (GaloisField 2 2)) =
    Matrix.diagonal (dz i) := rfl

@[expose] def ρ : Equiv.Perm (Fin 4) := ⟨![2, 0, 1, 3], ![1, 2, 0, 3], by decide, by decide⟩

theorem ρ_cube : ρ * ρ * ρ = 1 := by decide

theorem sign_ρ : Equiv.Perm.sign ρ = 1 := by decide

@[expose] noncomputable def tL : SL4 :=
  ⟨ρ.permMatrix (GaloisField 2 2), by rw [Matrix.det_permutation, sign_ρ]; simp⟩

theorem coe_tL : ((tL : SL4) : Matrix (Fin 4) (Fin 4) (GaloisField 2 2)) =
    ρ.permMatrix (GaloisField 2 2) := rfl

@[expose] def sw : Equiv.Perm (Fin 4) := Equiv.swap 0 3

@[expose] noncomputable def mL : SL4 :=
  ⟨sw.permMatrix (GaloisField 2 2), by
    rw [Matrix.det_permutation, sw, Equiv.Perm.sign_swap (by decide)]
    simp [CharTwo.neg_eq]⟩

theorem coe_mL : ((mL : SL4) : Matrix (Fin 4) (Fin 4) (GaloisField 2 2)) =
    sw.permMatrix (GaloisField 2 2) := rfl

theorem t_mul_z0 : tL * zL 0 = zL 1 * tL := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun a b => ?_
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_tL, coe_zL]
  fin_cases a <;> fin_cases b <;>
    simp [dz, ρ, Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal_apply]

theorem t_mul_z1 : tL * zL 1 = zL 2 * tL := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun a b => ?_
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_tL, coe_zL]
  fin_cases a <;> fin_cases b <;>
    simp [dz, ρ, Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal_apply]

theorem t_mul_z2 : tL * zL 2 = zL 0 * tL := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun a b => ?_
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_tL, coe_zL]
  fin_cases a <;> fin_cases b <;>
    simp [dz, ρ, Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal_apply]

theorem coe_vecElt (v : Fin 3 → ZMod 3) :
    ((vecElt (zL) v : SL4) : Matrix (Fin 4) (Fin 4) (GaloisField 2 2)) =
      Matrix.diagonal fun k => dz 0 k ^ (v 0).val * dz 1 k ^ (v 1).val * dz 2 k ^ (v 2).val := by
  rw [vecElt, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_pow,
    Matrix.SpecialLinearGroup.coe_pow, coe_zL, coe_zL, coe_zL, Matrix.diagonal_pow,
    Matrix.diagonal_pow, Matrix.diagonal_pow, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  rfl

theorem wreathFacts_L4 : WreathFacts zL tL where
  pow_z i := by
    refine Matrix.SpecialLinearGroup.ext _ _ fun a b => ?_
    rw [Matrix.SpecialLinearGroup.coe_pow, coe_zL, Matrix.diagonal_pow,
      Matrix.SpecialLinearGroup.coe_one, ← Matrix.diagonal_one]
    congr 1
    funext k
    exact dz_cube i k
  comm_z i j := by
    refine Matrix.SpecialLinearGroup.ext _ _ fun a b => ?_
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_zL, coe_zL,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext k
    exact mul_comm _ _
  inj v hv := by
    have hmat : ((vecElt zL v : SL4) : Matrix (Fin 4) (Fin 4) (GaloisField 2 2)) = 1 := by
      rw [hv]
      rfl
    rw [coe_vecElt] at hmat
    have h0 := congrFun (congrFun hmat 0) 0
    have h1 := congrFun (congrFun hmat 1) 1
    have h2 := congrFun (congrFun hmat 2) 2
    simp [dz] at h0 h1 h2
    funext i
    fin_cases i
    · exact (ZMod.val_eq_zero _).mp (zeta_pow_eq_zero (ZMod.val_lt _) h0)
    · exact (ZMod.val_eq_zero _).mp (zeta_pow_eq_zero (ZMod.val_lt _) h1)
    · exact (ZMod.val_eq_zero _).mp (zeta_pow_eq_zero (ZMod.val_lt _) h2)
  pow_t := by
    refine Matrix.SpecialLinearGroup.ext _ _ fun a b => ?_
    rw [Matrix.SpecialLinearGroup.coe_pow, coe_tL, pow_three, ← Matrix.permMatrix_mul,
      ← Matrix.permMatrix_mul, ρ_cube, Matrix.permMatrix_one, Matrix.SpecialLinearGroup.coe_one]
  conj0 := by rw [t_mul_z0, mul_inv_cancel_right]
  conj1 := by rw [t_mul_z1, mul_inv_cancel_right]
  conj2 := by rw [t_mul_z2, mul_inv_cancel_right]
  t_ne v hv := by
    have h := congrFun (congrFun (congrArg
      (fun g : SL4 => ((g : SL4) : Matrix (Fin 4) (Fin 4) (GaloisField 2 2))) hv) 1) 0
    rw [coe_vecElt, Matrix.diagonal_apply_ne _ (by decide), coe_tL] at h
    simp [ρ] at h

theorem factorization_card_SL4 : (Nat.card SL4).factorization 3 = 4 := by
  rw [KFacts.KS21.L44.card_M_eq]
  exact Item434AltPerm.factorization_three_pow_mul 4 (by norm_num)

theorem card_wreathW_L4 : Nat.card (wreathW zL tL) = 81 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle := Item434AltPerm.card_le_of_isPGroup (isPGroup_wreathW wreathFacts_L4)
  rw [factorization_card_SL4] at hle
  have := le_card_wreathW wreathFacts_L4
  norm_num at hle
  omega

theorem not_243_dvd_SL4 : ¬ 243 ∣ Nat.card SL4 := by
  rw [KFacts.KS21.L44.card_M_eq]
  norm_num

theorem val_one_zmod3 : (1 : ZMod 3).val = 1 := rfl

theorem vecElt_one_one_one : vecElt zL ![1, 1, 1] = zL 0 * zL 1 * zL 2 := by
  simp [vecElt, val_one_zmod3]

theorem vecElt_zero_one_one : vecElt zL ![0, 1, 1] = zL 1 * zL 2 := by
  simp [vecElt, val_one_zmod3]

theorem mL_mul_c : mL * (zL 0 * zL 1 * zL 2) = zL 1 * zL 2 * mL := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun a b => ?_
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_mL, coe_zL, Matrix.mul_diagonal,
    Matrix.diagonal_mul, Matrix.diagonal_mul_diagonal]
  fin_cases a <;> fin_cases b <;>
    simp [sw, dz, Matrix.diagonal_apply, Equiv.swap_apply_def, zeta_sq_mul_sq,
      zeta_sq_mul_sq_mul_sq, zeta_mul_sq]

theorem vecElt_not_mem_zpowers {H : Type} [Group H] {z : Fin 3 → H} {t : H}
    (hf : WreathFacts z t) {v : Fin 3 → ZMod 3} (hv : ¬ (v 0 = v 1 ∧ v 1 = v 2)) :
    vecElt z v ∉ Subgroup.zpowers (vecElt z ![1, 1, 1]) := by
  intro hmem
  have hc3 : (vecElt z ![1, 1, 1]) ^ 3 = 1 :=
    (isElemAbelian_baseA hf).2 _ (vecElt_mem_baseA hf _)
  have key : ∀ x y : ZMod 3, x + 1 = 0 → y + 1 = 0 → x = y := by decide
  rcases mem_zpowers_cases_of_pow_three hc3 hmem with h | h | h
  · have hv0 := hf.inj v h
    subst hv0
    exact hv ⟨rfl, rfl⟩
  · have hv1 := vecElt_injective hf h
    subst hv1
    exact hv ⟨rfl, rfl⟩
  · have h1 : vecElt z (v + ![1, 1, 1]) = 1 := by
      rw [vecElt_add hf, h, inv_mul_cancel]
    have h2 := hf.inj _ h1
    have e0 := congrFun h2 0
    have e1 := congrFun h2 1
    have e2 := congrFun h2 2
    simp only [Pi.add_apply, Pi.zero_apply] at e0 e1 e2
    exact hv ⟨key _ _ (by simpa using e0) (by simpa using e1),
      key _ _ (by simpa using e1) (by simpa using e2)⟩

theorem flip_L4 : ∃ m : SL4, m * vecElt zL ![1, 1, 1] * m⁻¹ ∈ baseA zL ∧
    m * vecElt zL ![1, 1, 1] * m⁻¹ ∉ Subgroup.zpowers (vecElt zL ![1, 1, 1]) := by
  refine ⟨mL, ?_⟩
  have hconj : mL * vecElt zL ![1, 1, 1] * mL⁻¹ = vecElt zL ![0, 1, 1] := by
    rw [vecElt_one_one_one, mL_mul_c, mul_inv_cancel_right, vecElt_zero_one_one]
  rw [hconj]
  exact ⟨vecElt_mem_baseA wreathFacts_L4 _,
    vecElt_not_mem_zpowers wreathFacts_L4 (by decide)⟩

theorem listRow_SL4 : ListRow SL4 :=
  listRow_of_wreath3 wreathFacts_L4 card_wreathW_L4 not_243_dvd_SL4 flip_L4

theorem listRow_projSL4 : ListRow (projSL 4 (GaloisField 2 2)) :=
  ListRow.of_mulEquiv KFacts.KS21.L44.equivSL.symm listRow_SL4

theorem not_three_dvd_card_outer_projSL4 :
    ¬ 3 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      (projSL 4 (GaloisField 2 2))) := by
  intro h3
  have hd := higher_linear_outer_order_divides_field_gcd_bound (k := GaloisField 2 2) (p := 2)
    (f := 2) (n := 4) Nat.prime_two (by norm_num) (by norm_num) (GaloisField.card 2 2 (by norm_num))
  rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
    (projSLEquivProjectiveSL 4 (GaloisField 2 2))).toEquiv] at h3
  norm_num at hd
  have := h3.trans hd
  norm_num at this

theorem outerRow_projSL4 : OuterRow (projSL 4 (GaloisField 2 2)) :=
  outerRow_of_not_three_dvd_outer not_three_dvd_card_outer_projSL4

theorem row_l44 : RowOf (projSL 4 (GaloisField 2 2)) := by
  intro S _ _ _ _ ⟨e⟩
  haveI : Finite (projSL 4 (GaloisField 2 2)) := Finite.of_equiv S e.toEquiv
  exact GoodRow.of_mulEquiv (S := projSL 4 (GaloisField 2 2)) e.symm
    ⟨listRow_projSL4, outerRow_projSL4⟩

end CFSG.RankThree.PartTwo.Sec4.RonanK432
