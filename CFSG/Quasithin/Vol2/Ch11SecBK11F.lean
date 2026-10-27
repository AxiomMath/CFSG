module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LieType.Universal.Unitary.Basic
public import CFSG.RankThree.SubgroupLists.SL3Involutions

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA.BK11

open CFSG.Assembly.LowTwoRank
open CFSG.RankThree.SubgroupLists (negDiag3 coe_negDiag3)
open CFSG.LieType.Universal.Unitary (conjTr conjTr_mul)

variable {K : Type} [Field K]

theorem det_conj (P t : GL (Fin 3) K) :
    ((P⁻¹ * t * P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det =
      (t : Matrix (Fin 3) (Fin 3) K).det := by
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc,
    ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, one_mul]

theorem scalars_le_center (H : Subgroup (GL (Fin 3) K)) :
    (StatedScalars (Fin 3) K).subgroupOf H ≤ Subgroup.center ↥H := by
  intro z hz
  rw [Subgroup.mem_subgroupOf, StatedScalars,
    ← Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (Subgroup.mem_center_iff.mp hz g)

theorem scalars_pow_three {H : Subgroup (GL (Fin 3) K)}
    (hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) K).det = 1) :
    ∀ z ∈ (StatedScalars (Fin 3) K).subgroupOf H, z ^ 3 = 1 := by
  intro z hz
  rw [Subgroup.mem_subgroupOf] at hz
  obtain ⟨u, hu⟩ := hz
  have hd := hdet _ z.2
  rw [← hu, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
    Fin.prod_const] at hd
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, ← hu, Matrix.GeneralLinearGroup.coe_scalar,
    ← map_pow, hd, map_one]
  rfl

theorem eq_one_or_neg_one_of_pow {l : K} {k : ℕ} (h6 : l ^ 6 = 1) (hk : l ^ 2 ^ k = 1) :
    l = 1 ∨ l = -1 := by
  have h2 : orderOf l ∣ 2 := by
    obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
    have h6' := orderOf_dvd_of_pow_eq_one h6
    rw [hjeq] at h6' ⊢
    have hj1 : j ≤ 1 := by
      by_contra h
      have h4 : 2 ^ 2 ∣ 6 := (Nat.pow_dvd_pow 2 (by omega)).trans h6'
      norm_num at h4
    exact (Nat.pow_dvd_pow 2 hj1).trans (by norm_num)
  have hsq : l * l = 1 := by
    rw [← sq]
    exact orderOf_dvd_iff_pow_eq_one.mp h2
  exact mul_self_eq_one_iff.mp hsq

theorem conjTr_gram (σ : K ≃+* K) {P t : GL (Fin 3) K}
    (ht : conjTr σ (t : Matrix (Fin 3) (Fin 3) K) * (t : Matrix (Fin 3) (Fin 3) K) = 1) :
    conjTr σ ((P⁻¹ * t * P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (conjTr σ (P : Matrix (Fin 3) (Fin 3) K) * P) *
          ((P⁻¹ * t * P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      conjTr σ (P : Matrix (Fin 3) (Fin 3) K) * P := by
  have hPD : (P : Matrix (Fin 3) (Fin 3) K) *
      ((P⁻¹ * t * P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        (t : Matrix (Fin 3) (Fin 3) K) * P := by
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    group
  calc conjTr σ ((P⁻¹ * t * P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (conjTr σ (P : Matrix (Fin 3) (Fin 3) K) * P) *
          ((P⁻¹ * t * P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      conjTr σ ((P : Matrix (Fin 3) (Fin 3) K) *
          ((P⁻¹ * t * P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) *
        ((P : Matrix (Fin 3) (Fin 3) K) *
          ((P⁻¹ * t * P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
        rw [conjTr_mul]
        simp only [Matrix.mul_assoc]
    _ = conjTr σ (P : Matrix (Fin 3) (Fin 3) K) *
          (conjTr σ (t : Matrix (Fin 3) (Fin 3) K) * (t : Matrix (Fin 3) (Fin 3) K)) * P := by
        rw [hPD, conjTr_mul]
        simp only [Matrix.mul_assoc]
    _ = conjTr σ (P : Matrix (Fin 3) (Fin 3) K) * P := by rw [ht, Matrix.mul_one]

theorem conjTr_diagonal_mul_apply (σ : K ≃+* K) (a b : Fin 3 → K) (G : Matrix (Fin 3) (Fin 3) K)
    (i j : Fin 3) :
    (conjTr σ (Matrix.diagonal a) * G * Matrix.diagonal b) i j = σ (a i) * G i j * b j := by
  rw [conjTr, Matrix.diagonal_map (map_zero σ), Matrix.diagonal_transpose, Matrix.mul_diagonal,
    Matrix.diagonal_mul]

theorem sigma_mul_eq_one (h2 : (2 : K) ≠ 0) (σ : K ≃+* K) {z t P : GL (Fin 3) K} {l m : K}
    (hz : conjTr σ (z : Matrix (Fin 3) (Fin 3) K) * (z : Matrix (Fin 3) (Fin 3) K) = 1)
    (ht : conjTr σ (t : Matrix (Fin 3) (Fin 3) K) * (t : Matrix (Fin 3) (Fin 3) K) = 1)
    (hP : P⁻¹ * z * P = negDiag3 K)
    (hD : ((P⁻¹ * t * P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal ![l, l, m]) :
    σ l * l = 1 := by
  set G := conjTr σ (P : Matrix (Fin 3) (Fin 3) K) * P with hG
  have hGz := conjTr_gram σ (P := P) hz
  have hGt := conjTr_gram σ (P := P) ht
  rw [hP, coe_negDiag3] at hGz
  rw [hD] at hGt
  have hdet : G.det ≠ 0 := by
    have hmap : ((P : Matrix (Fin 3) (Fin 3) K).map σ).det = σ (P : Matrix (Fin 3) (Fin 3) K).det :=
      (RingHom.map_det (σ : K →+* K) _).symm
    rw [hG, Matrix.det_mul, conjTr, Matrix.det_transpose, hmap]
    have hPd : (P : Matrix (Fin 3) (Fin 3) K).det ≠ 0 := by
      have h := congrArg Matrix.det (congrArg Units.val (mul_inv_cancel P))
      rw [Units.val_mul, Matrix.det_mul, Units.val_one, Matrix.det_one] at h
      exact left_ne_zero_of_mul_eq_one h
    exact mul_ne_zero ((map_ne_zero σ).mpr hPd) hPd
  have e02 := congrFun (congrFun hGz 0) 2
  rw [conjTr_diagonal_mul_apply] at e02
  simp only [Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    map_neg, map_one, mul_one] at e02
  have hG02 : G 0 2 = 0 := by
    have : (2 : K) * G 0 2 = 0 := by linear_combination -e02
    exact (mul_eq_zero.mp this).resolve_left h2
  have e00 := congrFun (congrFun hGt 0) 0
  have e01 := congrFun (congrFun hGt 0) 1
  rw [conjTr_diagonal_mul_apply] at e00 e01
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e00 e01
  by_cases h0 : G 0 0 = 0
  · by_cases h1 : G 0 1 = 0
    · exfalso
      apply hdet
      refine Matrix.det_eq_zero_of_row_eq_zero 0 fun j => ?_
      fin_cases j
      · exact h0
      · exact h1
      · exact hG02
    · have : (σ l * l - 1) * G 0 1 = 0 := by linear_combination e01
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right h1)
  · have : (σ l * l - 1) * G 0 0 = 0 := by linear_combination e00
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right h0)

end CFSG.Quasithin.Vol2.Ch11.SecA.BK11
