module

public import CFSG.RankThree.PartTwo.KFacts.K72SLPiElems

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.RankThree.PartTwo.Sec4 CFSG.LocalAnalysis.ComponentInitial
open Matrix

section Matrices

variable {K : Type} [Field K]

theorem commute_of_mul_eq_mul_diagonal {n : ℕ} {W P Q Y Z : Matrix (Fin n) (Fin n) K}
    {d : Fin n → K} (hd : ∀ i j, i ≠ j → d i ≠ d j) (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (hWP : W * P = P * diagonal d) (hY : Y * W = W * Y) (hZ : Z * W = W * Z) :
    Y * Z = Z * Y := by
  have hQW : Q * W = diagonal d * Q := by
    calc Q * W = Q * W * (P * Q) := by rw [hPQ, Matrix.mul_one]
      _ = Q * (W * P) * Q := by simp only [Matrix.mul_assoc]
      _ = Q * P * diagonal d * Q := by rw [hWP]; simp only [Matrix.mul_assoc]
      _ = diagonal d * Q := by rw [hQP, Matrix.one_mul]
  have hdiag : ∀ {V : Matrix (Fin n) (Fin n) K}, V * W = W * V →
      Q * V * P = diagonal (fun i => (Q * V * P) i i) := by
    intro V hV
    have hc : Q * V * P * diagonal d = diagonal d * (Q * V * P) := by
      calc Q * V * P * diagonal d = Q * V * (W * P) := by
            rw [hWP]; simp only [Matrix.mul_assoc]
        _ = Q * (V * W) * P := by simp only [Matrix.mul_assoc]
        _ = Q * W * V * P := by rw [hV]; simp only [Matrix.mul_assoc]
        _ = diagonal d * (Q * V * P) := by rw [hQW]; simp only [Matrix.mul_assoc]
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [diagonal_apply_eq]
    · rw [entry_eq_zero_of_commute_diagonal hc (hd i j hij), diagonal_apply_ne _ hij]
  have hback : ∀ V : Matrix (Fin n) (Fin n) K, V = P * (Q * V * P) * Q := fun V => by
    calc V = (P * Q) * V * (P * Q) := by rw [hPQ, Matrix.one_mul, Matrix.mul_one]
      _ = P * (Q * V * P) * Q := by simp only [Matrix.mul_assoc]
  have hcomm : (Q * Y * P) * (Q * Z * P) = (Q * Z * P) * (Q * Y * P) := by
    rw [hdiag hY, hdiag hZ, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  calc Y * Z = P * (Q * Y * P) * Q * (P * (Q * Z * P) * Q) := by rw [← hback, ← hback]
    _ = P * ((Q * Y * P) * (Q * P) * (Q * Z * P)) * Q := by simp only [Matrix.mul_assoc]
    _ = P * ((Q * Z * P) * (Q * P) * (Q * Y * P)) * Q := by
        rw [hQP, Matrix.mul_one, Matrix.mul_one, hcomm]
    _ = P * (Q * Z * P) * Q * (P * (Q * Y * P) * Q) := by simp only [Matrix.mul_assoc]
    _ = Z * Y := by rw [← hback, ← hback]

theorem distinct_of_three_dvd_sum (k : Fin 3 → Fin 3)
    (h3 : ((k 0 : ℕ) + k 1 + k 2) % 3 = 0) (hk : ¬ (k 0 = k 1 ∧ k 1 = k 2)) :
    k 0 ≠ k 1 ∧ k 0 ≠ k 2 ∧ k 1 ≠ k 2 := by
  revert k
  decide

end Matrices

section Model

variable {π : Bool} {p f : ℕ} {K : Type} [Field K]

theorem commute_of_commute_slPi (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (h3 : (3 : K) ≠ 0) {w : slPi π 3 (p ^ f) K} (hw3 : w ^ 3 = 1)
    (hw : w ∉ Subgroup.center (slPi π 3 (p ^ f) K)) {y z : slPi π 3 (p ^ f) K}
    (hy : y * w = w * y) (hz : z * w = w * z) : y * z = z * y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  obtain ⟨τ, hτ3, hτ1⟩ := exists_tau hK hq
  have hcoe : ∀ s t : slPi π 3 (p ^ f) K, s * t = t * s →
      ((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * ((t : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = ((t : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := fun s t h => by
    rw [← Units.val_mul, ← Units.val_mul, ← Subgroup.coe_mul, ← Subgroup.coe_mul, h]
  set W : Matrix (Fin 3) (Fin 3) K := ((w : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hWdef
  have hW3 : W ^ 3 = 1 := by
    rw [hWdef, ← Units.val_pow_eq_pow_val, ← SubgroupClass.coe_pow, hw3]
    rfl
  obtain ⟨b, hb, hk⟩ := exists_eigenbasis hτ3 hτ1 h3 hW3
  choose k hk using hk
  set P := colMat b with hPdef
  have hP : IsUnit P := isUnit_colMat hb
  have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hWP : W * P = P * diagonal (fun i => τ ^ (k i : ℕ)) := mul_colMat_eq hk
  have hns : ¬ (k 0 = k 1 ∧ k 1 = k 2) := by
    rintro ⟨h01, h12⟩
    apply hw
    have hD : diagonal (fun i => τ ^ (k i : ℕ)) =
        τ ^ (k 0 : ℕ) • (1 : Matrix (Fin 3) (Fin 3) K) := by
      rw [Matrix.smul_one_eq_diagonal]
      congr 1
      funext i
      fin_cases i
      · rfl
      · simp [h01]
      · simp [h01, h12]
    have hWs : W = τ ^ (k 0 : ℕ) • (1 : Matrix (Fin 3) (Fin 3) K) := by
      have h1 : W * P = (τ ^ (k 0 : ℕ) • (1 : Matrix (Fin 3) (Fin 3) K)) * P := by
        rw [hWP, hD, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul]
      exact hP.mul_left_inj.mp h1
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, ← hWdef, hWs,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
  have hdet : τ ^ ((k 0 : ℕ) + k 1 + k 2) = 1 := by
    have h1 : W.det = 1 := ((mem_slPi_iff hπ).mp w.2).2
    have h2 := congrArg Matrix.det hWP
    rw [det_mul, det_mul, h1, one_mul, det_diagonal, Fin.prod_univ_three] at h2
    have h4 : P.det * 1 = P.det * (τ ^ (k 0 : ℕ) * τ ^ (k 1 : ℕ) * τ ^ (k 2 : ℕ)) := by
      rw [mul_one]
      exact h2
    rw [pow_add, pow_add]
    exact (hPdet.mul_left_cancel h4).symm
  have hord : orderOf τ = 3 := orderOf_eq_prime hτ3 hτ1
  have h3dvd : ((k 0 : ℕ) + k 1 + k 2) % 3 = 0 := by
    have h := orderOf_dvd_of_pow_eq_one hdet
    rw [hord] at h
    exact Nat.mod_eq_zero_of_dvd h
  obtain ⟨d01, d02, d12⟩ := distinct_of_three_dvd_sum k h3dvd hns
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    norm_num at hτ3
  set u : Kˣ := Units.mk0 τ hτ0 with hudef
  have hu3 : u ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hτ3,
    Units.val_one])
  have hu1 : u ≠ 1 := fun h => hτ1 (by rw [← Units.val_mk0 hτ0, ← hudef, h, Units.val_one])
  have hordu : orderOf u = 3 := orderOf_eq_prime hu3 hu1
  have hinj : ∀ a c : Fin 3, a ≠ c → τ ^ (a : ℕ) ≠ τ ^ (c : ℕ) := by
    intro a c hac h
    apply hac
    have h1 : u ^ (a : ℕ) = u ^ (c : ℕ) := Units.ext (by
      rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, Units.val_mk0]
      exact h)
    have h' := pow_inj_mod.mp h1
    rw [hordu, Nat.mod_eq_of_lt a.2, Nat.mod_eq_of_lt c.2] at h'
    exact Fin.ext h'
  have hd : ∀ i j : Fin 3, i ≠ j → τ ^ (k i : ℕ) ≠ τ ^ (k j : ℕ) := by
    intro i j hij
    apply hinj
    fin_cases i <;> fin_cases j
    all_goals first
      | exact absurd rfl hij
      | exact d01 | exact d02 | exact d12 | exact d01.symm | exact d02.symm | exact d12.symm
  have hYZ := commute_of_mul_eq_mul_diagonal hd (Matrix.mul_nonsing_inv P hPdet)
    (Matrix.nonsing_inv_mul P hPdet) hWP (hcoe y w hy) (hcoe z w hz)
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul]
  exact hYZ

end Model

theorem commute_of_mem_centralizer_of_isSLThreePiAt {X : Type} [Group X] [Finite X] {n : ℕ}
    (hn : 1 ≤ n) (hX : Sec4.IsSLThreePiAt X (2 ^ (3 * n))) {w : X} (hw3 : w ^ 3 = 1)
    (hw : w ∉ Subgroup.center X) {y z : X} (hy : y * w = w * y) (hz : z * w = w * z) :
    y * z = z * y := by
  obtain ⟨π, K, _, hK, hq, ⟨e⟩⟩ := exists_slPi_of_isSLThreePiAt hn hX
  have : CharP K 2 := hK.charP
  have h3 : (3 : K) ≠ 0 := by
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    intro h
    have h1 : (1 : K) = 0 := by linear_combination h - h2
    exact one_ne_zero h1
  have key := commute_of_commute_slPi hK hq h3 (w := e w) (by rw [← map_pow, hw3, map_one])
    (fun h => hw (by simpa using mem_center_of_mulEquiv e.symm h)) (y := e y) (z := e z)
    (by rw [← map_mul, hy, map_mul]) (by rw [← map_mul, hz, map_mul])
  apply e.injective
  rw [map_mul, map_mul, key]

end CFSG.RankThree.PartTwo.KFacts
