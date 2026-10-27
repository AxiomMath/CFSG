module

public import CFSG.RankThree.PartTwo.Sec21.Item223CensusProofOrders
public import CFSG.RankThree.PartTwo.Sec4.Item413Classical
import CFSG.Models.PGLOrders

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSp projImage sympForm)
open Matrix Polynomial

namespace Item223CensusResProof

noncomputable def palSextic (a b c : ZMod 2) : (ZMod 2)[X] :=
  X ^ 6 + C a * X ^ 5 + C b * X ^ 4 + C c * X ^ 3 + C b * X ^ 2 + C a * X + 1

theorem palSextic_bezout (a b c : ZMod 2) : ∃ u w : (ZMod 2)[X],
    X ^ 7 - 1 = u * palSextic a b c + w * (X ^ 21 - 1) ∨
      X ^ 3 - 1 = u * palSextic a b c + w * (X ^ 21 - 1) := by
  have h01 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases h01 a with rfl | rfl <;> rcases h01 b with rfl | rfl <;> rcases h01 c with rfl | rfl
  · exact ⟨X ^ 15 + X ^ 9 + X ^ 3, 1, Or.inr (by
      simp only [palSextic, map_zero]; ring_nf; reduce_mod_char)⟩
  · exact ⟨X ^ 18 + X ^ 16 + X ^ 15 + X ^ 13 + X ^ 9 + X ^ 7 + X ^ 6 + X ^ 4 + X + 1,
      X ^ 3 + X, Or.inl (by simp only [palSextic, map_zero, map_one]; ring_nf; reduce_mod_char)⟩
  · exact ⟨X ^ 19 + X ^ 16 + X ^ 15 + X ^ 14 + X ^ 11 + X ^ 8 + X ^ 7 + X ^ 6 + X ^ 3 + X + 1,
      X ^ 4 + X ^ 2 + X, Or.inl (by
        simp only [palSextic, map_zero, map_one]; ring_nf; reduce_mod_char)⟩
  · exact ⟨X ^ 17 + X ^ 16 + X ^ 12 + X ^ 11 + X ^ 7 + X ^ 6 + X ^ 2 + X, X ^ 2 + X + 1,
      Or.inr (by simp only [palSextic, map_zero, map_one]; ring_nf; reduce_mod_char)⟩
  · exact ⟨X ^ 19 + X ^ 17 + X ^ 16 + X ^ 15 + X ^ 13 + X ^ 9 + X ^ 7 + X ^ 6 + X ^ 5 + X ^ 3 +
      X + 1, X ^ 4 + X ^ 3 + X ^ 2, Or.inl (by
        simp only [palSextic, map_zero, map_one]; ring_nf; reduce_mod_char)⟩
  · exact ⟨X ^ 18 + X ^ 17 + X ^ 16 + X ^ 14 + X ^ 13 + X ^ 12 + X ^ 6 + X ^ 5 + X ^ 4 + X ^ 2 +
      X + 1, X ^ 3, Or.inr (by
        simp only [palSextic, map_zero, map_one]; ring_nf; reduce_mod_char)⟩
  · exact ⟨X ^ 17 + X ^ 13 + X ^ 9 + X ^ 5 + X, X ^ 2 + X + 1, Or.inr (by
      simp only [palSextic, map_zero, map_one]; ring_nf; reduce_mod_char)⟩
  · exact ⟨X + 1, 0, Or.inl (by
      simp only [palSextic, map_one]; ring_nf; reduce_mod_char)⟩

theorem charpoly_reverse_of_symplectic {n : ℕ}
    {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod 2)}
    (hM : Mᵀ * sympForm n (ZMod 2) * M = sympForm n (ZMod 2)) (hMu : IsUnit M) :
    M.charpoly.reverse = M.charpoly := by
  set J := sympForm n (ZMod 2) with hJdef
  have hJdet : IsUnit J.det := isUnit_iff_ne_zero.mpr (Sec4.det_sympForm_ne_zero n (ZMod 2))
  have hJ : IsUnit J := (Matrix.isUnit_iff_isUnit_det J).mpr hJdet
  have hdet : M.det = 1 := by
    have h0 : M.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det M).mp hMu).ne_zero
    have h01 : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
    exact h01 _ h0
  have hinv : M⁻¹ = J⁻¹ * Mᵀ * J := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Mᵀ, hM,
      Matrix.nonsing_inv_mul J hJdet]
  have h1 : M⁻¹.charpoly = M.charpoly := by
    rw [hinv]
    have h := Matrix.charpoly_units_conj' hJ.unit Mᵀ
    rw [IsUnit.unit_spec] at h
    rw [h, Matrix.charpoly_transpose]
  rw [Matrix.charpoly_inv M hMu, hdet, Ring.inverse_one, map_one, mul_one, Fintype.card_sum,
    Fintype.card_fin, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul,
    ← Matrix.reverse_charpoly] at h1
  exact h1

theorem charpoly_eq_palSextic {M : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)}
    (hM : Mᵀ * sympForm 3 (ZMod 2) * M = sympForm 3 (ZMod 2)) (hMu : IsUnit M) :
    M.charpoly = palSextic (M.charpoly.coeff 5) (M.charpoly.coeff 4) (M.charpoly.coeff 3) := by
  set χ := M.charpoly with hχ
  have hpal : χ.reverse = χ := charpoly_reverse_of_symplectic hM hMu
  have hdeg : χ.natDegree = 6 := by
    rw [hχ, Matrix.charpoly_natDegree_eq_dim, Fintype.card_sum, Fintype.card_fin]
  have hmon : χ.Monic := Matrix.charpoly_monic M
  have hrev : ∀ k, k ≤ 6 → χ.coeff k = χ.coeff (6 - k) := by
    intro k hk
    conv_lhs => rw [← hpal]
    rw [Polynomial.coeff_reverse, hdeg, Polynomial.revAt_le hk]
  have h6 : χ.coeff 6 = 1 := by
    have := hmon.coeff_natDegree
    rwa [hdeg] at this
  ext k
  simp only [palSextic, coeff_add, coeff_C_mul, coeff_X_pow, coeff_one, coeff_X]
  rcases Nat.lt_or_ge 6 k with hk | hk
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; exact hk)]
    have h1 : k ≠ 6 := by omega
    have h2 : k ≠ 5 := by omega
    have h3 : k ≠ 4 := by omega
    have h4 : k ≠ 3 := by omega
    have h5 : k ≠ 2 := by omega
    have h6' : (1 : ℕ) ≠ k := by omega
    have h7 : k ≠ 0 := by omega
    simp [h1, h2, h3, h4, h5, h6', h7]
  · interval_cases k
    · rw [hrev 0 (by norm_num)]
      simp [h6]
    · rw [hrev 1 (by norm_num)]
      simp
    · rw [hrev 2 (by norm_num)]
      simp
    · simp
    · simp
    · simp
    · simp [h6]

theorem pow_seven_or_pow_three_of_symplectic
    {M : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)}
    (hM : Mᵀ * sympForm 3 (ZMod 2) * M = sympForm 3 (ZMod 2)) (h21 : M ^ 21 = 1) :
    M ^ 7 = 1 ∨ M ^ 3 = 1 := by
  have hMu : IsUnit M := ⟨⟨M, M ^ 20, by rw [← pow_succ', h21], by rw [← pow_succ, h21]⟩, rfl⟩
  have hCH : aeval M (palSextic (M.charpoly.coeff 5) (M.charpoly.coeff 4)
      (M.charpoly.coeff 3)) = 0 := by
    rw [← charpoly_eq_palSextic hM hMu]
    exact Matrix.aeval_self_charpoly M
  have h21' : aeval M ((X : (ZMod 2)[X]) ^ 21 - 1) = 0 := by
    rw [map_sub, map_pow, aeval_X, map_one, h21]
    exact sub_self _
  obtain ⟨u, w, h | h⟩ := palSextic_bezout (M.charpoly.coeff 5) (M.charpoly.coeff 4)
    (M.charpoly.coeff 3)
  · left
    have h1 := congrArg (aeval M) h
    rw [map_add, map_mul, map_mul, hCH, h21', mul_zero, mul_zero, add_zero, map_sub, map_pow,
      aeval_X, map_one] at h1
    exact sub_eq_zero.mp h1
  · right
    have h1 := congrArg (aeval M) h
    rw [map_add, map_mul, map_mul, hCH, h21', mul_zero, mul_zero, add_zero, map_sub, map_pow,
      aeval_X, map_one] at h1
    exact sub_eq_zero.mp h1

theorem card_projSp_three_two : Nat.card (projSp 3 (GaloisField 2 1)) = 1451520 :=
  CFSG.PGLModel.card_projSp_three_two

theorem eq_three_of_dvd_1451520 {m : ℕ} (hm1 : 1 < m) (hmo : Odd m)
    (h : 3 * (2 ^ m - 1) ∣ 1451520) : m = 3 := by
  have hdvd : 2 ^ m - 1 ∣ 1451520 := (Dvd.intro_left 3 rfl).trans h
  by_contra hm3
  have hcheck : ∀ m < 22, 1 < m → Odd m → m ≠ 3 → ¬ 3 * (2 ^ m - 1) ∣ 1451520 := by decide
  by_cases hmb : m < 22
  · exact hcheck m hmb hm1 hmo hm3 h
  · have h1 : 2 ^ 22 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 := Nat.le_of_dvd (by norm_num) hdvd
    omega

theorem eq_one_of_mem_center_GF2 {ι : Type} [Fintype ι] [DecidableEq ι]
    {A : GL ι (GaloisField 2 1)} (hA : A ∈ Subgroup.center (GL ι (GaloisField 2 1))) : A = 1 := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hA
  obtain ⟨c, rfl⟩ := hA
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : c = 1 := by
    have hcard : Nat.card (GaloisField 2 1)ˣ = 1 := by
      rw [Nat.card_units, GaloisField.card 2 1 (by norm_num)]
      norm_num
    have : Subsingleton (GaloisField 2 1)ˣ := (Nat.card_eq_one_iff_unique.mp hcard).1
    exact Subsingleton.elim _ _
  rw [hc, map_one]

theorem pow_seven_or_pow_three_of_symplectic_GF2 {A : GL (Fin 3 ⊕ Fin 3) (GaloisField 2 1)}
    (hA : (A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (GaloisField 2 1))ᵀ *
      sympForm 3 (GaloisField 2 1) * A = sympForm 3 (GaloisField 2 1)) (h21 : A ^ 21 = 1) :
    A ^ 7 = 1 ∨ A ^ 3 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set e : GaloisField 2 1 ≃+* ZMod 2 := (GaloisField.equivZmodP 2).toRingEquiv
  set Φ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (GaloisField 2 1) ≃+*
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) := e.mapMatrix
  have hJ : Φ (sympForm 3 (GaloisField 2 1)) = sympForm 3 (ZMod 2) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> by_cases h : i = j <;>
      simp [Φ, sympForm, h]
  have hM : (Φ A)ᵀ * sympForm 3 (ZMod 2) * Φ A = sympForm 3 (ZMod 2) := by
    have h1 : (Φ (A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (GaloisField 2 1)))ᵀ =
        Φ ((A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (GaloisField 2 1))ᵀ) := by
      simp only [Φ, RingEquiv.mapMatrix_apply, Matrix.transpose_map]
    rw [← hJ, h1, ← map_mul, ← map_mul, hA]
  have h21' : Φ A ^ 21 = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, h21, Units.val_one, map_one]
  have hinj : ∀ k : ℕ, Φ A ^ k = 1 → A ^ k = 1 := by
    intro k hk
    apply Units.ext
    apply Φ.injective
    rw [Units.val_pow_eq_pow_val, map_pow, hk, Units.val_one, map_one]
  rcases pow_seven_or_pow_three_of_symplectic hM h21' with h | h
  · exact Or.inl (hinj 7 h)
  · exact Or.inr (hinj 3 h)

end Item223CensusResProof

open Item223CensusResProof

theorem census223Sp62Orders_holds : Census223Sp62Orders := by
  intro s m hm1 hmo hs
  have hdvd : 3 * (2 ^ m - 1) ∣ 1451520 := by
    rw [← hs, ← card_projSp_three_two]
    exact orderOf_dvd_natCard s
  obtain rfl := eq_three_of_dvd_1451520 hm1 hmo hdvd
  norm_num at hs
  obtain ⟨A, hA, hAs⟩ := s.2
  have hmk : ∀ k : ℕ, s ^ k = 1 ↔ A ^ k = 1 := by
    intro k
    rw [← OneMemClass.coe_eq_one, Subgroup.coe_pow, ← hAs, ← map_pow,
      Matrix.ProjGenLinGroup.mk_eq_one]
    exact ⟨eq_one_of_mem_center_GF2, fun h => h ▸ Subgroup.one_mem _⟩
  have h21 : A ^ 21 = 1 := (hmk 21).mp (hs ▸ pow_orderOf_eq_one s)
  have hform := Sec4.form_of_mem_closure hA
  rcases pow_seven_or_pow_three_of_symplectic_GF2 hform h21 with h | h
  · have := orderOf_dvd_of_pow_eq_one ((hmk 7).mpr h)
    rw [hs] at this
    norm_num at this
  · have := orderOf_dvd_of_pow_eq_one ((hmk 3).mpr h)
    rw [hs] at this
    norm_num at this

end CFSG.RankThree.PartTwo.Sec21
