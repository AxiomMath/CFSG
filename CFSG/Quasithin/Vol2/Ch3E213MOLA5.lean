module

public import CFSG.ClassicalInvolution.AschTight.S19KLinStd

public section

namespace CFSG.Quasithin.Ch3E213M.OLA

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Models.Transfer
  CFSG.ClassicalInvolution.Disconnected.AschTight.S19K
open scoped MatrixGroups

theorem isScalar_of_commute_two {F : Type*} [Field F] {Y A B : Matrix (Fin 2) (Fin 2) F}
    (hA : Y * A = A * Y) (hB : Y * B = B * Y) (hAB : A * B ≠ B * A) :
    Y 0 1 = 0 ∧ Y 1 0 = 0 ∧ Y 0 0 = Y 1 1 := by
  have e := fun i j => congrFun (congrFun hA i) j
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at e
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have hspan : ∀ α β : F, A 0 0 = α + β * Y 0 0 → A 0 1 = β * Y 0 1 → A 1 0 = β * Y 1 0 →
      A 1 1 = α + β * Y 1 1 → False := by
    intro α β h00 h01 h10 h11
    apply hAB
    have hA' : A = α • 1 + β • Y := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11]
    rw [hA', add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
      Matrix.smul_mul, Matrix.mul_smul, hB]
  by_contra hns
  by_cases hb : Y 0 1 = 0
  · by_cases hc : Y 1 0 = 0
    · have hd : Y 0 0 - Y 1 1 ≠ 0 := fun h => hns ⟨hb, hc, sub_eq_zero.mp h⟩
      rw [hb] at e01
      rw [hc] at e10
      refine hspan (A 0 0 - (A 0 0 - A 1 1) / (Y 0 0 - Y 1 1) * Y 0 0)
        ((A 0 0 - A 1 1) / (Y 0 0 - Y 1 1)) (by ring) ?_ ?_ ?_
      · rw [hb, mul_zero]
        have h1 : A 0 1 * (Y 0 0 - Y 1 1) = 0 := by linear_combination e01
        exact (mul_eq_zero.mp h1).resolve_right hd
      · rw [hc, mul_zero]
        have h1 : A 1 0 * (Y 0 0 - Y 1 1) = 0 := by linear_combination -e10
        exact (mul_eq_zero.mp h1).resolve_right hd
      · field_simp
        ring
    · rw [hb] at e00
      refine hspan (A 0 0 - A 1 0 / Y 1 0 * Y 0 0) (A 1 0 / Y 1 0) (by ring) ?_ ?_ ?_
      · rw [hb, mul_zero]
        have h1 : A 0 1 * Y 1 0 = 0 := by linear_combination -e00
        exact (mul_eq_zero.mp h1).resolve_right hc
      · field_simp
      · field_simp
        linear_combination -e10
  · refine hspan (A 0 0 - A 0 1 / Y 0 1 * Y 0 0) (A 0 1 / Y 0 1) (by ring) ?_ ?_ ?_
    · field_simp
    · field_simp
      linear_combination e00
    · field_simp
      linear_combination e01

theorem sq_eq_one_of_pow {M : Type*} [Monoid M] {ν : M} {k m : ℕ} (hk : ν ^ 2 ^ k = 1)
    (hm : ν ^ (2 * m) = 1) (hmodd : Odd m) : ν ^ 2 = 1 := by
  have h1 : (ν ^ 2) ^ 2 ^ k = 1 := by rw [← pow_mul, mul_comm, pow_mul, hk, one_pow]
  have h2 : (ν ^ 2) ^ m = 1 := by rw [← pow_mul, hm]
  have hcop : Nat.Coprime (2 ^ k) m := Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hmodd)
  have h3 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
  rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h3
  exact h3

theorem mem_of_pow_three_mem {G : Type*} [Group G] {H : Subgroup G} {c : G} {k : ℕ}
    (hk : c ^ 2 ^ k = 1) (h3 : c ^ 3 ∈ H) : c ∈ H := by
  have hcop : Nat.Coprime 3 (orderOf c) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hk)
      (Nat.Coprime.pow_right k (by norm_num))
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hm]
  exact H.pow_mem h3 m

theorem center_pow_three_sl3 {F : Type} [Field F] :
    ∀ c ∈ Subgroup.center SL(3, F), c ^ 3 = 1 := by
  intro c hc
  obtain ⟨r, hr, hc'⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  rw [Fintype.card_fin] at hr
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, ← hc', ← map_pow, hr, map_one,
    Matrix.SpecialLinearGroup.coe_one]

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K]

theorem lin_centralizer_two (hq : Nat.card F % 4 = 3) (h4 : 4 ≤ Nat.card F)
    (θ : SL(3, F) →* K) (hθ : Function.Surjective θ) (hker : θ.ker ≤ Subgroup.center SL(3, F)) :
    ∀ c ∈ Subgroup.centralizer
      (((Models.rootSL2 F (n := 3) (by norm_num)).map θ : Subgroup K) : Set K), ∀ k : ℕ,
      c ^ 2 ^ k = 1 → c ∈ Subgroup.zpowers (θ (Models.rootInv F (n := 3) (by norm_num))) := by
  intro c hc k hk
  have hodd : Odd (Nat.card F) := Nat.odd_iff.mpr (by omega)
  have h2 : (2 : F) ≠ 0 := Models.two_ne_zero_of_odd_natCard hodd
  have : Group.IsPerfect (Models.rootSL2 F (n := 3) (by norm_num)) :=
    (Models.isClassicalSL2_rootSL2 (K := F) h2 (by norm_num : 2 ≤ 3)).isPerfect h4
  obtain ⟨x, rfl⟩ := hθ c
  have hx := mem_centralizer_of_map hker Subgroup.commutator_eq_self hc
  obtain ⟨h01, h02, h10, h12, h20, h21, h0011⟩ := isBlockScalar_of_mem_centralizer hx
  set X := ((x : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) with hX
  have hXd : X = Matrix.diagonal ![X 0 0, X 0 0, X 2 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h01, h02, h10, h12, h20, h21, ← h0011]
  have hpow : ∀ n : ℕ, ((x ^ n : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      Matrix.diagonal ![X 0 0 ^ n, X 0 0 ^ n, X 2 2 ^ n] := by
    intro n
    rw [Matrix.SpecialLinearGroup.coe_pow, ← hX, hXd, Matrix.diagonal_pow]
    congr 1
    ext i
    fin_cases i <;> rfl
  have hdet : X 0 0 * X 0 0 * X 2 2 = 1 := by
    have h1 := x.2
    rw [← hX, hXd, Matrix.det_diagonal, Fin.prod_univ_three] at h1
    simpa [mul_assoc] using h1
  have hl0 : X 0 0 ≠ 0 := fun h => by
    rw [h] at hdet
    simp at hdet
  have hk' : x ^ 2 ^ k ∈ θ.ker := by rw [MonoidHom.mem_ker, map_pow, hk]
  obtain ⟨r, hr3, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp (hker hk')
  rw [Fintype.card_fin] at hr3
  have hlk : X 0 0 ^ 2 ^ k = r := by
    have h1 := congrFun (congrFun (hpow (2 ^ k)) 0) 0
    rw [← hr] at h1
    simpa [Matrix.scalar_apply] using h1.symm
  have hνk : (X 0 0 ^ 3) ^ 2 ^ k = 1 := by rw [← pow_mul, mul_comm, pow_mul, hlk, hr3]
  have hνq : (X 0 0 ^ 3) ^ (2 * ((Nat.card F - 1) / 2)) = 1 := by
    have := Fintype.ofFinite F
    have h1 := FiniteField.pow_card_sub_one_eq_one (X 0 0 ^ 3) (pow_ne_zero 3 hl0)
    rw [← Nat.card_eq_fintype_card] at h1
    rwa [show 2 * ((Nat.card F - 1) / 2) = Nat.card F - 1 by omega]
  have hν2 := sq_eq_one_of_pow hνk hνq (Nat.odd_iff.mpr (by omega))
  have hμ3 : X 2 2 ^ 3 = 1 := by
    have h1 : (X 0 0 * X 0 0 * X 2 2) ^ 3 = (X 0 0 ^ 3) ^ 2 * X 2 2 ^ 3 := by ring
    rw [hdet, one_pow, hν2, one_mul] at h1
    exact h1.symm
  have h3 : θ x ^ 3 ∈ Subgroup.zpowers (θ (Models.rootInv F (n := 3) (by norm_num))) := by
    have h1 : (X 0 0 ^ 3 - 1) * (X 0 0 ^ 3 + 1) = 0 := by linear_combination hν2
    rw [← map_pow]
    rcases mul_eq_zero.mp h1 with h | h
    · have hx3 : x ^ 3 = 1 := by
        apply Subtype.ext
        rw [hpow, sub_eq_zero.mp h, hμ3, Matrix.SpecialLinearGroup.coe_one]
        ext i j
        fin_cases i <;> fin_cases j <;> simp
      rw [hx3, map_one]
      exact Subgroup.one_mem _
    · have hx3 : x ^ 3 = Models.rootInv F (n := 3) (by norm_num) := by
        apply Subtype.ext
        rw [hpow, eq_neg_of_add_eq_zero_left h, hμ3, coe_rootInv_three]
        ext i j
        fin_cases i <;> fin_cases j <;> simp
      rw [hx3]
      exact Subgroup.mem_zpowers _
  exact mem_of_pow_three_mem hk h3

end CFSG.Quasithin.Ch3E213M.OLA
