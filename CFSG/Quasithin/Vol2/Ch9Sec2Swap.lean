module

public import CFSG.Quasithin.Vol2.Ch9Lem926
public import CFSG.Quasithin.Vol2.Ch9FactsFrob

public section

namespace CFSG.Quasithin.H.Om4

open Matrix

variable {K : Type} [Field K]

theorem exists_smul_of_lr_eq_one {R S : GL (Fin 2) K} (h : lr R S = 1) :
    ∃ c : K, c ≠ 0 ∧ (R : Matrix (Fin 2) (Fin 2) K) = c • 1 ∧
      (S : Matrix (Fin 2) (Fin 2) K) = c⁻¹ • 1 := by
  have key : ∀ X : Matrix (Fin 2) (Fin 2) K,
      (R : Matrix (Fin 2) (Fin 2) K) * X * (S : Matrix (Fin 2) (Fin 2) K)ᵀ = X := fun X => by
    have := congrArg (fun f : MulAut (VM K) => Multiplicative.toAdd (f (Multiplicative.ofAdd X))) h
    simpa only [toAdd_lr, MulAut.one_apply, toAdd_ofAdd] using this
  have e1 := key !![1, 0; 0, 0]
  have e2 := key !![0, 0; 0, 1]
  have e3 := key !![0, 1; 0, 0]
  have a00 := congrFun (congrFun e1 0) 0
  have a10 := congrFun (congrFun e1 1) 0
  have a01 := congrFun (congrFun e1 0) 1
  have b11 := congrFun (congrFun e2 1) 1
  have b01 := congrFun (congrFun e2 0) 1
  have b10 := congrFun (congrFun e2 1) 0
  have c01 := congrFun (congrFun e3 0) 1
  rw [mul_mul_transpose_entry] at a00 a10 a01 b11 b01 b10 c01
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, mul_zero, zero_mul, add_zero, zero_add,
    one_mul] at a00 a10 a01 b11 b01 b10 c01
  set R' := (R : Matrix (Fin 2) (Fin 2) K)
  set S' := (S : Matrix (Fin 2) (Fin 2) K)
  have hR00 : R' 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one a00
  have hS00 : S' 0 0 ≠ 0 := right_ne_zero_of_mul_eq_one a00
  have hR11 : R' 1 1 ≠ 0 := left_ne_zero_of_mul_eq_one b11
  have hS11 : S' 1 1 ≠ 0 := right_ne_zero_of_mul_eq_one b11
  have hR10 : R' 1 0 = 0 := (mul_eq_zero.mp a10).resolve_right hS00
  have hS10 : S' 1 0 = 0 := (mul_eq_zero.mp a01).resolve_left hR00
  have hR01 : R' 0 1 = 0 := (mul_eq_zero.mp b01).resolve_right hS11
  have hS01 : S' 0 1 = 0 := (mul_eq_zero.mp b10).resolve_left hR11
  have hS : S' 0 0 = S' 1 1 := mul_left_cancel₀ hR00 (a00.trans c01.symm)
  have hR : R' 1 1 = R' 0 0 := mul_right_cancel₀ hS11 (b11.trans c01.symm)
  have hinv : S' 0 0 = (R' 0 0)⁻¹ := eq_inv_of_mul_eq_one_right a00
  refine ⟨R' 0 0, hR00, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [hR10, hR01, hR]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [hS10, hS01, ← hS, hinv]

theorem exists_smul_of_lr_eq {P Q P' Q' : GL (Fin 2) K} (h : lr P Q = lr P' Q') :
    ∃ c : K, c ≠ 0 ∧ (P' : Matrix (Fin 2) (Fin 2) K) = c • (P : Matrix (Fin 2) (Fin 2) K) ∧
      (Q' : Matrix (Fin 2) (Fin 2) K) = c⁻¹ • (Q : Matrix (Fin 2) (Fin 2) K) := by
  have h1 : lr (P⁻¹ * P') (Q⁻¹ * Q') = 1 := by
    rw [← lr_mul, ← lr_inv, h, inv_mul_cancel]
  obtain ⟨c, hc, hR, hS⟩ := exists_smul_of_lr_eq_one h1
  refine ⟨c, hc, ?_, ?_⟩
  · have : (P' : Matrix (Fin 2) (Fin 2) K) = (P : Matrix (Fin 2) (Fin 2) K) *
        ((P⁻¹ * P' : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
      rw [← Units.val_mul, mul_inv_cancel_left]
    rw [this, hR, Matrix.mul_smul, Matrix.mul_one]
  · have : (Q' : Matrix (Fin 2) (Fin 2) K) = (Q : Matrix (Fin 2) (Fin 2) K) *
        ((Q⁻¹ * Q' : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
      rw [← Units.val_mul, mul_inv_cancel_left]
    rw [this, hS, Matrix.mul_smul, Matrix.mul_one]

theorem eq_of_rho_eq_lr [CharP K 2]
    {γ : SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K} {P Q : GL (Fin 2) K}
    (hP : (P : Matrix (Fin 2) (Fin 2) K).det = 1) (h : rho γ = lr P Q) :
    (P : Matrix (Fin 2) (Fin 2) K) = γ.1 ∧ (Q : Matrix (Fin 2) (Fin 2) K) = γ.2 := by
  rw [rho_apply] at h
  obtain ⟨c, -, h1, h2⟩ := exists_smul_of_lr_eq h
  have hdet := congrArg Matrix.det h1
  rw [Matrix.det_smul, hP, Fintype.card_fin] at hdet
  have hdet' : ((Matrix.SpecialLinearGroup.toGL γ.1 : GL (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K).det = 1 := γ.1.2
  rw [hdet', mul_one] at hdet
  have hc1 : c = 1 := by
    have h22 : (2 : K) = 0 := CharTwo.two_eq_zero
    have : (c - 1) ^ 2 = 0 := by linear_combination -hdet + (1 - c) * h22
    exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp this)
  rw [hc1, one_smul] at h1
  rw [hc1, inv_one, one_smul] at h2
  exact ⟨h1, h2⟩

theorem det_conj_map (A : GL (Fin 2) K) (τ : K ≃+* K) (g : SpecialLinearGroup (Fin 2) K) :
    ((A * GeneralLinearGroup.map τ.toRingHom (Matrix.SpecialLinearGroup.toGL g) * A⁻¹ :
      GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 := by
  rw [Units.val_mul, Units.val_mul, Matrix.det_units_conj]
  show (τ.toRingHom.mapMatrix (g : Matrix (Fin 2) (Fin 2) K)).det = 1
  rw [← RingHom.map_det, g.2, map_one]

theorem conj_isNS (X Y A B : GL (Fin 2) K) (τ : K ≃+* K) :
    (lr X Y * frM τ) * lr A B * (lr X Y * frM τ)⁻¹ =
      lr (X * GeneralLinearGroup.map τ.toRingHom A * X⁻¹)
        (Y * GeneralLinearGroup.map τ.toRingHom B * Y⁻¹) := by
  have e1 : lr (X * GeneralLinearGroup.map τ.toRingHom A * X⁻¹)
      (Y * GeneralLinearGroup.map τ.toRingHom B * Y⁻¹) * lr X Y =
      lr (X * GeneralLinearGroup.map τ.toRingHom A) (Y * GeneralLinearGroup.map τ.toRingHom B) := by
    rw [lr_mul, inv_mul_cancel_right, inv_mul_cancel_right]
  rw [mul_inv_eq_iff_eq_mul]
  calc lr X Y * frM τ * lr A B = lr X Y * (frM τ * lr A B) := by rw [mul_assoc]
    _ = lr X Y * (lr (GeneralLinearGroup.map τ.toRingHom A)
          (GeneralLinearGroup.map τ.toRingHom B) * frM τ) := by rw [frM_lr]
    _ = lr (X * GeneralLinearGroup.map τ.toRingHom A)
          (Y * GeneralLinearGroup.map τ.toRingHom B) * frM τ := by rw [← mul_assoc, lr_mul]
    _ = _ := by rw [← e1, mul_assoc]

theorem conj_swap (X Y A B : GL (Fin 2) K) (τ : K ≃+* K) :
    (lr X Y * frM τ * trM) * lr A B * (lr X Y * frM τ * trM)⁻¹ =
      lr (X * GeneralLinearGroup.map τ.toRingHom B * X⁻¹)
        (Y * GeneralLinearGroup.map τ.toRingHom A * Y⁻¹) := by
  have e1 : lr (X * GeneralLinearGroup.map τ.toRingHom B * X⁻¹)
      (Y * GeneralLinearGroup.map τ.toRingHom A * Y⁻¹) * lr X Y =
      lr (X * GeneralLinearGroup.map τ.toRingHom B) (Y * GeneralLinearGroup.map τ.toRingHom A) := by
    rw [lr_mul, inv_mul_cancel_right, inv_mul_cancel_right]
  rw [mul_inv_eq_iff_eq_mul]
  calc lr X Y * frM τ * trM * lr A B = lr X Y * (frM τ * lr B A) * trM := by
        rw [mul_assoc _ trM, trM_lr]; simp only [mul_assoc]
    _ = lr X Y * (lr (GeneralLinearGroup.map τ.toRingHom B)
          (GeneralLinearGroup.map τ.toRingHom A) * frM τ) * trM := by rw [frM_lr]
    _ = lr (X * GeneralLinearGroup.map τ.toRingHom B)
          (Y * GeneralLinearGroup.map τ.toRingHom A) * frM τ * trM := by
        rw [← mul_assoc (lr X Y), lr_mul]
    _ = _ := by rw [← e1]; simp only [mul_assoc]

theorem IsUT.mul_apply_zero_zero {A B : GL (Fin 2) K} (hB : IsUT B) :
    ((A * B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 =
      (A : Matrix (Fin 2) (Fin 2) K) 0 0 * (B : Matrix (Fin 2) (Fin 2) K) 0 0 := by
  unfold IsUT at hB
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hB, mul_zero, add_zero]

theorem IsUT.mul_apply_one_one {A B : GL (Fin 2) K} (hA : IsUT A) :
    ((A * B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 =
      (A : Matrix (Fin 2) (Fin 2) K) 1 1 * (B : Matrix (Fin 2) (Fin 2) K) 1 1 := by
  unfold IsUT at hA
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hA, zero_mul, zero_add]

theorem IsUT.inv {A : GL (Fin 2) K} (hA : IsUT A) : IsUT A⁻¹ ∧
    ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 =
      ((A : Matrix (Fin 2) (Fin 2) K) 0 0)⁻¹ ∧
    ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 =
      ((A : Matrix (Fin 2) (Fin 2) K) 1 1)⁻¹ := by
  obtain ⟨-, h1⟩ := hA.apply_ne_zero
  have hAA : (A : Matrix (Fin 2) (Fin 2) K) * ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have e10 := congrFun (congrFun hAA 1) 0
  have e00 := congrFun (congrFun hAA 0) 0
  have e11 := congrFun (congrFun hAA 1) 1
  unfold IsUT at hA
  simp only [Matrix.mul_apply, Fin.sum_univ_two, hA, zero_mul, zero_add, Matrix.one_apply_ne
    (show (1 : Fin 2) ≠ 0 by decide), Matrix.one_apply_eq] at e10 e00 e11
  have hB10 : ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 :=
    (mul_eq_zero.mp e10).resolve_left h1
  rw [hB10, mul_zero, add_zero] at e00
  exact ⟨hB10, eq_inv_of_mul_eq_one_right e00, eq_inv_of_mul_eq_one_right e11⟩

theorem map_apply' (τ : K ≃+* K) (A : GL (Fin 2) K) (i j : Fin 2) :
    ((GeneralLinearGroup.map τ.toRingHom A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j =
      τ ((A : Matrix (Fin 2) (Fin 2) K) i j) := rfl

theorem conj_map_apply {X A : GL (Fin 2) K} (hX : IsUT X) (hA : IsUT A) (τ : K ≃+* K) :
    ((X * GeneralLinearGroup.map τ.toRingHom A * X⁻¹ : GL (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) 0 0 = τ ((A : Matrix (Fin 2) (Fin 2) K) 0 0) ∧
    ((X * GeneralLinearGroup.map τ.toRingHom A * X⁻¹ : GL (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) 1 1 = τ ((A : Matrix (Fin 2) (Fin 2) K) 1 1) := by
  obtain ⟨hXi, hXi0, hXi1⟩ := hX.inv
  obtain ⟨h0, h1⟩ := hX.apply_ne_zero
  have hAτ := hA.map τ
  refine ⟨?_, ?_⟩
  · rw [hXi.mul_apply_zero_zero, hAτ.mul_apply_zero_zero, map_apply', hXi0, mul_right_comm,
      mul_inv_cancel₀ h0, one_mul]
  · rw [(hX.mul hAτ).mul_apply_one_one, hX.mul_apply_one_one, map_apply', hXi1, mul_right_comm,
      mul_inv_cancel₀ h1, one_mul]

end CFSG.Quasithin.H.Om4

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H Matrix

theorem le_two_of_dvd_add {n a b : ℕ} (ha : a < n) (hb : b < n)
    (h : 2 ^ n - 1 ∣ 2 ^ a + 2 ^ b) : n ≤ 2 := by
  by_contra hn2
  have hn3 : 3 ≤ n := by omega
  have h8 : 8 ≤ 2 ^ n := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
  have hA : 2 ^ a ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hB : 2 ^ b ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hn1 : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h4 : 4 ≤ 2 ^ (n - 1) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨c, hc⟩ := h
  have hpos : 0 < 2 ^ a + 2 ^ b := by positivity
  have hc1 : c = 1 := by
    rcases Nat.lt_or_ge c 2 with h2 | h2
    · interval_cases c
      · rw [mul_zero] at hc
        omega
      · rfl
    · have : (2 ^ n - 1) * 2 ≤ (2 ^ n - 1) * c := Nat.mul_le_mul_left _ h2
      omega
  rw [hc1, mul_one] at hc
  have key : ∀ x y : ℕ, y < n → 2 ^ x + 2 ^ y = 2 ^ n - 1 → x = 0 → False := by
    intro x y hy hxy hx0
    subst hx0
    rw [pow_zero] at hxy
    rcases Nat.eq_zero_or_pos y with hy0 | hy0
    · rw [hy0, pow_zero] at hxy
      omega
    · have h2y : 2 ^ y = 2 * 2 ^ (y - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      have hyn : 2 ^ (y - 1) = 2 ^ (n - 1) - 1 := by omega
      have h3 : Odd (2 ^ (n - 1) - 1) := Nat.Even.sub_odd Nat.one_le_two_pow
        (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
      rw [← hyn] at h3
      have hy1 : y - 1 = 0 := by
        by_contra h0
        exact (Nat.not_even_iff_odd.mpr h3) (Nat.even_pow.mpr ⟨even_two, h0⟩)
      rw [hy1, pow_zero] at hyn
      omega
  rcases Nat.eq_zero_or_pos a with ha0 | ha0
  · exact key a b hb hc ha0
  · rcases Nat.eq_zero_or_pos b with hb0 | hb0
    · exact key b a ha (by rw [add_comm]; exact hc) hb0
    · have hodd : Odd (2 ^ a + 2 ^ b) := by
        rw [hc]
        exact Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
      have he : Even (2 ^ a + 2 ^ b) :=
        (Nat.even_pow.mpr ⟨even_two, by omega⟩).add (Nat.even_pow.mpr ⟨even_two, by omega⟩)
      exact (Nat.not_even_iff_odd.mpr hodd) he

theorem pow_two_pow_mod {K : Type} [Field K] [Fintype K] {n : ℕ} (hK : Fintype.card K = 2 ^ n)
    (x : K) (i : ℕ) : x ^ 2 ^ i = x ^ 2 ^ (i % n) := by
  have hfix : ∀ y : K, y ^ 2 ^ n = y := fun y => by rw [← hK]; exact FiniteField.pow_card y
  have key : ∀ q : ℕ, ∀ y : K, y ^ 2 ^ (n * q) = y := by
    intro q
    induction q with
    | zero => intro y; simp
    | succ q ih => intro y; rw [Nat.mul_succ, pow_add, pow_mul y (2 ^ (n * q)) (2 ^ n), ih, hfix]
  calc x ^ 2 ^ i = x ^ 2 ^ (n * (i / n) + i % n) := by rw [Nat.div_add_mod]
    _ = (x ^ 2 ^ (n * (i / n))) ^ 2 ^ (i % n) := by
      rw [pow_add, pow_mul x (2 ^ (n * (i / n))) (2 ^ (i % n))]
    _ = x ^ 2 ^ (i % n) := by rw [key]

theorem exists_frob_pow_lt {K : Type} [Field K] [Fintype K] [CharP K 2] {n : ℕ}
    (hn : 1 ≤ n) (hK : Fintype.card K = 2 ^ n) (τ : K ≃+* K) :
    ∃ j < n, ∀ x : K, τ x = x ^ 2 ^ j := by
  obtain ⟨i, hi⟩ := FactsFrob.exists_frob_pow τ
  exact ⟨i % n, Nat.mod_lt _ (by omega), fun x => by rw [hi, pow_two_pow_mod hK]⟩

theorem map_u1 {K : Type} [Field K] (τ : K ≃+* K) :
    ((GeneralLinearGroup.map τ.toRingHom (Matrix.SpecialLinearGroup.toGL (u1 K)) :
      GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = (u1 K : Matrix (Fin 2) (Fin 2) K) := by
  ext i j
  rw [Om4.map_apply']
  change τ ((u1 K : Matrix (Fin 2) (Fin 2) K) i j) = (u1 K : Matrix (Fin 2) (Fin 2) K) i j
  fin_cases i <;> fin_cases j <;> simp [u1]

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

namespace Setup

variable (S : Setup T L I n)

namespace IsCoord

variable {S} {K : Type} [Field K] [Fintype K] [CharP K 2] {e : ↥(fsuV T I) ≃* Om4.VM K}
  {ψ : ↥(fsuL0 T L) →* SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K}
  (hc : S.IsCoord e ψ)
include hc

theorem bar_conj {x : G} (hx : x ∈ fsuM T L) (k : ↥(fsuL0 T L)) :
    Om4.rho (ψ ⟨x * k * x⁻¹, (Subgroup.mem_normalizer_iff.mp hx k).mp k.2⟩) =
      bar e ⟨x, S.hMN hx⟩ * Om4.rho (ψ k) * (bar e ⟨x, S.hMN hx⟩)⁻¹ := by
  rw [← hc.bar_L0, ← hc.bar_L0, ← map_inv, ← map_mul, ← map_mul]
  exact congrArg (bar e) (Subtype.ext rfl)

theorem mem_normalizer_L_of_isNS (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h37c : Vol2Native.A37ForSQTKCat) (h38c : Vol2Native.A38ForSQTKCat)
    {x : G} (hx : x ∈ fsuM T L) {A B : GL (Fin 2) K} {τ : K ≃+* K}
    (hform : bar e ⟨x, S.hMN hx⟩ = Om4.lr A B * Om4.frM τ) :
    x ∈ Subgroup.normalizer (L : Set G) := by
  obtain ⟨t₀, ht₀, ht₀n⟩ := S.exists_not_mem_normalizer
  set PL := (L.subgroupOf (fsuL0 T L)).map ψ with hPL
  have key : ∀ l (hl : l ∈ L), ψ ⟨x * l * x⁻¹,
      (Subgroup.mem_normalizer_iff.mp hx l).mp (S.L_le_L0 hl)⟩ ∈ PL := by
    intro l hl
    have hρ := hc.bar_conj hx ⟨l, S.L_le_L0 hl⟩
    rw [hform, Om4.rho_apply (ψ ⟨l, S.L_le_L0 hl⟩), Om4.conj_isNS] at hρ
    have hmem : ψ ⟨l, S.L_le_L0 hl⟩ ∈ PL :=
      ⟨⟨l, S.L_le_L0 hl⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
    rcases hc.map_L h37c h38c with h | h <;> rw [← hPL] at h <;> rw [h] at hmem ⊢
    · have h2 : (ψ ⟨l, S.L_le_L0 hl⟩).2 = 1 := hmem
      rw [h2, map_one, map_one, mul_one, mul_inv_cancel] at hρ
      obtain ⟨-, h3⟩ := Om4.eq_of_rho_eq_lr (Om4.det_conj_map A τ _) hρ
      exact MonoidHom.mem_ker.mpr (Subtype.ext h3.symm)
    · have h2 : (ψ ⟨l, S.L_le_L0 hl⟩).1 = 1 := hmem
      rw [h2, map_one, map_one, mul_one, mul_inv_cancel] at hρ
      obtain ⟨h3, -⟩ := Om4.eq_of_rho_eq_lr (by rw [Units.val_one, Matrix.det_one]) hρ
      exact MonoidHom.mem_ker.mpr (Subtype.ext h3.symm)
  rcases H13.conjugate_eq_or_of_mem h37 h38 S.hyp.fsu S.not_le_normalizer_L ht₀ ht₀n
      ((fsuM T L).inv_mem hx) with h | h
  · have := (Subgroup.normalizer (L : Set G)).inv_mem
      (Vol2.Ch10.SecA.conjugate_eq_self_iff.mp h)
    rwa [inv_inv] at this
  · exfalso
    have hL0 := H13.fsuL0_eq_sup' h37 h38 S.hyp.fsu S.not_le_normalizer_L ht₀ ht₀n
    rw [← h] at hL0
    have hcl : CFSG.conjugate L x⁻¹ ≤ fsuL0 T L := by rw [hL0]; exact le_sup_right
    have hle : ∀ k : ↥(fsuL0 T L), ψ k ∈ PL := by
      have hsub : L ⊔ CFSG.conjugate L x⁻¹ ≤ (PL.comap ψ).map (fsuL0 T L).subtype := by
        refine sup_le (fun y hy => ⟨⟨y, S.L_le_L0 hy⟩,
          ⟨⟨y, S.L_le_L0 hy⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩, rfl⟩) fun y hy => ?_
        have hy' : x⁻¹ * y * x⁻¹⁻¹ ∈ L := Vol2.Ch10.SecA.mem_conjugate_iff.mp hy
        rw [inv_inv] at hy'
        refine ⟨⟨y, hcl hy⟩, ?_, rfl⟩
        have hk2 : (⟨y, hcl hy⟩ : ↥(fsuL0 T L)) = ⟨x * (x⁻¹ * y * x) * x⁻¹,
            (Subgroup.mem_normalizer_iff.mp hx _).mp (S.L_le_L0 hy')⟩ :=
          Subtype.ext (by simp [mul_assoc])
        show ψ ⟨y, hcl hy⟩ ∈ PL
        rw [hk2]
        exact key _ hy'
      intro k
      have hk : (k : G) ∈ L ⊔ CFSG.conjugate L x⁻¹ := by rw [← hL0]; exact k.2
      obtain ⟨k', hk', hkk'⟩ := hsub hk
      rw [show k = k' from Subtype.ext hkk'.symm]
      exact hk'
    have hne : ((u1 K, u1 K) : SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K) ∉
        PL := by
      have hu : u1 K ≠ 1 := fun h1 => by
        have := congrArg (fun g : SpecialLinearGroup (Fin 2) K =>
          (g : Matrix (Fin 2) (Fin 2) K) 0 1) h1
        simp [u1] at this
      rcases hc.map_L h37c h38c with h' | h' <;> rw [← hPL] at h' <;> rw [h'] <;>
        exact fun hm => hu (MonoidHom.mem_ker.mp hm)
    obtain ⟨k, hk⟩ := hc.surj (u1 K, u1 K)
    exact hne (hk ▸ hle k)

theorem swap_of_not_mem (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h37c : Vol2Native.A37ForSQTKCat) (h38c : Vol2Native.A38ForSQTKCat) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    ∃ (A B : GL (Fin 2) K) (τ : K ≃+* K), Om4.IsUT A ∧ Om4.IsUT B ∧
      bar e ⟨t, S.hMN (Setup.T_le_fsuM ht)⟩ = Om4.lr A B * Om4.frM τ * Om4.trM := by
  have htM : t ∈ fsuM T L := Setup.T_le_fsuM ht
  obtain ⟨A, B, τ, h | h⟩ := hc.exists_form htM
  · exact absurd (hc.mem_normalizer_L_of_isNS h37 h38 h37c h38c htM h) htn
  have hconj : ∀ γ ∈ (uni K).prod (uni K), ∃ k : ↥(fsuL0 T L), ψ k = γ ∧
      ψ ⟨t * k * t⁻¹, (Subgroup.mem_normalizer_iff.mp htM k).mp k.2⟩ ∈ (uni K).prod (uni K) := by
    intro γ hγ
    rw [← hc.sylow] at hγ
    obtain ⟨u, hu, hψu⟩ := hγ
    have huT : (u : G) ∈ T ⊓ fsuL0 T L := Subgroup.mem_subgroupOf.mp hu
    refine ⟨u, hψu, ?_⟩
    rw [← hc.sylow]
    exact ⟨_, Subgroup.mem_subgroupOf.mpr ⟨T.mul_mem (T.mul_mem ht huT.1) (T.inv_mem ht),
      (Subgroup.mem_normalizer_iff.mp htM u).mp u.2⟩, rfl⟩
  refine ⟨A, B, τ, ?_, ?_, h⟩
  · obtain ⟨u, hψu, hψ⟩ := hconj (1, u1 K) ⟨(uni K).one_mem, u1_mem⟩
    have hρ := hc.bar_conj htM u
    have hu : Om4.rho (ψ u) = Om4.lr (Matrix.SpecialLinearGroup.toGL 1)
        (Matrix.SpecialLinearGroup.toGL (u1 K)) := by rw [hψu]; rfl
    rw [h, hu, Om4.conj_swap, map_one, map_one, mul_one, mul_inv_cancel] at hρ
    obtain ⟨h1, -⟩ := Om4.eq_of_rho_eq_lr (Om4.det_conj_map A τ _) hρ
    obtain ⟨c, hc'⟩ := mem_uni_iff.mp hψ.1
    refine FactsFrob.isUT_of_conj_u1 (c := c) ?_
    rw [← hc', ← h1, Units.val_mul, Units.val_mul, map_u1]
  · obtain ⟨u, hψu, hψ⟩ := hconj (u1 K, 1) ⟨u1_mem, (uni K).one_mem⟩
    have hρ := hc.bar_conj htM u
    have hu : Om4.rho (ψ u) = Om4.lr (Matrix.SpecialLinearGroup.toGL (u1 K))
        (Matrix.SpecialLinearGroup.toGL 1) := by rw [hψu]; rfl
    rw [h, hu, Om4.conj_swap, map_one, map_one, mul_one, mul_inv_cancel] at hρ
    obtain ⟨-, h1⟩ := Om4.eq_of_rho_eq_lr (by rw [Units.val_one, Matrix.det_one]) hρ
    obtain ⟨c, hc'⟩ := mem_uni_iff.mp hψ.2
    refine FactsFrob.isUT_of_conj_u1 (c := c) ?_
    rw [← hc', ← h1, Units.val_mul, Units.val_mul, map_u1]

theorem le_two_of_conj (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h37c : Vol2Native.A37ForSQTKCat) (h38c : Vol2Native.A38ForSQTKCat)
    (h1 : zQ T I = fsuV T I) {b : G} (hbL : b ∈ fsuL0 T L)
    (hbZ : b ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hbo : orderOf b = 2 ^ n - 1) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {j : ℕ} (hj : t * b * t⁻¹ = b ^ 2 ^ j) :
    n ≤ 2 := by
  have hn1 : 1 ≤ n := by have := S.two_le; omega
  have hodd : Odd (2 ^ n - 1) := Nat.Even.sub_odd Nat.one_le_two_pow
    (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
  obtain ⟨kb, rfl⟩ : ∃ kb : ↥(fsuL0 T L), (kb : G) = b := ⟨⟨b, hbL⟩, rfl⟩
  obtain ⟨hP, hQ, hPQ⟩ := hc.ut_of_mem_centralizer h1 kb hbZ
  set α := (((ψ kb).1 : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 with hα
  have hpowα : ∀ N : ℕ, (((ψ (kb ^ N)).1 : SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) 0 0 = α ^ N := by
    intro N
    have h3 := Om4.IsUT.pow_apply_zero_zero (A := Matrix.SpecialLinearGroup.toGL (ψ kb).1) hP N
    rw [map_pow, Prod.pow_fst]
    rw [← map_pow] at h3
    exact h3
  have hkill : ∀ N : ℕ, α ^ N = 1 → 2 ^ n - 1 ∣ N := by
    intro N hN
    have h2 := (hpowα N).trans hN
    have h3 := hc.eq_one_of_chi h37c h38c h1 (kb ^ N) (by
      show (kb : G) ^ N ∈ _
      exact Subgroup.pow_mem _ hbZ _) (by
      show Odd (orderOf ((kb : G) ^ N))
      exact hodd.of_dvd_nat (hbo ▸ orderOf_pow_dvd N)) h2
    have h4 : (kb : G) ^ N = 1 := h3
    rw [← hbo]
    exact orderOf_dvd_of_pow_eq_one h4
  obtain ⟨A, B, τ, hA, -, hform⟩ := hc.swap_of_not_mem h37 h38 h37c h38c ht htn
  have htM : t ∈ fsuM T L := Setup.T_le_fsuM ht
  have hkb : (⟨t * kb * t⁻¹, (Subgroup.mem_normalizer_iff.mp htM kb).mp kb.2⟩ :
      ↥(fsuL0 T L)) = kb ^ 2 ^ j := Subtype.ext hj
  have hρ := hc.bar_conj htM kb
  rw [hform, Om4.rho_apply (ψ kb), Om4.conj_swap, hkb] at hρ
  obtain ⟨h2, -⟩ := Om4.eq_of_rho_eq_lr (Om4.det_conj_map A τ _) hρ
  have h00 := congrFun (congrFun h2 0) 0
  rw [(Om4.conj_map_apply hA (show Om4.IsUT (Matrix.SpecialLinearGroup.toGL (ψ kb).2) from hQ)
    τ).1, hpowα] at h00
  have hQ0 : ((Matrix.SpecialLinearGroup.toGL (ψ kb).2 : GL (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) 0 0 = α⁻¹ := eq_inv_of_mul_eq_one_right hPQ
  rw [hQ0, map_inv₀] at h00
  obtain ⟨i, hi, hτ⟩ := exists_frob_pow_lt hn1 hc.card τ
  rw [hτ, pow_two_pow_mod hc.card α j] at h00
  have hα1 : α ^ (2 ^ (j % n) + 2 ^ i) = 1 := by
    rw [pow_add, ← h00, inv_mul_cancel₀]
    exact pow_ne_zero _ (left_ne_zero_of_mul_eq_one hPQ)
  exact le_two_of_dvd_add (Nat.mod_lt _ (by omega)) hi (hkill _ hα1)

end IsCoord

include S in
theorem exists_mem_normalizer_cartan {B D : Subgroup G}
    (hD : Lin2.IsHallTwoPrimeOf D
      (fsuL0 T L ⊓ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G)))
    (hBD : B = D ⊓ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G)) :
    ∃ t ∈ T, t ∉ Subgroup.normalizer (L : Set G) ∧ t ∈ Subgroup.normalizer (B : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t₀, ht₀, ht₀n⟩ := S.exists_not_mem_normalizer
  set P₀ := T ⊓ fsuL0 T L with hP₀
  set N₀ := fsuL0 T L ⊓ Subgroup.normalizer (P₀ : Set G) with hN₀
  have hP₀N₀ : P₀ ≤ N₀ := fun x hx => ⟨hx.2, Subgroup.le_normalizer hx⟩
  have hP₀2 : IsPGroup 2 P₀ := S.hyp.fsu.sylow.1.to_le inf_le_left
  have hP₀i : ¬ 2 ∣ P₀.relIndex N₀ := by
    intro h2
    apply S.isSylowTwoOf_T_inf_L0.2.2
    show 2 ∣ P₀.relIndex (fsuL0 T L)
    rw [← Subgroup.relIndex_mul_relIndex P₀ N₀ (fsuL0 T L) hP₀N₀ inf_le_left]
    exact h2.mul_right _
  have hP₀S : IsSylowTwoOf P₀ N₀ := ⟨hP₀N₀, hP₀2, hP₀i⟩
  have hTP : ∀ s ∈ T, s ∈ Subgroup.normalizer (P₀ : Set G) := fun s hs =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hs,
      Setup.T_le_normalizer_L0 hs⟩
  have hTN : ∀ s ∈ T, s ∈ Subgroup.normalizer (N₀ : Set G) := fun s hs =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Setup.T_le_normalizer_L0 hs,
      Subgroup.le_normalizer (hTP s hs)⟩
  set D' := D.map (MulAut.conj t₀).toMonoidHom with hD'def
  have hD' : Lin2.IsHallTwoPrimeOf D' N₀ :=
    Vol2.Ch10.SecB.C11AmS.isHallTwoPrimeOf_map_conj (hTN t₀ ht₀) hD
  have hsup : P₀ ⊔ D = P₀ ⊔ D' :=
    (le_antisymm (sup_le hP₀N₀ hD.1) (Vol2.Ch10.SecB.C11AmS.le_sup_of_hall hP₀S hD)).trans
      (le_antisymm (Vol2.Ch10.SecB.C11AmS.le_sup_of_hall hP₀S hD') (sup_le hP₀N₀ hD'.1))
  obtain ⟨m, hm, hmD⟩ := Vol2.Ch10.SecB.C11AmS.exists_conj_of_complement hP₀2 hD.2.1
    (hD.1.trans inf_le_right) (hD'.1.trans inf_le_right)
    (Vol2.Ch10.SecB.C11AmS.inf_eq_bot_of_odd hP₀2 hD.2.1)
    (Vol2.Ch10.SecB.C11AmS.inf_eq_bot_of_odd hP₀2 hD'.2.1) hsup
  have hmT : m ∈ T := hm.1
  refine ⟨m * t₀, T.mul_mem hmT ht₀, fun hmt => ht₀n ?_, ?_⟩
  · have hmN : m ∈ Subgroup.normalizer (L : Set G) :=
      Vol2.Ch10.SecA.fsuL0_le_normalizer S.hyp.fsu.maximal.1 hm.2
    have := (Subgroup.normalizer (L : Set G)).mul_mem
      ((Subgroup.normalizer (L : Set G)).inv_mem hmN) hmt
    rwa [inv_mul_cancel_left] at this
  have hDn : ∀ d ∈ D, (m * t₀) * d * (m * t₀)⁻¹ ∈ D := by
    intro d hd
    have h1 : t₀ * d * t₀⁻¹ ∈ D' := ⟨d, hd, by simp [MulAut.conj_apply]⟩
    rw [hmD] at h1
    obtain ⟨d₂, hd₂, hd₂e⟩ := h1
    have h2 : m⁻¹ * d₂ * m = t₀ * d * t₀⁻¹ := by simpa [MulAut.conj_apply] using hd₂e
    have h3 : (m * t₀) * d * (m * t₀)⁻¹ = d₂ := by
      calc (m * t₀) * d * (m * t₀)⁻¹ = m * (t₀ * d * t₀⁻¹) * m⁻¹ := by group
        _ = m * (m⁻¹ * d₂ * m) * m⁻¹ := by rw [h2]
        _ = d₂ := by group
    rw [h3]
    exact hd₂
  have hDN : m * t₀ ∈ Subgroup.normalizer (D : Set G) := by
    have hle : D.map (MulAut.conj (m * t₀)).toMonoidHom ≤ D := by
      rintro _ ⟨d, hd, rfl⟩
      show (MulAut.conj (m * t₀)) d ∈ D
      rw [MulAut.conj_apply]
      exact hDn d hd
    have heq := Subgroup.eq_of_le_of_card_ge hle
      (Subgroup.card_map_of_injective (MulAut.conj (m * t₀)).injective).ge
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq
  have hNC : ∀ {Y : Subgroup G} {s : G}, s ∈ Subgroup.normalizer (Y : Set G) →
      s ∈ Subgroup.normalizer (Subgroup.centralizer (Y : Set G) : Set G) := by
    intro Y s hs
    refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => H13.conj_mem_centralizer hs hx,
      fun hx => ?_⟩
    have := H13.conj_mem_centralizer ((Subgroup.normalizer (Y : Set G)).inv_mem hs) hx
    simpa [mul_assoc] using this
  have hV1 : m * t₀ ∈ Subgroup.normalizer ((fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨S.T_le_normalizer_V (T.mul_mem hmT ht₀),
      hNC (hTP _ (T.mul_mem hmT ht₀))⟩
  rw [hBD]
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hDN, hNC hV1⟩

end Setup

end CFSG.Quasithin.H13.Ch9
