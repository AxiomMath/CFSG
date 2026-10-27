module

public import CFSG.RankThree.GroupTheory.ComponentCubeObstruction
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.RankThree

open Matrix Subgroup CFSG CFSG.Assembly.LowTwoRank

section EvenUnitaryThree

variable {F : Type} [Field F]

@[expose] def eu3P : Matrix (Fin 3) (Fin 3) F := !![1, 1, 0; 1, 1, 1; 0, 1, 1]

@[expose] def eu3Pinv : Matrix (Fin 3) (Fin 3) F := !![0, 1, 1; 1, 1, 1; 1, 1, 0]

@[expose] def eu3J : Matrix (Fin 3) (Fin 3) F := !![0, 0, 1; 0, 1, 0; 1, 0, 0]

@[expose] def eu3U (t : F) : Matrix (Fin 3) (Fin 3) F := !![1, 0, t; 0, 1, 0; 0, 0, 1]

@[expose] def eu3D (a b c : F) : Matrix (Fin 3) (Fin 3) F := !![a, 0, 0; 0, b, 0; 0, 0, c]

@[expose] def eu3Conj (M : Matrix (Fin 3) (Fin 3) F) : Matrix (Fin 3) (Fin 3) F :=
  eu3P * M * eu3Pinv

theorem eu3P_transpose : (eu3P : Matrix (Fin 3) (Fin 3) F)ᵀ = eu3P := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem eu3Pinv_transpose : (eu3Pinv : Matrix (Fin 3) (Fin 3) F)ᵀ = eu3Pinv := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem eu3P_map {g : F → F} (h0 : g 0 = 0) (h1 : g 1 = 1) :
    (eu3P : Matrix (Fin 3) (Fin 3) F).map g = eu3P := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eu3P, h0, h1]

theorem eu3Pinv_map {g : F → F} (h0 : g 0 = 0) (h1 : g 1 = 1) :
    (eu3Pinv : Matrix (Fin 3) (Fin 3) F).map g = eu3Pinv := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eu3Pinv, h0, h1]

theorem eu3U_map {g : F → F} (h0 : g 0 = 0) (h1 : g 1 = 1) (t : F) :
    (eu3U t).map g = eu3U (g t) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eu3U, h0, h1]

theorem eu3D_map {g : F → F} (h0 : g 0 = 0) (a b c : F) :
    (eu3D a b c).map g = eu3D (g a) (g b) (g c) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eu3D, h0]

theorem eu3U_mul (t s : F) : eu3U t * eu3U s = eu3U (t + s) := by
  rw [eu3U, eu3U, eu3U, Matrix.mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [add_comm]

theorem eu3U_zero : eu3U (0 : F) = 1 := by
  rw [eu3U, Matrix.one_fin_three]

theorem eu3D_mul (a b c a' b' c' : F) :
    eu3D a b c * eu3D a' b' c' = eu3D (a * a') (b * b') (c * c') := by
  rw [eu3D, eu3D, eu3D, Matrix.mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem eu3D_one : eu3D (1 : F) 1 1 = 1 := by
  rw [eu3D, Matrix.one_fin_three]

theorem eu3D_pow (a b c : F) (n : ℕ) : eu3D a b c ^ n = eu3D (a ^ n) (b ^ n) (c ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, pow_zero, pow_zero, eu3D_one]
  | succ n ih => rw [pow_succ, ih, eu3D_mul, ← pow_succ, ← pow_succ, ← pow_succ]

theorem det_eu3U (t : F) : (eu3U t).det = 1 := by
  simp [eu3U, det_fin_three]

theorem det_eu3D (a b c : F) : (eu3D a b c).det = a * b * c := by
  simp [eu3D, det_fin_three]

theorem eu3D_mul_eu3U {a b c t s : F} (h : a * t = s * c) :
    eu3D a b c * eu3U t = eu3U s * eu3D a b c := by
  rw [eu3D, eu3U, eu3U, Matrix.mul_fin_three, Matrix.mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h]

theorem eu3D_transpose_mul_J_mul {a b c a' b' c' : F} (h1 : a' * c = 1) (h2 : b' * b = 1)
    (h3 : c' * a = 1) : (eu3D a' b' c')ᵀ * eu3J * eu3D a b c = eu3J := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eu3D, eu3J, Matrix.mul_apply, Fin.sum_univ_three, h1, h2, h3]

section CharTwo

variable [CharP F 2]

theorem eu3P_mul_Pinv : (eu3P : Matrix (Fin 3) (Fin 3) F) * eu3Pinv = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [eu3P, eu3Pinv, Matrix.mul_fin_three, Matrix.one_fin_three]
  ext a b; fin_cases a <;> fin_cases b <;> simp <;> linear_combination h2

theorem eu3Pinv_mul_P : (eu3Pinv : Matrix (Fin 3) (Fin 3) F) * eu3P = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [eu3P, eu3Pinv, Matrix.mul_fin_three, Matrix.one_fin_three]
  ext a b; fin_cases a <;> fin_cases b <;> simp <;> linear_combination h2

theorem eu3P_mul_P : (eu3P : Matrix (Fin 3) (Fin 3) F) * eu3P = eu3J := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [eu3P, eu3J, Matrix.mul_fin_three]
  ext a b; fin_cases a <;> fin_cases b <;> simp <;> linear_combination h2

theorem eu3Pinv_mul_J_mul_Pinv : (eu3Pinv : Matrix (Fin 3) (Fin 3) F) * eu3J * eu3Pinv = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [eu3Pinv, eu3J, Matrix.mul_fin_three, Matrix.mul_fin_three, Matrix.one_fin_three]
  ext a b; fin_cases a <;> fin_cases b <;> simp <;> linear_combination h2

theorem eu3Conj_mul (M N : Matrix (Fin 3) (Fin 3) F) :
    eu3Conj (M * N) = eu3Conj M * eu3Conj N := by
  simp only [eu3Conj, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc eu3Pinv eu3P, eu3Pinv_mul_P, Matrix.one_mul]

theorem eu3Conj_one : eu3Conj (1 : Matrix (Fin 3) (Fin 3) F) = 1 := by
  rw [eu3Conj, Matrix.mul_one, eu3P_mul_Pinv]

theorem eu3Conj_pow (M : Matrix (Fin 3) (Fin 3) F) (n : ℕ) : eu3Conj (M ^ n) = eu3Conj M ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, eu3Conj_one]
  | succ n ih => rw [pow_succ, eu3Conj_mul, ih, pow_succ]

theorem eu3Pinv_mul_eu3Conj_mul_P (M : Matrix (Fin 3) (Fin 3) F) :
    eu3Pinv * eu3Conj M * eu3P = M := by
  simp only [eu3Conj, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc eu3Pinv eu3P, eu3Pinv_mul_P, Matrix.one_mul, Matrix.mul_one]

theorem det_eu3Conj (M : Matrix (Fin 3) (Fin 3) F) : (eu3Conj M).det = M.det := by
  rw [eu3Conj, det_mul, det_mul, mul_comm (eu3P.det), mul_assoc, ← det_mul, eu3P_mul_Pinv,
    det_one, mul_one]

theorem unitary_eu3Conj {f : ℕ} {M : Matrix (Fin 3) (Fin 3) F}
    (hM : (M.map (· ^ 2 ^ f))ᵀ * eu3J * M = eu3J) :
    ((eu3Conj M).map (· ^ 2 ^ f))ᵀ * eu3Conj M = 1 := by
  have hφ : ∀ N : Matrix (Fin 3) (Fin 3) F,
      N.map (· ^ 2 ^ f) = N.map (iterateFrobenius F 2 f) := fun N => by
    ext i j
    simp [iterateFrobenius_def]
  rw [hφ] at hM ⊢
  rw [eu3Conj, Matrix.map_mul, Matrix.map_mul, eu3P_map (map_zero _) (map_one _),
    eu3Pinv_map (map_zero _) (map_one _), Matrix.transpose_mul, Matrix.transpose_mul,
    eu3P_transpose, eu3Pinv_transpose]
  calc eu3Pinv * ((M.map (iterateFrobenius F 2 f))ᵀ * eu3P) * (eu3P * M * eu3Pinv)
      = eu3Pinv * ((M.map (iterateFrobenius F 2 f))ᵀ * (eu3P * eu3P) * M) * eu3Pinv := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [eu3P_mul_P, hM, eu3Pinv_mul_J_mul_Pinv]

theorem unitaryJ_eu3U {f : ℕ} {t : F} (ht : t ^ 2 ^ f = t) :
    ((eu3U t).map (· ^ 2 ^ f))ᵀ * eu3J * eu3U t = eu3J := by
  have hq : (2 : ℕ) ^ f ≠ 0 := pow_ne_zero _ two_ne_zero
  rw [eu3U_map (g := fun x : F => x ^ 2 ^ f) (zero_pow hq) (one_pow _), ht]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eu3U, eu3J, Matrix.mul_apply, Fin.sum_univ_three, CharTwo.add_self_eq_zero]

theorem eq_scalar_of_eu3Conj_eq {M : Matrix (Fin 3) (Fin 3) F} {c : F}
    (h : eu3Conj M = Matrix.scalar (Fin 3) c) : M = Matrix.scalar (Fin 3) c :=
  calc M = eu3Pinv * eu3Conj M * eu3P := (eu3Pinv_mul_eu3Conj_mul_P M).symm
    _ = Matrix.scalar (Fin 3) c * eu3Pinv * eu3P := by
        rw [h, (Matrix.scalar_commute c (fun _ => Commute.all _ _) eu3Pinv).eq]
    _ = Matrix.scalar (Fin 3) c := by rw [Matrix.mul_assoc, eu3Pinv_mul_P, Matrix.mul_one]

end CharTwo

section Torus

variable {f : ℕ}

@[expose] noncomputable def eu3Torus (f : ℕ) (a : F) : Matrix (Fin 3) (Fin 3) F :=
  eu3D a (a ^ (2 ^ f - 1)) (a ^ 2 ^ f)⁻¹

theorem det_eu3Torus {a : F} (ha : a ≠ 0) : (eu3Torus f a).det = 1 := by
  rw [eu3Torus, det_eu3D, mul_pow_sub_one (pow_ne_zero _ two_ne_zero),
    mul_inv_cancel₀ (pow_ne_zero _ ha)]

theorem pow_sq_sub_one_eq_one (hpow : ∀ y : F, y ^ (2 ^ f) ^ 2 = y) {a : F} (ha : a ≠ 0) :
    a ^ ((2 ^ f) ^ 2 - 1) = 1 := by
  have h := mul_pow_sub_one (pow_ne_zero 2 (pow_ne_zero f two_ne_zero)) a
  rw [hpow] at h
  exact mul_left_cancel₀ ha (h.trans (mul_one a).symm)

theorem unitaryJ_eu3Torus (hpow : ∀ y : F, y ^ (2 ^ f) ^ 2 = y) {a : F} (ha : a ≠ 0) :
    ((eu3Torus f a).map (· ^ 2 ^ f))ᵀ * eu3J * eu3Torus f a = eu3J := by
  rw [eu3Torus, eu3D_map (g := fun x : F => x ^ 2 ^ f) (zero_pow (pow_ne_zero _ two_ne_zero))]
  apply eu3D_transpose_mul_J_mul
  · exact mul_inv_cancel₀ (pow_ne_zero _ ha)
  · have hq : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    have he : (2 ^ f - 1) * 2 ^ f + (2 ^ f - 1) = (2 ^ f) ^ 2 - 1 := by
      obtain ⟨k, hk⟩ : ∃ k, 2 ^ f = k + 1 := ⟨2 ^ f - 1, by omega⟩
      rw [hk, Nat.add_sub_cancel]
      symm
      apply Nat.sub_eq_of_eq_add
      ring
    rw [← pow_mul, ← pow_add, he, pow_sq_sub_one_eq_one hpow ha]
  · rw [inv_pow, ← pow_mul, ← sq, hpow, inv_mul_cancel₀ ha]

theorem eu3Torus_mul_eu3U {a : F} (ha : a ≠ 0) (t : F) :
    eu3Torus f a * eu3U t = eu3U (a ^ (2 ^ f + 1) * t) * eu3Torus f a := by
  rw [eu3Torus]
  apply eu3D_mul_eu3U
  rw [pow_succ]
  field_simp

theorem eu3Torus_pow (a : F) (n : ℕ) : eu3Torus f a ^ n = eu3Torus f (a ^ n) := by
  rw [eu3Torus, eu3Torus, eu3D_pow]
  congr 1
  · rw [← pow_mul, ← pow_mul, mul_comm]
  · rw [inv_pow, ← pow_mul, ← pow_mul, mul_comm]

theorem eu3Torus_one : eu3Torus f (1 : F) = 1 := by
  rw [eu3Torus, one_pow, one_pow, inv_one, eu3D_one]

theorem pow_succ_mul_fixed (hpow : ∀ y : F, y ^ (2 ^ f) ^ 2 = y) (a : F) {t : F}
    (ht : t ^ 2 ^ f = t) : (a ^ (2 ^ f + 1) * t) ^ 2 ^ f = a ^ (2 ^ f + 1) * t := by
  rw [mul_pow, ht, ← pow_mul, show (2 ^ f + 1) * 2 ^ f = (2 ^ f) ^ 2 + 2 ^ f by ring, pow_add,
    hpow, ← pow_succ']

end Torus

section Elements

variable [CharP F 2] {f : ℕ}

@[expose] noncomputable def eu3SU (M : Matrix (Fin 3) (Fin 3) F) (hdet : M.det = 1)
    (hM : (M.map (· ^ 2 ^ f))ᵀ * eu3J * M = eu3J) : StatedSU 3 (2 ^ f) F :=
  ⟨GeneralLinearGroup.mkOfDetNeZero (eu3Conj M) (by rw [det_eu3Conj, hdet]; exact one_ne_zero),
    subset_closure ⟨by rw [GeneralLinearGroup.val_mkOfDetNeZero, det_eu3Conj, hdet], by
      rw [GeneralLinearGroup.val_mkOfDetNeZero]; exact unitary_eu3Conj hM⟩⟩

theorem coe_eu3SU (M : Matrix (Fin 3) (Fin 3) F) (hdet : M.det = 1)
    (hM : (M.map (· ^ 2 ^ f))ᵀ * eu3J * M = eu3J) :
    (((eu3SU M hdet hM : StatedSU 3 (2 ^ f) F) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      eu3Conj M :=
  GeneralLinearGroup.val_mkOfDetNeZero _ _

omit [CharP F 2] in
theorem eu3_ext {x y : StatedSU 3 (2 ^ f) F}
    (h : ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) : x = y :=
  Subtype.ext (Units.ext h)

variable (F f) in
@[expose] noncomputable def eu3Root : Subgroup (StatedSU 3 (2 ^ f) F) where
  carrier := {x | ∃ t : F, t ^ 2 ^ f = t ∧
    ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = eu3Conj (eu3U t)}
  mul_mem' := by
    rintro x y ⟨t, ht, hx⟩ ⟨s, hs, hy⟩
    refine ⟨t + s, by rw [add_pow_char_pow, ht, hs], ?_⟩
    rw [Subgroup.coe_mul, Units.val_mul, hx, hy, ← eu3Conj_mul, eu3U_mul]
  one_mem' := ⟨0, zero_pow (pow_ne_zero _ two_ne_zero), by
    rw [OneMemClass.coe_one, Units.val_one, eu3U_zero, eu3Conj_one]⟩
  inv_mem' := by
    rintro x ⟨t, ht, hx⟩
    have hxx : x * x = 1 := eu3_ext (by
      rw [Subgroup.coe_mul, Units.val_mul, hx, ← eu3Conj_mul, eu3U_mul,
        CharTwo.add_self_eq_zero, eu3U_zero, eu3Conj_one, OneMemClass.coe_one, Units.val_one])
    exact ⟨t, ht, by rw [inv_eq_of_mul_eq_one_right hxx, hx]⟩

theorem isPGroup_eu3Root : IsPGroup 2 (eu3Root F f) := by
  rintro ⟨x, t, ht, hx⟩
  refine ⟨1, Subtype.ext (eu3_ext ?_)⟩
  rw [pow_one, SubgroupClass.coe_pow, SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, hx, sq,
    ← eu3Conj_mul, eu3U_mul, CharTwo.add_self_eq_zero, eu3U_zero, eu3Conj_one,
    OneMemClass.coe_one, OneMemClass.coe_one, Units.val_one]

end Elements

theorem exists_prime_gt_three_dvd_two_pow_sq_sub_one {f : ℕ} (hf : 2 ≤ f) :
    ∃ r : ℕ, r.Prime ∧ 3 < r ∧ r ∣ (2 ^ f) ^ 2 - 1 := by
  set q := 2 ^ f with hqdef
  have hq4 : 4 ≤ q := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have h3q : ¬ 3 ∣ q := fun h => by
    have := Nat.prime_three.dvd_of_dvd_pow h
    omega
  have hq2 : 2 ∣ q := dvd_pow_self 2 (by omega)
  have hfac : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    obtain ⟨k, hk⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
    rw [hk, Nat.add_sub_cancel]
    apply Nat.sub_eq_of_eq_add
    ring
  have key : ∀ m : ℕ, m ∣ q ^ 2 - 1 → 1 < m → ¬ 2 ∣ m → ¬ 3 ∣ m →
      ∃ r : ℕ, r.Prime ∧ 3 < r ∧ r ∣ q ^ 2 - 1 := by
    intro m hm hm1 hm2 hm3
    obtain ⟨r, hr, hrm⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
    have hr2 : r ≠ 2 := by
      rintro rfl
      exact hm2 hrm
    have hr3 : r ≠ 3 := by
      rintro rfl
      exact hm3 hrm
    have := hr.two_le
    exact ⟨r, hr, by omega, hrm.trans hm⟩
  rcases (by omega : q % 3 = 1 ∨ q % 3 = 2) with h | h
  · exact key (q + 1) (hfac ▸ dvd_mul_left _ _) (by omega) (by omega) (by omega)
  · exact key (q - 1) (hfac ▸ dvd_mul_right _ _) (by omega) (by omega) (by omega)

theorem even_unitary_three_witness [Finite F] {f : ℕ} (hf : 2 ≤ f)
    (hF : Nat.card F = (2 ^ f) ^ 2) :
    ∃ V : Subgroup (StatedProj (StatedSU 3 (2 ^ f) F)), V ≠ ⊥ ∧ IsPGroup 2 V ∧
      ∃ r : ℕ, r.Prime ∧ 3 < r ∧
        r ∣ Nat.card (normalizer (V : Set (StatedProj (StatedSU 3 (2 ^ f) F)))) := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = (2 ^ f) ^ 2 := by rw [← Nat.card_eq_fintype_card]; exact hF
  have h2 : (2 : F) = 0 := by
    have h := FiniteField.cast_card_eq_zero F
    rw [hcard, Nat.cast_pow, Nat.cast_pow] at h
    exact (pow_eq_zero_iff (by omega : f ≠ 0)).1 ((pow_eq_zero_iff two_ne_zero).1 (by
      exact_mod_cast h))
  have : CharP F 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 (by exact_mod_cast h2)
  have hpow : ∀ y : F, y ^ (2 ^ f) ^ 2 = y := fun y => by
    rw [← hcard]
    exact FiniteField.pow_card y
  obtain ⟨r, hr, hr3, hrd⟩ := exists_prime_gt_three_dvd_two_pow_sq_sub_one hf
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨a, ha⟩ :=
    exists_prime_orderOf_dvd_card' (G := Fˣ) r (by rw [Nat.card_units, hF]; exact hrd)
  have ha0 : (a : F) ≠ 0 := a.ne_zero
  set S := StatedSU 3 (2 ^ f) F
  set ρ : S →* StatedProj S := QuotientGroup.mk' _
  have hscal : ∀ (x : S) (M : Matrix (Fin 3) (Fin 3) F),
      ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = eu3Conj M → ρ x = 1 →
        ∃ c : F, M = Matrix.scalar (Fin 3) c := by
    intro x M hx h1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf, StatedScalars,
      MonoidHom.mem_range] at h1
    obtain ⟨c, hc⟩ := h1
    refine ⟨c, eq_scalar_of_eu3Conj_eq ?_⟩
    rw [← hx, ← hc, GeneralLinearGroup.coe_scalar]
  set x₁ : S := eu3SU (eu3U 1) (det_eu3U 1) (unitaryJ_eu3U (one_pow _))
  have hx₁ : x₁ ∈ eu3Root F f := ⟨1, one_pow _, coe_eu3SU _ _ _⟩
  set V := (eu3Root F f).map ρ
  have hVne : V ≠ ⊥ := by
    intro hV
    have hmem : ρ x₁ ∈ V := mem_map_of_mem ρ hx₁
    rw [hV, mem_bot] at hmem
    obtain ⟨c, hc⟩ := hscal x₁ _ (coe_eu3SU _ _ _) hmem
    have h02 := congrFun (congrFun hc 0) 2
    simp [eu3U] at h02
  set x : S := eu3SU (eu3Torus f (a : F)) (det_eu3Torus ha0) (unitaryJ_eu3Torus hpow ha0)
  have hxN : x ∈ normalizer ((eu3Root F f : Subgroup S) : Set S) := by
    rw [mem_normalizer_iff_map_conj_eq]
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨g, ⟨t, ht, hg⟩, rfl⟩
      have hs := pow_succ_mul_fixed hpow (a : F) ht
      set y : S := eu3SU (eu3U ((a : F) ^ (2 ^ f + 1) * t)) (det_eu3U _) (unitaryJ_eu3U hs)
      have hxy : x * g = y * x := eu3_ext (by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_eu3SU,
          coe_eu3SU, hg, ← eu3Conj_mul, ← eu3Conj_mul, eu3Torus_mul_eu3U ha0])
      change x * g * x⁻¹ ∈ eu3Root F f
      rw [mul_inv_eq_of_eq_mul hxy]
      exact ⟨_, hs, coe_eu3SU _ _ _⟩
    · rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]
  have hρxN : ρ x ∈ normalizer (V : Set (StatedProj S)) :=
    le_normalizer_map ρ (mem_map_of_mem ρ hxN)
  have hxr : ρ x ^ r = 1 := by
    rw [← map_pow]
    have : x ^ r = 1 := eu3_ext (by
      rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, coe_eu3SU, ← eu3Conj_pow,
        eu3Torus_pow, ← Units.val_pow_eq_pow_val, ← ha, pow_orderOf_eq_one, Units.val_one,
        eu3Torus_one, eu3Conj_one, OneMemClass.coe_one, Units.val_one])
    rw [this, map_one]
  have hx1 : ρ x ≠ 1 := by
    intro h1
    obtain ⟨c, hc⟩ := hscal x _ (coe_eu3SU _ _ _) h1
    have h00 := congrFun (congrFun hc 0) 0
    have h11 := congrFun (congrFun hc 1) 1
    have h22 := congrFun (congrFun hc 2) 2
    simp [eu3Torus, eu3D] at h00 h11 h22
    have hdet := det_eu3Torus (f := f) ha0
    rw [eu3Torus, det_eu3D, h11, h22, ← h00] at hdet
    have ha3 : a ^ 3 = 1 := Units.ext (by
      rw [Units.val_pow_eq_pow_val, Units.val_one, ← hdet]
      ring)
    have hdvd := orderOf_dvd_of_pow_eq_one ha3
    rw [ha] at hdvd
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have hord : orderOf (ρ x) = r := orderOf_eq_prime hxr hx1
  refine ⟨V, hVne, (isPGroup_eu3Root).map ρ, r, hr, hr3, ?_⟩
  have h := orderOf_dvd_natCard (⟨ρ x, hρxN⟩ : normalizer (V : Set (StatedProj S)))
  rwa [Subgroup.orderOf_mk, hord] at h

end EvenUnitaryThree

open CFSG.RankThree.LocalRank
open CFSG.Assembly.RankThreeEven (localRank)

theorem theta_free_even_unitary_three_component_normalization_at_three {G : Type} [Group G]
    [Finite G] (hθ : aschbacherSolvableCore 3 G = ⊥) (he : twoLocalOddRank G ≤ 3)
    (hq : ∀ r : ℕ, r.Prime → 3 < r → localRank r G ≤ 2) (h3 : pCore 3 G ≠ ⊥)
    {A : Subgroup G} (hA : IsPGroup 3 A) :
    (∀ L ∈ thetaComponents 3 G, ∀ f : ℕ,
      StatedClassicalModel (L ⧸ center L) .PSU 3 2 f → A ≤ normalizer (L : Set G)) ∧
    ∀ L : Subgroup G, IsComponent L → ∀ f : ℕ,
      StatedClassicalModel (L ⧸ center L) .PSU 3 2 f → A ≤ normalizer (L : Set G) := by
  have hmain : ∀ L ∈ thetaComponents 3 G, ∀ f : ℕ,
      StatedClassicalModel (L ⧸ center L) .PSU 3 2 f → A ≤ normalizer (L : Set G) := by
    rintro L hL f ⟨⟨-, hf, -, hne⟩, F, _, _, hF, ⟨e⟩⟩
    have hf2 : 2 ≤ f := by
      by_contra h
      have h1 : f = 1 := by omega
      exact hne (by rw [h1, pow_one])
    refine normalizes_of_quotient_witness hθ he hq h3 hA hL fun _ _ => ?_
    exact quotient_witness_of_mulEquiv e
      ((even_unitary_three_witness hf2 hF).imp fun V ⟨hV, hV2, r, hr, hr3, hrd⟩ =>
        ⟨hV, hV2, Or.inl ⟨r, hr, hr3, hrd⟩⟩)
  exact ⟨hmain, fun L hL => hmain L (mem_thetaComponents_of_isComponent Nat.prime_three hθ hL)⟩

end CFSG.RankThree
