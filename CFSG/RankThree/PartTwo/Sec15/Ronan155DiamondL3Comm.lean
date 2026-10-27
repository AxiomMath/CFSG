module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData

public section

namespace CFSG.RankThree.PartTwo.Sec15.Ronan155DiamondL3

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix

variable {K : Type*} [Field K] [Finite K] [CharP K 2]

@[expose] noncomputable def diagSL (a b : K) (hab : a * b = 1) :
    Matrix.SpecialLinearGroup (Fin 3) K :=
  ⟨!![a, 0, 0; 0, b, 0; 0, 0, 1], by simp [Matrix.det_fin_three, hab]⟩

@[simp] theorem coe_diagSL (a b : K) (hab : a * b = 1) :
    ((diagSL a b hab : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![a, 0, 0; 0, b, 0; 0, 0, 1] :=
  rfl

@[expose] noncomputable def unipSL (α : K) : Matrix.SpecialLinearGroup (Fin 3) K :=
  ⟨!![1, α, 0; 0, 1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

@[simp] theorem coe_unipSL (α : K) :
    ((unipSL α : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![1, α, 0; 0, 1, 0; 0, 0, 1] :=
  rfl

theorem unipSL_mul_self (α : K) : unipSL α * unipSL α = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, coe_unipSL]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, CharTwo.add_self_eq_zero]

theorem unipSL_inv (α : K) : (unipSL α)⁻¹ = unipSL α :=
  inv_eq_of_mul_eq_one_right (unipSL_mul_self α)

theorem inv_proj_eq_of_mul_eq_one {g h : Matrix.SpecialLinearGroup (Fin 3) K} (hgh : g * h = 1) :
    (proj 3 K g)⁻¹ = proj 3 K h := by
  apply inv_eq_of_mul_eq_one_right
  rw [← map_mul (proj 3 K), hgh, map_one]

theorem pow_mulVec_eq_smul {M : Matrix (Fin 3) (Fin 3) K} {v : Fin 3 → K} {μ : K}
    (hv : M *ᵥ v = μ • v) (k : ℕ) : (M ^ k) *ᵥ v = μ ^ k • v := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ M k, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul, ih, smul_smul,
      ← pow_succ' μ k]

theorem scalar_eq_one_of_pow_twelve {M : Matrix (Fin 3) (Fin 3) K} {c : K}
    (hpow : M ^ 12 = Matrix.scalar (Fin 3) c) (he : M *ᵥ ![0, 0, 1] = ![0, 0, 1]) : c = 1 := by
  have he' : M *ᵥ ![0, 0, 1] = (1 : K) • ![0, 0, 1] := by
    rw [one_smul]
    exact he
  have h := pow_mulVec_eq_smul he' 12
  rw [hpow] at h
  have h2 := congrFun h 2
  simpa [Matrix.scalar_apply, Matrix.mulVec_diagonal] using h2

theorem pow_twelve_eq_one_of_mulVec {M : Matrix (Fin 3) (Fin 3) K} {v : Fin 3 → K} {μ : K}
    (hpow : M ^ 12 = 1) (hv : M *ᵥ v = μ • v) {i : Fin 3} (hi : v i ≠ 0) : μ ^ 12 = 1 := by
  have h := pow_mulVec_eq_smul hv 12
  rw [hpow, Matrix.one_mulVec] at h
  have h2 := congrFun h i
  simp only [Pi.smul_apply, smul_eq_mul] at h2
  apply mul_right_cancel₀ hi
  rw [one_mul]
  exact h2.symm

theorem mulVec_unip_eq {α B U V : K} (h2 : (2 : K) = 0) (hT : B * α = U + V)
    (hUV : U * V = 1) :
    !![1, α, 0; B, 1 + B * α, 0; 0, 0, 1] *ᵥ ![α, 1 + U, 0] = U • ![α, 1 + U, 0] := by
  ext i
  fin_cases i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    linear_combination α * h2
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    linear_combination (2 + U) * hT + hUV + (U + V + 1) * h2
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem val_pow_eq_one_iff {x : Kˣ} {m : ℕ} : (x : K) ^ m = 1 ↔ x ^ m = 1 := by
  constructor
  · intro h
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact h)
  · intro h
    rw [← Units.val_pow_eq_pow_val, h, Units.val_one]

theorem add_two_not_dvd_two {r : ℕ} (hr : 3 ≤ r) : ¬ r + 2 ∣ 2 := by
  intro h
  have := Nat.le_of_dvd (by norm_num) h
  omega

theorem add_two_not_dvd_twelve {r : ℕ} (hr : 3 ≤ r) (hodd : r % 2 = 1) : ¬ r + 2 ∣ 12 := by
  intro h
  have h1 : r + 2 ≤ 12 := Nat.le_of_dvd (by norm_num) h
  have h2 : r ≤ 10 := by omega
  interval_cases r <;> first | omega | norm_num at h

theorem exists_setup {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 4 ≤ f) (hfe : Even f) :
    ∃ r : ℕ, 3 ≤ r ∧ r % 2 = 1 ∧ 2 ^ (f / 2) = r + 1 ∧
      ∃ x : Kˣ, (∀ y : Kˣ, ∃ j : ℕ, x ^ j = y) ∧ ∀ n : ℕ, x ^ (r * n) = 1 ↔ (r + 2) ∣ n := by
  have hf2 : f / 2 + f / 2 = f := by
    obtain ⟨k, hk⟩ := hfe
    omega
  have h4 : 4 ≤ 2 ^ (f / 2) := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (f / 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ∣ 2 ^ (f / 2) := dvd_pow_self 2 (by omega)
  obtain ⟨r, hr⟩ : ∃ r : ℕ, 2 ^ (f / 2) = r + 1 := ⟨2 ^ (f / 2) - 1, by omega⟩
  have hr3 : 3 ≤ r := by omega
  have hodd : r % 2 = 1 := by
    rw [hr] at h2
    omega
  have hcard : Nat.card K = (r + 1) * (r + 1) := by
    have hfpow : (2 : ℕ) ^ f = 2 ^ (f / 2) * 2 ^ (f / 2) := by
      rw [← pow_add, hf2]
    rw [hK, hfpow, hr]
  obtain ⟨x, hxgen⟩ := IsCyclic.exists_monoid_generator (α := Kˣ)
  have hord : orderOf x = Nat.card Kˣ :=
    orderOf_eq_card_of_forall_mem_zpowers fun y => mem_powers_iff_mem_zpowers.mp (hxgen y)
  have hcardU : Nat.card Kˣ = r * (r + 2) := by
    rw [Nat.card_units K, hcard]
    have e : (r + 1) * (r + 1) = r * (r + 2) + 1 := by ring
    rw [e, Nat.add_sub_cancel]
  refine ⟨r, hr3, hodd, hr, x, fun y => (Submonoid.mem_powers_iff y x).mp (hxgen y), fun n => ?_⟩
  rw [← orderOf_dvd_iff_pow_eq_one, hord, hcardU,
    Nat.mul_dvd_mul_iff_left (show 0 < r by omega)]

theorem exists_fieldAut_comm_pow_twelve_ne_one {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 4 ≤ f)
    (hfe : Even f) {σ : K ≃+* K} (hσ : ∀ x, σ x = x ^ 2 ^ (f / 2)) :
    ∃ j : projectiveSL 3 K, (fieldAut 3 K σ j * j⁻¹) ^ 12 ≠ 1 := by
  obtain ⟨r, hr3, hodd, hr, x, -, hx⟩ := exists_setup hK hf hfe
  have hσ' : ∀ y : K, σ y = y ^ (r + 1) := fun y => by rw [hσ y, hr]
  have hl : (x : K) ≠ 0 := Units.ne_zero x
  have hDD : diagSL (x : K) (x : K)⁻¹ (mul_inv_cancel₀ hl) *
      diagSL (x : K)⁻¹ (x : K) (inv_mul_cancel₀ hl) = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, coe_diagSL,
      coe_diagSL]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, mul_inv_cancel₀ hl, inv_mul_cancel₀ hl]
  have hinv : (proj 3 K (diagSL (x : K) (x : K)⁻¹ (mul_inv_cancel₀ hl)))⁻¹ =
      proj 3 K (diagSL (x : K)⁻¹ (x : K) (inv_mul_cancel₀ hl)) :=
    inv_proj_eq_of_mul_eq_one hDD
  have hYf : ((Matrix.SpecialLinearGroup.map σ.toRingHom
      (diagSL (x : K) (x : K)⁻¹ (mul_inv_cancel₀ hl)) *
        diagSL (x : K)⁻¹ (x : K) (inv_mul_cancel₀ hl) : Matrix.SpecialLinearGroup (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) =
      !![σ (x : K) * (x : K)⁻¹, 0, 0; 0, σ (x : K)⁻¹ * (x : K), 0; 0, 0, 1] := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.map_apply_coe, coe_diagSL,
      coe_diagSL]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, RingHom.mapMatrix_apply]
  refine ⟨proj 3 K (diagSL (x : K) (x : K)⁻¹ (mul_inv_cancel₀ hl)), ?_⟩
  have hY : fieldAut 3 K σ (proj 3 K (diagSL (x : K) (x : K)⁻¹ (mul_inv_cancel₀ hl))) *
      (proj 3 K (diagSL (x : K) (x : K)⁻¹ (mul_inv_cancel₀ hl)))⁻¹ =
      proj 3 K (Matrix.SpecialLinearGroup.map σ.toRingHom
        (diagSL (x : K) (x : K)⁻¹ (mul_inv_cancel₀ hl)) *
          diagSL (x : K)⁻¹ (x : K) (inv_mul_cancel₀ hl)) := by
    rw [hinv, fieldAut_proj, ← map_mul (proj 3 K)]
  intro h
  rw [hY, ← map_pow (proj 3 K), proj_eq_one_iff, mem_scalars] at h
  obtain ⟨c, -, hc⟩ := h
  rw [Matrix.SpecialLinearGroup.coe_pow, hYf] at hc
  have he2 : !![σ (x : K) * (x : K)⁻¹, 0, 0; 0, σ (x : K)⁻¹ * (x : K), 0; 0, 0, 1] *ᵥ
      ![0, 0, 1] = ![0, 0, 1] := by
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have hc1 : (c : K) = 1 := scalar_eq_one_of_pow_twelve hc he2
  rw [hc1, map_one] at hc
  have hv : !![σ (x : K) * (x : K)⁻¹, 0, 0; 0, σ (x : K)⁻¹ * (x : K), 0; 0, 0, 1] *ᵥ
      ![1, 0, 0] = (σ (x : K) * (x : K)⁻¹) • ![1, 0, 0] := by
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have ha := pow_twelve_eq_one_of_mulVec hc hv (i := 0) (by simp)
  rw [hσ', pow_succ (x : K) r, mul_assoc, mul_inv_cancel₀ hl, mul_one, ← pow_mul] at ha
  exact add_two_not_dvd_twelve hr3 hodd ((hx 12).mp (val_pow_eq_one_iff.mp ha))

theorem exists_fieldAut_mul_dualAut_comm_pow_twelve_ne_one {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (hf : 4 ≤ f) (hfe : Even f) {σ : K ≃+* K} (hσ : ∀ x, σ x = x ^ 2 ^ (f / 2)) :
    ∃ j : projectiveSL 3 K, ((fieldAut 3 K σ * dualAut 3 K) j * j⁻¹) ^ 12 ≠ 1 := by
  obtain ⟨r, hr3, hodd, hr, x, hxgen, hx⟩ := exists_setup hK hf hfe
  have hσ' : ∀ y : K, σ y = y ^ (r + 1) := fun y => by rw [hσ y, hr]
  obtain ⟨U, hUdef⟩ : ∃ U : K, U = (x : K) ^ r := ⟨_, rfl⟩
  have hUiff : ∀ n : ℕ, U ^ n = 1 ↔ (r + 2) ∣ n := fun n => by
    rw [hUdef, ← pow_mul, val_pow_eq_one_iff, hx n]
  have hUs2 : U ^ (r + 2) = 1 := (hUiff _).mpr dvd_rfl
  have hUV : U * U ^ (r + 1) = 1 := by
    calc U * U ^ (r + 1) = U ^ (r + 2) := by ring
      _ = 1 := hUs2
  have hpow_sq : (U ^ (r + 1)) ^ (r + 1) = U := by
    rw [← pow_mul, show (r + 1) * (r + 1) = (r + 2) * r + 1 by ring, pow_succ, pow_mul, hUs2,
      one_pow, one_mul]
  obtain ⟨t, htdef⟩ : ∃ t : K, t = U + U ^ (r + 1) := ⟨_, rfl⟩
  have ht0 : t ≠ 0 := by
    intro h0
    rw [htdef] at h0
    have h' : U * (U + U ^ (r + 1)) = 0 := by rw [h0, mul_zero]
    have hsq : U ^ 2 = 1 := by
      have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
      linear_combination h' - hUV - h2
    exact add_two_not_dvd_two hr3 ((hUiff 2).mp hsq)
  have hσt : σ t = t := by
    rw [htdef, map_add, hσ' U, map_pow, hσ' U, hpow_sq, add_comm]
  have htr : t ^ r = 1 := by
    have h1 : t ^ (r + 1) = t := by
      rw [← hσ' t]
      exact hσt
    have h2' : t ^ r * t = 1 * t := by
      rw [one_mul, ← pow_succ]
      exact h1
    exact mul_right_cancel₀ ht0 h2'
  obtain ⟨j, hj⟩ := hxgen (Units.mk0 t ht0)
  have hTr : (Units.mk0 t ht0) ^ r = 1 :=
    val_pow_eq_one_iff.mp (by rw [Units.val_mk0]; exact htr)
  have hxj : x ^ (r * j) = 1 := by
    rw [mul_comm r j, pow_mul, hj, hTr]
  obtain ⟨m, hm⟩ := (hx j).mp hxj
  have hαpow : ((x ^ m : Kˣ) : K) ^ (r + 2) = t := by
    have h1 : (x ^ m) ^ (r + 2) = Units.mk0 t ht0 := by
      rw [← pow_mul, mul_comm m (r + 2), ← hm, hj]
    rw [← Units.val_pow_eq_pow_val, h1, Units.val_mk0]
  obtain ⟨α, hαt, hα0⟩ : ∃ α : K, α ^ (r + 2) = t ∧ α ≠ 0 :=
    ⟨_, hαpow, Units.ne_zero _⟩
  have hT : σ α * α = U + U ^ (r + 1) := by
    rw [← htdef, hσ' α]
    calc α ^ (r + 1) * α = α ^ (r + 2) := by ring
      _ = t := hαt
  have hg : unipSL α * unipSL α = 1 := unipSL_mul_self α
  have hY : (fieldAut 3 K σ * dualAut 3 K) (proj 3 K (unipSL α)) *
      (proj 3 K (unipSL α))⁻¹ =
      proj 3 K (Matrix.SpecialLinearGroup.map σ.toRingHom (unipSL α).transpose * unipSL α) := by
    rw [MulAut.mul_apply, dualAut_proj, unipSL_inv, fieldAut_proj,
      inv_proj_eq_of_mul_eq_one hg, ← map_mul (proj 3 K)]
  have hMat : ((Matrix.SpecialLinearGroup.map σ.toRingHom (unipSL α).transpose * unipSL α :
      Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![1, α, 0; σ α, 1 + σ α * α, 0; 0, 0, 1] := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.map_apply_coe,
      Matrix.SpecialLinearGroup.coe_transpose, coe_unipSL]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, RingHom.mapMatrix_apply] <;> ring
  refine ⟨proj 3 K (unipSL α), ?_⟩
  intro h
  rw [hY, ← map_pow (proj 3 K), proj_eq_one_iff, mem_scalars] at h
  obtain ⟨c, -, hc⟩ := h
  rw [Matrix.SpecialLinearGroup.coe_pow, hMat] at hc
  have he2 : !![1, α, 0; σ α, 1 + σ α * α, 0; 0, 0, 1] *ᵥ ![0, 0, 1] = ![0, 0, 1] := by
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have hc1 : (c : K) = 1 := scalar_eq_one_of_pow_twelve hc he2
  rw [hc1, map_one] at hc
  have hv := mulVec_unip_eq (CharTwo.two_eq_zero) hT hUV
  have hU12 : U ^ 12 = 1 := pow_twelve_eq_one_of_mulVec hc hv (i := 0) (by simpa using hα0)
  exact add_two_not_dvd_twelve hr3 hodd ((hUiff 12).mp hU12)

end CFSG.RankThree.PartTwo.Sec15.Ronan155DiamondL3
