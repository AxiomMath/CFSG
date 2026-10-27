module

public import CFSG.Quasithin.Background.SmithB42LnL4Rep

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.B42Ln

open Matrix

local notation "𝕄₄" => Matrix (Fin 4) (Fin 4) (ZMod 2)

theorem add_self_mat4 (M : 𝕄₄) : M + M = 0 := by
  ext i j
  simp only [Matrix.add_apply, Matrix.zero_apply]
  generalize M i j = a
  revert a
  decide

theorem mul_self_zmod2' (a : ZMod 2) : a * a = a := by
  revert a
  decide

theorem vecMulVec_mulVec_eq4 (v φ x : Fin 4 → ZMod 2) :
    vecMulVec v φ *ᵥ x = (φ ⬝ᵥ x) • v := by
  ext i
  simp only [mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem exists_dot_eq_one4 : ∀ φ : Fin 4 → ZMod 2, φ ≠ 0 → ∃ x : Fin 4 → ZMod 2, φ ⬝ᵥ x = 1 := by
  decide

theorem vecMulVec_inj4 {v φ v' φ' : Fin 4 → ZMod 2} (hv : v ≠ 0) (hφ : φ ≠ 0) (hv' : v' ≠ 0)
    (h : vecMulVec v φ = vecMulVec v' φ') : v = v' ∧ φ = φ' := by
  obtain ⟨x, hx⟩ := exists_dot_eq_one4 φ hφ
  have h1 := congrArg (· *ᵥ x) h
  simp only [vecMulVec_mulVec_eq4, hx, one_smul] at h1
  have hvv : v = v' := by
    rcases zmod2_eq (φ' ⬝ᵥ x) with h0 | h0
    · rw [h0, zero_smul] at h1
      exact absurd h1 hv
    · rw [h0, one_smul] at h1
      exact h1
  subst hvv
  refine ⟨rfl, ?_⟩
  ext j
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hv (funext hall)
  have h3 := congrFun (congrFun h i) j
  simp only [vecMulVec_apply] at h3
  rcases zmod2_eq (v i) with h0 | h0
  · exact absurd h0 hi
  · rw [h0, one_mul, one_mul] at h3
    exact h3

theorem tv_mul_tv4 (v₁ φ₁ v₂ φ₂ : Fin 4 → ZMod 2) :
    (1 + vecMulVec v₁ φ₁) * (1 + vecMulVec v₂ φ₂) =
      1 + vecMulVec v₁ φ₁ + vecMulVec v₂ φ₂ + (φ₁ ⬝ᵥ v₂) • vecMulVec v₁ φ₂ := by
  rw [add_mul, one_mul, mul_add, mul_one, vecMulVec_mul_vecMulVec]
  have : vecMulVec v₁ ((φ₁ ⬝ᵥ v₂) • φ₂) = (φ₁ ⬝ᵥ v₂) • vecMulVec v₁ φ₂ := by
    ext i j
    simp only [vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply]
    ring
  rw [this]
  abel

section Graph

variable {σ : G4 ≃* G4} {P : GL (Fin 4) (ZMod 2)}

theorem tv_fixed4
    (hσ : ∀ x : G4, ((σ x : G4) : 𝕄₄) =
      (P : 𝕄₄) * ((x⁻¹ : G4) : 𝕄₄)ᵀ * ((P⁻¹ : GL (Fin 4) (ZMod 2)) : 𝕄₄))
    {b : G4} (hb : σ b = b) {v φ : Fin 4 → ZMod 2} (hbm : (b : 𝕄₄) = 1 + vecMulVec v φ)
    (hv : v ≠ 0) (hφ : φ ≠ 0) (hφv : φ ⬝ᵥ v = 0) : v = (P : 𝕄₄) *ᵥ φ := by
  set p : 𝕄₄ := (P : 𝕄₄)
  set q : 𝕄₄ := ((P⁻¹ : GL (Fin 4) (ZMod 2)) : 𝕄₄)
  have hpq : p * q = 1 := GL4_mul_inv P
  have hqp : q * p = 1 := GL4_inv_mul P
  have hb2 : b * b = 1 := by
    apply Subtype.ext
    show (b : 𝕄₄) * (b : 𝕄₄) = 1
    rw [hbm, tv_mul_tv4, hφv, zero_smul, add_zero, add_assoc, add_self_mat4, add_zero]
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have hσb : ((σ b : G4) : 𝕄₄) = 1 + vecMulVec (p *ᵥ φ) (v ᵥ* q) := by
    rw [hσ, hbinv, hbm, transpose_add, transpose_one, transpose_vecMulVec, Matrix.mul_add,
      Matrix.mul_one, Matrix.add_mul, hpq, mul_vecMulVec, vecMulVec_mul]
  have h1 : vecMulVec (p *ᵥ φ) (v ᵥ* q) = vecMulVec v φ := by
    have h2 : (1 : 𝕄₄) + vecMulVec (p *ᵥ φ) (v ᵥ* q) = 1 + vecMulVec v φ := by
      rw [← hσb, ← hbm, hb]
    exact add_left_cancel h2
  have hpφ : p *ᵥ φ ≠ 0 := fun h0 => hφ (by
    have := congrArg (q *ᵥ ·) h0
    simpa [mulVec_mulVec, hqp] using this)
  have hvq : v ᵥ* q ≠ 0 := fun h0 => hv (by
    have := congrArg (· ᵥ* p) h0
    simpa [vecMul_vecMul, hqp] using this)
  exact ((vecMulVec_inj4 hpφ hvq hv h1).1).symm

theorem conj_tv4 (h : G4) (v φ : Fin 4 → ZMod 2) :
    ((h⁻¹ : G4) : 𝕄₄) * (1 + vecMulVec v φ) * (h : 𝕄₄) =
      1 + vecMulVec (((h⁻¹ : G4) : 𝕄₄) *ᵥ v) (φ ᵥ* (h : 𝕄₄)) := by
  have hh : ((h⁻¹ : G4) : 𝕄₄) * (h : 𝕄₄) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, hh, mul_vecMulVec, vecMulVec_mul]

theorem vecMul_injective_of_mul {M M' : 𝕄₄} (h : M * M' = 1) {x y : Fin 4 → ZMod 2}
    (hxy : x ᵥ* M = y ᵥ* M) : x = y := by
  have := congrArg (· ᵥ* M') hxy
  simpa [vecMul_vecMul, h] using this

theorem mulVec_injective_of_mul {M M' : 𝕄₄} (h : M' * M = 1) {x y : Fin 4 → ZMod 2}
    (hxy : M *ᵥ x = M *ᵥ y) : x = y := by
  have := congrArg (M' *ᵥ ·) hxy
  simpa [mulVec_mulVec, h] using this

theorem not_fixed_compat
    (hσ : ∀ x : G4, ((σ x : G4) : 𝕄₄) =
      (P : 𝕄₄) * ((x⁻¹ : G4) : 𝕄₄)ᵀ * ((P⁻¹ : GL (Fin 4) (ZMod 2)) : 𝕄₄))
    (h : G4) {cx cy : Fin 64} (hx : cx ∈ tvL) (hy : cy ∈ tvL) (hxy : cx ≠ cy)
    (hc : up4 cx * up4 cy = up4 cy * up4 cx) (hp : code4 (up4 cx * up4 cy) ∈ tvL)
    (hfx : σ (h⁻¹ * uOf cx * h) = h⁻¹ * uOf cx * h)
    (hfy : σ (h⁻¹ * uOf cy * h) = h⁻¹ * uOf cy * h) : False := by
  obtain ⟨ex, hvx, hφx, hdx⟩ := tvCA_spec cx hx
  obtain ⟨ey, hvy, hφy, hdy⟩ := tvCA_spec cy hy
  have hhi : (h : 𝕄₄) * ((h⁻¹ : G4) : 𝕄₄) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hih : ((h⁻¹ : G4) : 𝕄₄) * (h : 𝕄₄) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have key : ∀ {c : Fin 64}, up4 c = 1 + vecMulVec (tvC c) (tvA c) → tvC c ≠ 0 → tvA c ≠ 0 →
      tvA c ⬝ᵥ tvC c = 0 → σ (h⁻¹ * uOf c * h) = h⁻¹ * uOf c * h →
      ((h⁻¹ : G4) : 𝕄₄) *ᵥ tvC c = (P : 𝕄₄) *ᵥ (tvA c ᵥ* (h : 𝕄₄)) := by
    intro c hec hv hφ hd hfix
    refine tv_fixed4 hσ hfix ?_ ?_ ?_ ?_
    · show ((h⁻¹ : G4) : 𝕄₄) * up4 c * (h : 𝕄₄) = _
      rw [hec, conj_tv4]
    · intro h0
      exact hv (mulVec_injective_of_mul hhi (h0.trans (mulVec_zero _).symm))
    · intro h0
      exact hφ (vecMul_injective_of_mul hhi (h0.trans (zero_vecMul _).symm))
    · rw [dotProduct_mulVec, vecMul_vecMul, hhi, vecMul_one]
      exact hd
  have kx := key ex hvx hφx hdx hfx
  have ky := key ey hvy hφy hdy hfy
  apply hxy
  rw [← code4_up4 cx, ← code4_up4 cy, ex, ey]
  rcases compat_center_or_axis cx hx cy hy hxy hc hp with hv | hφ
  · rw [hv] at kx
    have h1 := mulVec_injective_of_mul (GL4_inv_mul P) (kx.symm.trans ky)
    rw [vecMul_injective_of_mul hhi h1, hv]
  · rw [hφ] at kx
    have h1 := mulVec_injective_of_mul hhi (kx.trans ky.symm)
    rw [h1, hφ]

end Graph

theorem sum_sum_symm4 (f : Fin 4 → Fin 4 → ZMod 2) (hf : ∀ i j, f i j = f j i) :
    ∑ i, ∑ j, f i j = ∑ i, f i i := by
  simp only [Fin.sum_univ_four]
  rw [hf 1 0, hf 2 0, hf 3 0, hf 2 1, hf 3 1, hf 3 2]
  have h2 : (2 : ZMod 2) = 0 := rfl
  linear_combination (f 0 1 + f 0 2 + f 0 3 + f 1 2 + f 1 3 + f 2 3) * h2

theorem dotProduct_mulVec_self4 {M : 𝕄₄} (hM : Mᵀ = M) (x : Fin 4 → ZMod 2) :
    x ⬝ᵥ (M *ᵥ x) = (fun i => M i i) ⬝ᵥ x := by
  have hMs : ∀ i j, M j i = M i j := fun i j => by
    have := congrFun (congrFun hM i) j
    rwa [transpose_apply] at this
  have hf : ∀ i j, x i * (M i j * x j) = x j * (M j i * x i) := fun i j => by
    rw [hMs i j]
    ring
  simp only [dotProduct, mulVec, Finset.mul_sum]
  rw [sum_sum_symm4 _ hf]
  refine Finset.sum_congr rfl fun i _ => ?_
  calc x i * (M i i * x i) = M i i * (x i * x i) := by ring
    _ = M i i * x i := by rw [mul_self_zmod2']

theorem exists_v_ne4 : ∀ d : Fin 4 → ZMod 2, ∃ v : Fin 4 → ZMod 2, v ≠ 0 ∧ d ⬝ᵥ v = 0 := by
  decide

theorem four_le_card_orth (d v : Fin 4 → ZMod 2) :
    4 ≤ Nat.card {ψ : Fin 4 → ZMod 2 // d ⬝ᵥ ψ = 0 ∧ v ⬝ᵥ ψ = 0} := by
  set f : (Fin 4 → ZMod 2) →ₗ[ZMod 2] (Fin 2 → ZMod 2) := (Matrix.of ![d, v]).mulVecLin with hf
  have hker : ∀ ψ, ψ ∈ LinearMap.ker f ↔ d ⬝ᵥ ψ = 0 ∧ v ⬝ᵥ ψ = 0 := by
    intro ψ
    rw [LinearMap.mem_ker, hf, Matrix.mulVecLin_apply]
    constructor
    · intro h
      exact ⟨congrFun h 0, congrFun h 1⟩
    · rintro ⟨h0, h1⟩
      funext i
      fin_cases i
      · exact h0
      · exact h1
  have hrank := LinearMap.finrank_range_add_finrank_ker f
  have hr : Module.finrank (ZMod 2) (LinearMap.range f) ≤ 2 := by
    have := Submodule.finrank_le (LinearMap.range f)
    rwa [Module.finrank_fin_fun] at this
  rw [Module.finrank_fin_fun] at hrank
  have hk : 2 ≤ Module.finrank (ZMod 2) (LinearMap.ker f) := by omega
  have : Fintype (LinearMap.ker f) := Fintype.ofFinite _
  have hcard := Module.card_eq_pow_finrank (K := ZMod 2) (V := LinearMap.ker f)
  rw [ZMod.card, ← Nat.card_eq_fintype_card] at hcard
  have e : ↥(LinearMap.ker f) ≃ {ψ : Fin 4 → ZMod 2 // d ⬝ᵥ ψ = 0 ∧ v ⬝ᵥ ψ = 0} :=
    Equiv.subtypeEquivRight hker
  rw [← Nat.card_congr e, hcard]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ _ := Nat.pow_le_pow_right (by norm_num) hk

theorem exists_orth_ne4 (d v u : Fin 4 → ZMod 2) :
    ∃ ψ : Fin 4 → ZMod 2, ψ ≠ 0 ∧ ψ ≠ u ∧ d ⬝ᵥ ψ = 0 ∧ v ⬝ᵥ ψ = 0 := by
  classical
  by_contra hall'
  have hall : ∀ ψ : Fin 4 → ZMod 2, ψ ≠ 0 → d ⬝ᵥ ψ = 0 → v ⬝ᵥ ψ = 0 → ψ = u :=
    fun ψ h0 hd hv => by_contra fun hne => hall' ⟨ψ, h0, hne, hd, hv⟩
  have hinj : Function.Injective fun ψ : {ψ : Fin 4 → ZMod 2 // d ⬝ᵥ ψ = 0 ∧ v ⬝ᵥ ψ = 0} =>
      decide ((ψ : Fin 4 → ZMod 2) = 0) := by
    intro ψ ψ' h
    by_cases h1 : (ψ : Fin 4 → ZMod 2) = 0 <;> by_cases h1' : (ψ' : Fin 4 → ZMod 2) = 0
    · exact Subtype.ext (h1.trans h1'.symm)
    · simp [h1, h1'] at h
    · simp [h1, h1'] at h
    · exact Subtype.ext ((hall ψ h1 ψ.2.1 ψ.2.2).trans (hall ψ' h1' ψ'.2.1 ψ'.2.2).symm)
  have h2 := Nat.card_le_card_of_injective _ hinj
  have h4 := four_le_card_orth d v
  simp only [Nat.card_eq_fintype_card, Fintype.card_bool] at h2 h4
  omega

theorem exists_conj_mul_inv4 {σ : G4 ≃* G4} {P : GL (Fin 4) (ZMod 2)} (hPs : (P : 𝕄₄)ᵀ = P)
    (hσ : ∀ x : G4, ((σ x : G4) : 𝕄₄) =
      (P : 𝕄₄) * ((x⁻¹ : G4) : 𝕄₄)ᵀ * ((P⁻¹ : GL (Fin 4) (ZMod 2)) : 𝕄₄)) :
    ∃ γ : G4, γ * γ = 1 ∧ σ γ * γ ≠ 1 ∧ σ γ * γ * (σ γ * γ) = 1 := by
  set p : 𝕄₄ := (P : 𝕄₄) with hp
  set q : 𝕄₄ := ((P⁻¹ : GL (Fin 4) (ZMod 2)) : 𝕄₄) with hq
  have hpq : p * q = 1 := GL4_mul_inv P
  have hqp : q * p = 1 := GL4_inv_mul P
  have hqs : qᵀ = q := by
    calc qᵀ = qᵀ * (p * q) := by rw [hpq, Matrix.mul_one]
      _ = (p * q)ᵀ * q := by rw [transpose_mul, hPs, Matrix.mul_assoc]
      _ = q := by rw [hpq, transpose_one, Matrix.one_mul]
  obtain ⟨v, hv0, hvq⟩ := exists_v_ne4 (fun i => q i i)
  obtain ⟨ψ, hψ0, hψq, hdψ, hvψ⟩ := exists_orth_ne4 (fun i => p i i) v (q *ᵥ v)
  have hψv : ψ ⬝ᵥ v = 0 := by rw [dotProduct_comm]; exact hvψ
  have hγ2 : (1 + vecMulVec v ψ) * (1 + vecMulVec v ψ) = 1 := by
    rw [tv_mul_tv4, hψv, zero_smul, add_zero, add_assoc, add_self_mat4, add_zero]
  set γ : G4 := ofMI (1 + vecMulVec v ψ) (1 + vecMulVec v ψ) hγ2 with hγdef
  have hγ : (γ : 𝕄₄) = 1 + vecMulVec v ψ := rfl
  have hγγ : γ * γ = 1 := Subtype.ext hγ2
  have hγinv : γ⁻¹ = γ := inv_eq_of_mul_eq_one_right hγγ
  have hσγ : ((σ γ : G4) : 𝕄₄) = 1 + vecMulVec (p *ᵥ ψ) (v ᵥ* q) := by
    rw [hσ, hγinv, hγ, transpose_add, transpose_one, transpose_vecMulVec, Matrix.mul_add,
      Matrix.mul_one, Matrix.add_mul, hpq, mul_vecMulVec, vecMulVec_mul]
  have hA : (v ᵥ* q) ⬝ᵥ v = 0 := by
    rw [← dotProduct_mulVec, dotProduct_mulVec_self4 hqs]
    exact hvq
  have hB : ψ ⬝ᵥ (p *ᵥ ψ) = 0 := by
    rw [dotProduct_mulVec_self4 hPs]
    exact hdψ
  have hC : (v ᵥ* q) ⬝ᵥ (p *ᵥ ψ) = 0 := by
    rw [dotProduct_mulVec, vecMul_vecMul, hqp, vecMul_one]
    exact hvψ
  have hx : ((σ γ * γ : G4) : 𝕄₄) = 1 + vecMulVec (p *ᵥ ψ) (v ᵥ* q) + vecMulVec v ψ := by
    show ((σ γ : G4) : 𝕄₄) * (γ : 𝕄₄) = _
    rw [hσγ, hγ, tv_mul_tv4, hA, zero_smul, add_zero]
  refine ⟨γ, hγγ, fun h1 => ?_, ?_⟩
  · have h1' := congrArg (fun y : G4 => (y : 𝕄₄)) h1
    simp only [Matrix.SpecialLinearGroup.coe_one] at h1'
    rw [hx] at h1'
    have h3 : vecMulVec (p *ᵥ ψ) (v ᵥ* q) = vecMulVec v ψ := by
      have h4 : vecMulVec (p *ᵥ ψ) (v ᵥ* q) + vecMulVec v ψ = 0 := by
        have h5 : 1 + (vecMulVec (p *ᵥ ψ) (v ᵥ* q) + vecMulVec v ψ) = 1 + 0 := by
          rw [← add_assoc, h1', add_zero]
        exact add_left_cancel h5
      calc vecMulVec (p *ᵥ ψ) (v ᵥ* q) =
          vecMulVec (p *ᵥ ψ) (v ᵥ* q) + (vecMulVec v ψ + vecMulVec v ψ) := by
            rw [add_self_mat4, add_zero]
        _ = vecMulVec v ψ := by rw [← add_assoc, h4, zero_add]
    have hpψ0 : p *ᵥ ψ ≠ 0 := fun h0 => hψ0 (by
      have := congrArg (q *ᵥ ·) h0
      simpa [mulVec_mulVec, hqp] using this)
    have hvq0 : v ᵥ* q ≠ 0 := fun h0 => hv0 (by
      have := congrArg (· ᵥ* p) h0
      simpa [vecMul_vecMul, hqp] using this)
    obtain ⟨h4, -⟩ := vecMulVec_inj4 hpψ0 hvq0 hv0 h3
    apply hψq
    rw [← h4, mulVec_mulVec, hqp, one_mulVec]
  · apply Subtype.ext
    show ((σ γ * γ : G4) : 𝕄₄) * ((σ γ * γ : G4) : 𝕄₄) = 1
    rw [hx]
    set A := vecMulVec (p *ᵥ ψ) (v ᵥ* q)
    set B := vecMulVec v ψ
    have hAA : A * A = 0 := by rw [vecMulVec_mul_vecMulVec, hC, zero_smul, vecMulVec_zero]
    have hAB : A * B = 0 := by rw [vecMulVec_mul_vecMulVec, hA, zero_smul, vecMulVec_zero]
    have hBA : B * A = 0 := by rw [vecMulVec_mul_vecMulVec, hB, zero_smul, vecMulVec_zero]
    have hBB : B * B = 0 := by rw [vecMulVec_mul_vecMulVec, hψv, zero_smul, vecMulVec_zero]
    calc (1 + A + B) * (1 + A + B) = 1 + (A + A) + (B + B) + A * A + A * B + B * A + B * B := by
          noncomm_ring
      _ = 1 := by rw [add_self_mat4, add_self_mat4, hAA, hAB, hBA, hBB]; simp

end CFSG.Quasithin.B42Ln
