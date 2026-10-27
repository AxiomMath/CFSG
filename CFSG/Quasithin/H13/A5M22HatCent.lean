module

public import CFSG.Quasithin.Background.HStandard

public section

namespace CFSG.Quasithin.H13.A5.M22Hat

open CFSG.Quasithin CFSG.Quasithin.H
open scoped Matrix

variable {K : Type} [Field K]

theorem two_eq_zero_of_card [Finite K] (hK : Nat.card K = 4) : (2 : K) = 0 := by
  have := Fintype.ofFinite K
  have h := FiniteField.cast_card_eq_zero K
  rw [← Nat.card_eq_fintype_card, hK] at h
  have h4 : (2 : K) * 2 = 0 := by
    rw [← h]
    norm_num
  exact mul_self_eq_zero.mp h4

theorem exists_omega [Finite K] (hK : Nat.card K = 4) :
    ∃ ω : K, ω ≠ 1 ∧ ω ^ 3 = 1 ∧ ω ^ 2 + ω + 1 = 0 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := Fintype.ofFinite Kˣ
  have h3 : 3 ∣ Fintype.card Kˣ := by
    rw [← Nat.card_eq_fintype_card, Nat.card_units, hK]
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card 3 h3
  have hu3 : u ^ 3 = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
  have hω3 : (u : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hu3, Units.val_one]
  have hω1 : (u : K) ≠ 1 := by
    intro h
    have : u = 1 := Units.ext h
    rw [this, orderOf_one] at hu
    omega
  refine ⟨u, hω1, hω3, ?_⟩
  have h : ((u : K) - 1) * ((u : K) ^ 2 + u + 1) = 0 := by
    linear_combination hω3
  rcases mul_eq_zero.mp h with h | h
  · exact absurd (sub_eq_zero.mp h) hω1
  · exact h

@[expose] def eig (M : Matrix (Fin 6) (Fin 6) K) (μ : K) : Submodule K (Fin 6 → K) :=
  LinearMap.ker (M.mulVecLin - μ • LinearMap.id)

theorem mem_eig {M : Matrix (Fin 6) (Fin 6) K} {μ : K} {w : Fin 6 → K} :
    w ∈ eig M μ ↔ M *ᵥ w = μ • w := by
  rw [eig, LinearMap.mem_ker, LinearMap.sub_apply, Matrix.mulVecLin_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]

@[expose] def proj (M : Matrix (Fin 6) (Fin 6) K) (μ : K) : (Fin 6 → K) →ₗ[K] (Fin 6 → K) :=
  LinearMap.id + μ ^ 2 • M.mulVecLin + μ • (M * M).mulVecLin

theorem proj_apply (M : Matrix (Fin 6) (Fin 6) K) (μ : K) (w : Fin 6 → K) :
    proj M μ w = w + μ ^ 2 • (M *ᵥ w) + μ • (M *ᵥ (M *ᵥ w)) := by
  simp [proj, Matrix.mulVec_mulVec]

theorem proj_mem {M : Matrix (Fin 6) (Fin 6) K} (hM : M * M * M = 1) {μ : K} (hμ : μ ^ 3 = 1)
    (w : Fin 6 → K) : proj M μ w ∈ eig M μ := by
  rw [mem_eig, proj_apply]
  have h3 : M *ᵥ (M *ᵥ (M *ᵥ w)) = w := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM, Matrix.one_mulVec]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, h3]
  linear_combination (norm := module) (-hμ) • (M *ᵥ w)

theorem proj_of_mem {M : Matrix (Fin 6) (Fin 6) K} {μ ν : K} {w : Fin 6 → K}
    (hw : w ∈ eig M ν) : proj M μ w = (1 + μ ^ 2 * ν + μ * ν ^ 2) • w := by
  rw [mem_eig] at hw
  rw [proj_apply, hw, Matrix.mulVec_smul, hw]
  module

section Decomp

variable {M : Matrix (Fin 6) (Fin 6) K} {ω : K}

theorem eq_sum_proj (h2 : (2 : K) = 0) (hω : ω ^ 2 + ω + 1 = 0) (w : Fin 6 → K) :
    w = proj M 1 w + proj M ω w + proj M (ω ^ 2) w := by
  rw [proj_apply, proj_apply, proj_apply]
  linear_combination (norm := module) -(h2 • w) - ((ω ^ 2 - ω + 1) * hω) • (M *ᵥ w) -
    hω • (M *ᵥ (M *ᵥ w))

theorem proj_sum_of_mem (h2 : (2 : K) = 0) (hω : ω ^ 2 + ω + 1 = 0) {a b c : Fin 6 → K}
    (ha : a ∈ eig M 1) (hb : b ∈ eig M ω) (hc : c ∈ eig M (ω ^ 2)) :
    proj M 1 (a + (b + c)) = a ∧ proj M ω (a + (b + c)) = b ∧
      proj M (ω ^ 2) (a + (b + c)) = c := by
  simp only [map_add, proj_of_mem ha, proj_of_mem hb, proj_of_mem hc]
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (norm := module) h2 • a + hω • b + ((ω ^ 2 - ω + 1) * hω) • c
  · linear_combination (norm := module) hω • a + (ω ^ 3 * h2) • b + ((ω ^ 3 - ω + 1) * hω) • c
  · linear_combination (norm := module) ((ω ^ 2 - ω + 1) * hω) • a +
      ((ω ^ 3 - ω + 1) * hω) • b + (ω ^ 6 * h2) • c

theorem finrank_eig_add (h2 : (2 : K) = 0) (hω : ω ^ 2 + ω + 1 = 0) (hω3 : ω ^ 3 = 1)
    (hM : M * M * M = 1) :
    Module.finrank K (eig M 1) + Module.finrank K (eig M ω) +
      Module.finrank K (eig M (ω ^ 2)) = 6 := by
  have hω6 : (ω ^ 2) ^ 3 = 1 := by rw [← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, hω3,
    one_pow]
  let Φ : ↥(eig M 1) × ↥(eig M ω) × ↥(eig M (ω ^ 2)) →ₗ[K] (Fin 6 → K) :=
    (eig M 1).subtype.coprod ((eig M ω).subtype.coprod (eig M (ω ^ 2)).subtype)
  have hΦ : ∀ x, Φ x = (x.1 : Fin 6 → K) + ((x.2.1 : Fin 6 → K) + x.2.2) := fun x => rfl
  have hinj : Function.Injective Φ := by
    intro x y hxy
    rw [hΦ, hΦ] at hxy
    obtain ⟨h1, h2', h3⟩ := proj_sum_of_mem h2 hω x.1.2 x.2.1.2 x.2.2.2
    obtain ⟨h1', h2'', h3'⟩ := proj_sum_of_mem h2 hω y.1.2 y.2.1.2 y.2.2.2
    rw [hxy] at h1 h2' h3
    exact Prod.ext (Subtype.ext (h1.symm.trans h1'))
      (Prod.ext (Subtype.ext (h2'.symm.trans h2'')) (Subtype.ext (h3.symm.trans h3')))
  have hsurj : Function.Surjective Φ := fun w =>
    ⟨(⟨proj M 1 w, proj_mem hM (one_pow 3) w⟩, ⟨proj M ω w, proj_mem hM hω3 w⟩,
      ⟨proj M (ω ^ 2) w, proj_mem hM hω6 w⟩), by
        rw [hΦ, ← add_assoc]
        exact (eq_sum_proj h2 hω w).symm⟩
  have e := LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩
  have h := e.finrank_eq
  rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_fin_fun] at h
  omega

end Decomp

theorem mulVec_mem_eig {A M : Matrix (Fin 6) (Fin 6) K} (hAM : A * M = M * A) {μ : K}
    {w : Fin 6 → K} (hw : w ∈ eig M μ) : A *ᵥ w ∈ eig M μ := by
  rw [mem_eig] at hw ⊢
  rw [Matrix.mulVec_mulVec, ← hAM, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_smul]

section Group

variable {Γ₀ : Subgroup (GL (Fin 6) K)}

abbrev mat (γ : ↥Γ₀) : Matrix (Fin 6) (Fin 6) K := ((γ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)

theorem mat_mul (γ δ : ↥Γ₀) : mat (γ * δ) = mat γ * mat δ := rfl

theorem mat_one : mat (1 : ↥Γ₀) = 1 := rfl

theorem mat_pow (γ : ↥Γ₀) (k : ℕ) : mat (γ ^ k) = mat γ ^ k := by
  rw [mat, Subgroup.coe_pow, Units.val_pow_eq_pow_val]

theorem mat_mulVec_inv (γ : ↥Γ₀) (w : Fin 6 → K) : mat γ⁻¹ *ᵥ (mat γ *ᵥ w) = w := by
  rw [Matrix.mulVec_mulVec, ← mat_mul, inv_mul_cancel, mat_one, Matrix.one_mulVec]

theorem mat_mulVec_inv' (γ : ↥Γ₀) (w : Fin 6 → K) : mat γ *ᵥ (mat γ⁻¹ *ᵥ w) = w := by
  rw [Matrix.mulVec_mulVec, ← mat_mul, mul_inv_cancel, mat_one, Matrix.one_mulVec]

theorem eq_one_of_mulVec {γ : ↥Γ₀} (h : ∀ w, mat γ *ᵥ w = w) : γ = 1 := by
  have hM : mat γ = 1 := Matrix.ext_of_mulVec_single fun j => by rw [h, Matrix.one_mulVec]
  exact Subtype.ext (Units.ext hM)

theorem det_restrict_eq_one (hperf : commutator ↥Γ₀ = ⊤) (E : Submodule K (Fin 6 → K))
    (hE : ∀ γ : ↥Γ₀, ∀ w ∈ E, mat γ *ᵥ w ∈ E) (γ : ↥Γ₀) :
    LinearMap.det ((mat γ).mulVecLin.restrict (hE γ)) = 1 := by
  let χ : ↥Γ₀ →* K :=
    { toFun := fun γ => LinearMap.det ((mat γ).mulVecLin.restrict (hE γ))
      map_one' := by
        have : (mat (1 : ↥Γ₀)).mulVecLin.restrict (hE 1) = LinearMap.id :=
          LinearMap.ext fun x => Subtype.ext (by simp [mat_one])
        simp only [this, LinearMap.det_id]
      map_mul' := fun γ δ => by
        have : (mat (γ * δ)).mulVecLin.restrict (hE (γ * δ)) =
            (mat γ).mulVecLin.restrict (hE γ) * (mat δ).mulVecLin.restrict (hE δ) :=
          LinearMap.ext fun x => Subtype.ext (by
            change mat (γ * δ) *ᵥ (x : Fin 6 → K) = mat γ *ᵥ (mat δ *ᵥ (x : Fin 6 → K))
            rw [mat_mul, Matrix.mulVec_mulVec])
        simp only [this, map_mul] }
  have hker := Abelianization.commutator_subset_ker χ.toHomUnits
  rw [hperf] at hker
  have h1 : χ.toHomUnits γ = 1 := hker (Subgroup.mem_top γ)
  have h2 := congrArg Units.val h1
  rwa [MonoidHom.coe_toHomUnits, Units.val_one] at h2

theorem card_modEq_fix {α : Type*} [Finite α] (σ : Equiv.Perm α) (h : σ ^ 11 = 1) :
    Nat.card α ≡ Nat.card {x // σ x = x} [MOD 11] := by
  classical
  have := Fintype.ofFinite α
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have h' : σ ^ 11 ^ 1 = 1 := by rw [pow_one]; exact h
  have hc := Equiv.Perm.card_compl_support_modEq h'
  have e : (σ.supportᶜ : Finset α).card = Nat.card {x // σ x = x} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext x
    simp [Equiv.Perm.mem_support]
  rw [Nat.card_eq_fintype_card, ← e]
  exact hc.symm

theorem mulVec_eq_of_orderOf_eleven [Finite K] (hK : Nat.card K = 4) (E : Submodule K (Fin 6 → K))
    (hE : ∀ γ : ↥Γ₀, ∀ w ∈ E, mat γ *ᵥ w ∈ E) {γ : ↥Γ₀} (hγ : γ ^ 11 = 1)
    (hd : Module.finrank K E ≤ 4) : ∀ w ∈ E, mat γ *ᵥ w = w := by
  let σ : Equiv.Perm ↥E :=
    { toFun := fun x => ⟨mat γ *ᵥ x, hE γ x x.2⟩
      invFun := fun x => ⟨mat γ⁻¹ *ᵥ x, hE γ⁻¹ x x.2⟩
      left_inv := fun x => Subtype.ext (mat_mulVec_inv γ x)
      right_inv := fun x => Subtype.ext (mat_mulVec_inv' γ x) }
  have hpow : ∀ (k : ℕ) (x : ↥E), (((σ ^ k) x : ↥E) : Fin 6 → K) = mat (γ ^ k) *ᵥ x := by
    intro k
    induction k with
    | zero => intro x; simp [mat_one]
    | succ k ih =>
      intro x
      rw [pow_succ', Equiv.Perm.mul_apply, pow_succ', mat_mul, ← Matrix.mulVec_mulVec, ← ih]
      rfl
  have hσ : σ ^ 11 = 1 := Equiv.ext fun x => Subtype.ext (by
    rw [hpow, hγ, mat_one, Matrix.one_mulVec]
    rfl)
  have hmod := card_modEq_fix σ hσ
  let F : Submodule K (Fin 6 → K) := E ⊓ eig (mat γ) 1
  have hF : Nat.card {x // σ x = x} = Nat.card ↥F := by
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1.1, x.1.2, mem_eig.2 (by
          rw [one_smul]; exact congrArg Subtype.val x.2)⟩
        invFun := fun x => ⟨⟨x.1, x.2.1⟩, Subtype.ext (by
          have := mem_eig.1 x.2.2
          rw [one_smul] at this
          exact this)⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }
  rw [hF, Module.natCard_eq_pow_finrank (K := K) (V := ↥E),
    Module.natCard_eq_pow_finrank (K := K) (V := ↥F), hK] at hmod
  have hle : Module.finrank K F ≤ Module.finrank K E := Submodule.finrank_mono inf_le_left
  have key : ∀ d < 5, ∀ e < 5, e ≤ d → 4 ^ d % 11 = 4 ^ e % 11 → e = d := by decide
  have heq : Module.finrank K F = Module.finrank K E :=
    key _ (by omega) _ (by omega) hle hmod
  have hFE : F = E := Submodule.eq_of_le_of_finrank_eq inf_le_left heq
  intro w hw
  have : w ∈ F := by rw [hFE]; exact hw
  have := mem_eig.1 this.2
  rwa [one_smul] at this

theorem eig_one_eq_bot [Finite K] (hK : Nat.card K = 4) (hperf : commutator ↥Γ₀ = ⊤)
    {z : ↥Γ₀} (hz : z ∈ Subgroup.center ↥Γ₀) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) {g : ↥Γ₀}
    (hg : orderOf g = 11) : eig (mat z) 1 = ⊥ := by
  have h2 := two_eq_zero_of_card hK
  obtain ⟨ω, hω1, hω3, hω⟩ := exists_omega hK
  have hω6 : (ω ^ 2) ^ 3 = 1 := by
    rw [← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, hω3, one_pow]
  have hM : mat z * mat z * mat z = 1 := by
    have h : mat z ^ 3 = 1 := by rw [← mat_pow, hz3, mat_one]
    rwa [pow_three'] at h
  have hcomm : ∀ γ : ↥Γ₀, mat γ * mat z = mat z * mat γ := fun γ => by
    rw [← mat_mul, ← mat_mul, Subgroup.mem_center_iff.mp hz γ]
  have hinv : ∀ μ : K, ∀ γ : ↥Γ₀, ∀ w ∈ eig (mat z) μ, mat γ *ᵥ w ∈ eig (mat z) μ :=
    fun μ γ w hw => mulVec_mem_eig (hcomm γ) hw
  have hdet : ∀ μ : K, μ ^ Module.finrank K (eig (mat z) μ) = 1 := by
    intro μ
    have h := det_restrict_eq_one hperf (eig (mat z) μ) (hinv μ) z
    have hres : (mat z).mulVecLin.restrict (hinv μ z) = μ • LinearMap.id :=
      LinearMap.ext fun x => Subtype.ext (by
        change mat z *ᵥ (x : Fin 6 → K) = μ • (x : Fin 6 → K)
        exact mem_eig.1 x.2)
    rwa [hres, LinearMap.det_smul, LinearMap.det_id, mul_one] at h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hordω : orderOf ω = 3 := orderOf_eq_prime hω3 hω1
  have h3ω : 3 ∣ Module.finrank K (eig (mat z) ω) := hordω ▸ orderOf_dvd_of_pow_eq_one (hdet ω)
  have h3ω2 : 3 ∣ Module.finrank K (eig (mat z) (ω ^ 2)) := by
    have h := hdet (ω ^ 2)
    rw [← pow_mul] at h
    have h' : 3 ∣ 2 * Module.finrank K (eig (mat z) (ω ^ 2)) :=
      hordω ▸ orderOf_dvd_of_pow_eq_one h
    omega
  have hsum := finrank_eig_add h2 hω hω3 hM
  have htriv : ∀ γ : ↥Γ₀, (∀ w ∈ eig (mat z) 1, mat γ *ᵥ w = w) →
      (∀ w ∈ eig (mat z) ω, mat γ *ᵥ w = w) → (∀ w ∈ eig (mat z) (ω ^ 2), mat γ *ᵥ w = w) →
      γ = 1 := by
    intro γ h₁ h₂ h₃
    refine eq_one_of_mulVec fun w => ?_
    rw [eq_sum_proj (M := mat z) h2 hω w, Matrix.mulVec_add, Matrix.mulVec_add,
      h₁ _ (proj_mem hM (one_pow 3) w), h₂ _ (proj_mem hM hω3 w), h₃ _ (proj_mem hM hω6 w)]
  have hbot : ∀ {μ : K}, Module.finrank K (eig (mat z) μ) = 0 → ∀ γ : ↥Γ₀,
      ∀ w ∈ eig (mat z) μ, mat γ *ᵥ w = w := fun {μ} h γ w hw => by
    rw [Submodule.finrank_eq_zero.mp h] at hw
    rw [(Submodule.mem_bot K).mp hw, Matrix.mulVec_zero]
  by_contra hne
  have hd1 : Module.finrank K (eig (mat z) 1) ≠ 0 := fun h => hne (Submodule.finrank_eq_zero.mp h)
  rcases (by omega : (Module.finrank K (eig (mat z) ω) = 0 ∧
      Module.finrank K (eig (mat z) (ω ^ 2)) = 0) ∨
    (Module.finrank K (eig (mat z) 1) ≤ 4 ∧ Module.finrank K (eig (mat z) ω) ≤ 4 ∧
      Module.finrank K (eig (mat z) (ω ^ 2)) ≤ 4)) with ⟨h0, h0'⟩ | ⟨ha, hb, hc⟩
  · refine hz1 (htriv z (fun w hw => ?_) (hbot h0 z) (hbot h0' z))
    rw [mem_eig, one_smul] at hw
    exact hw
  · have hg11 : g ^ 11 = 1 := hg ▸ pow_orderOf_eq_one g
    have hg1 : g = 1 := htriv g (mulVec_eq_of_orderOf_eleven hK _ (hinv 1) hg11 ha)
      (mulVec_eq_of_orderOf_eleven hK _ (hinv ω) hg11 hb)
      (mulVec_eq_of_orderOf_eleven hK _ (hinv (ω ^ 2)) hg11 hc)
    rw [hg1, orderOf_one] at hg
    omega

theorem fixV_natAut_eq_bot [Finite K] (hK : Nat.card K = 4) (hperf : commutator ↥Γ₀ = ⊤)
    {z : ↥Γ₀} (hz : z ∈ Subgroup.center ↥Γ₀) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) {g : ↥Γ₀}
    (hg : orderOf g = 11) : fixV (Subgroup.zpowers (natAut Γ₀ z)) = ⊥ := by
  rw [eq_bot_iff]
  intro w hw
  rw [Subgroup.mem_bot]
  have h1 : natAut Γ₀ z w = w := hw _ (Subgroup.mem_zpowers _)
  have h2 : Multiplicative.toAdd w ∈ eig (mat z) 1 := by
    rw [mem_eig, one_smul]
    exact congrArg Multiplicative.toAdd h1
  rw [eig_one_eq_bot hK hperf hz hz3 hz1 hg] at h2
  exact congrArg Multiplicative.ofAdd ((Submodule.mem_bot K).mp h2)

end Group

end CFSG.Quasithin.H13.A5.M22Hat
