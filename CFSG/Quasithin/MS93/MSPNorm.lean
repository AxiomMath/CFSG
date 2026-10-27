module

public import CFSG.Quasithin.Vol2.KGNatSp4Semi
public import CFSG.Quasithin.Vol2.KGNatSemiLin
public import CFSG.Quasithin.MS93.MSPBasic

public section

namespace CFSG.Quasithin.MS93.MSP

open Matrix CFSG.Assembly.LowTwoRank CFSG.Quasithin.Vol2

variable {F : Type} [Field F]

@[expose] def Normalizes (T : V4 F →+ V4 F) : Prop :=
  ∀ g : Sp4 F, ∃ g' : Sp4 F, ∀ v : V4 F, T (mat g *ᵥ v) = mat g' *ᵥ T v

theorem Normalizes.exists_inv [Finite F] {T : V4 F →+ V4 F} (hTb : Function.Bijective T)
    (hT : Normalizes T) (g : Sp4 F) :
    ∃ g'' : Sp4 F, ∀ v : V4 F, T (mat g'' *ᵥ v) = mat g *ᵥ T v := by
  choose φ hφ using hT
  have hinj : Function.Injective φ := by
    intro g₁ g₂ h
    refine ext_mulVec fun v => hTb.1 ?_
    rw [hφ g₁ v, hφ g₂ v, h]
  have : Finite (Sp4 F) := Subtype.finite
  obtain ⟨g'', hg''⟩ := Finite.surjective_of_injective hinj g
  exact ⟨g'', fun v => by rw [hφ, hg'']⟩

theorem exists_semilinear [Finite F] {T : V4 F →+ V4 F} (hTb : Function.Bijective T)
    (hT : Normalizes T) : ∃ σ : F →+* F, ∀ (c : F) (v : V4 F), T (c • v) = σ c • T v := by
  let e := AddEquiv.ofBijective T hTb
  have hS : ∀ c : F, ∃ s : F, ∀ w : V4 F, T (c • e.symm w) = s • w := by
    intro c
    let S : V4 F →+ V4 F :=
      { toFun := fun w => T (c • e.symm w)
        map_zero' := by simp
        map_add' := fun w w' => by simp [smul_add] }
    refine KGNat.commutant_statedSp S fun γ x => ?_
    rw [KGNat.linModelNat_lin, KGNat.linModelNat_lin]
    obtain ⟨g'', hg''⟩ := hT.exists_inv hTb γ
    change T (c • e.symm (mat γ *ᵥ x)) = mat γ *ᵥ T (c • e.symm x)
    have h1 : e.symm (mat γ *ᵥ x) = mat g'' *ᵥ e.symm x := by
      refine e.injective ?_
      rw [AddEquiv.apply_symm_apply]
      change mat γ *ᵥ x = T (mat g'' *ᵥ e.symm x)
      rw [hg'']
      congr 1
      exact (e.apply_symm_apply x).symm
    rw [h1, ← mulVec_smul, hg'']
  choose s hs using hS
  have hTs : ∀ c v, T (c • v) = s c • T v := fun c v => by
    have := hs c (T v)
    rwa [show e.symm (T v) = v from e.symm_apply_apply v] at this
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : V4 F, w₀ ≠ 0 := ⟨Pi.single (.inl 0) 1, fun h => by
    simpa using congrFun h (.inl 0)⟩
  obtain ⟨v₀, rfl⟩ := hTb.2 w₀
  have hcancel : ∀ a b : F, a • T v₀ = b • T v₀ → a = b := fun a b h => by
    have := sub_eq_zero.2 h
    rw [← sub_smul] at this
    exact sub_eq_zero.1 ((smul_eq_zero.1 this).resolve_right hw₀)
  refine ⟨{ toFun := s, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hTs⟩
  · exact hcancel _ _ (by rw [← hTs, one_smul, one_smul])
  · intro a b
    exact hcancel _ _ (by rw [← hTs, mul_smul, hTs, hTs, smul_smul])
  · exact hcancel _ _ (by rw [← hTs, zero_smul, zero_smul, map_zero])
  · intro a b
    exact hcancel _ _ (by rw [← hTs, add_smul, map_add, hTs, hTs, add_smul])

theorem exists_similitude [Finite F] {T : V4 F →+ V4 F} (hT : Normalizes T) {σ : F →+* F}
    (hσ : ∀ (c : F) (v : V4 F), T (c • v) = σ c • T v) :
    ∃ c : F, ∀ u v : V4 F, form F (T u) (T v) = c * σ (form F u v) := by
  have hσbij : Function.Bijective σ := ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩
  set e := RingEquiv.ofBijective σ hσbij with he
  set τ : F →+* F := e.symm.toRingHom with hτ
  have hστ : ∀ c, σ (τ c) = c := fun c => e.apply_symm_apply c
  have hτσ : ∀ c, τ (σ c) = c := fun c => e.symm_apply_apply c
  let L : V4 F →ₗ[F] V4 F :=
    { toFun := fun x => T (τ ∘ x)
      map_add' := fun x y => by
        rw [← map_add]
        congr 1
        funext i
        simp [map_add]
      map_smul' := fun c x => by
        have h1 : τ ∘ (c • x) = τ c • (τ ∘ x) := by
          funext i
          simp [map_mul]
        change T (τ ∘ (c • x)) = c • T (τ ∘ x)
        rw [h1, hσ, hστ] }
  have hLx : ∀ x, L x = T (τ ∘ x) := fun x => rfl
  have hLN : ∀ γ : Sp4 F, ∃ γ' : Sp4 F, ∀ x, L (mat γ *ᵥ x) = mat γ' *ᵥ L x := by
    intro γ
    obtain ⟨γ', hγ'⟩ := hT ⟨_, KGNat.map_mem_statedSp τ γ.2⟩
    refine ⟨γ', fun x => ?_⟩
    rw [hLx, hLx]
    have h1 : τ ∘ (mat γ *ᵥ x) = mat ⟨_, KGNat.map_mem_statedSp τ γ.2⟩ *ᵥ (τ ∘ x) := by
      funext i
      exact RingHom.map_mulVec τ _ x i
    rw [h1, hγ']
  obtain ⟨c, hc⟩ := KGNat.exists_similitude L hLN
  have hTL : ∀ v, T v = L (σ ∘ v) := fun v => by
    rw [hLx]
    congr 1
    funext i
    simp [hτσ]
  refine ⟨c, fun u v => ?_⟩
  rw [hTL u, hTL v]
  change Matrix.toBilin' (KGNat.spJ F) (L _) (L _) = c * σ (Matrix.toBilin' (KGNat.spJ F) u v)
  rw [hc, KGNat.spB_map]

theorem eq_one_of_smul_mem [CharP F 2] {g : Sp4 F} {ν : F} (hg : ∀ v : V4 F, mat g *ᵥ v = ν • v) :
    ν = 1 := by
  have h := form_mat g (Pi.single (.inl 0) 1) (Pi.single (.inr 0) 1)
  rw [hg, hg, map_smul, map_smul, LinearMap.smul_apply, form_apply] at h
  simp only [Pi.single_apply, smul_eq_mul] at h
  norm_num at h
  have h2 : (ν - 1) ^ 2 = 0 := by
    have h2z : (2 : F) = 0 := CharTwo.two_eq_zero
    linear_combination h + (1 - ν) * h2z
  exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2)

theorem exists_eq_smul_mat [Finite F] [CharP F 2] {T : V4 F →+ V4 F}
    (hTb : Function.Bijective T) (hT : Normalizes T)
    (hlin : ∀ (c : F) (v : V4 F), T (c • v) = c • T v) :
    ∃ (μ : F) (g : Sp4 F), μ ≠ 0 ∧ ∀ v : V4 F, T v = μ • (mat g *ᵥ v) := by
  obtain ⟨c, hc⟩ := exists_similitude hT (σ := RingHom.id F) hlin
  simp only [RingHom.id_apply] at hc
  have hc0 : c ≠ 0 := by
    rintro rfl
    obtain ⟨u, hu⟩ := hTb.2 (Pi.single (.inl 0) 1)
    obtain ⟨w, hw⟩ := hTb.2 (Pi.single (.inr 0) 1)
    have := hc u w
    rw [hu, hw, zero_mul, form_apply] at this
    simp at this
  set μ := (frobeniusEquiv F 2).symm c with hμ
  have hμ2 : μ ^ 2 = c := frobeniusEquiv_symm_pow_p F 2 c
  have hμ0 : μ ≠ 0 := fun h => hc0 (by rw [← hμ2, h, zero_pow two_ne_zero])
  let T' : V4 F →ₗ[F] V4 F :=
    { toFun := fun v => μ⁻¹ • T v
      map_add' := fun u v => by rw [map_add, smul_add]
      map_smul' := fun a v => by rw [hlin, smul_comm]; rfl }
  have hT'b : Function.Bijective T' :=
    ⟨fun u v h => hTb.1 (smul_right_injective _ (inv_ne_zero hμ0) h), fun w => by
      obtain ⟨u, hu⟩ := hTb.2 (μ • w)
      exact ⟨u, by change μ⁻¹ • T u = w; rw [hu, smul_smul, inv_mul_cancel₀ hμ0, one_smul]⟩⟩
  let e := LinearEquiv.ofBijective T' hT'b
  have hiso : ∀ u v, form F (LinearMap.toMatrix' T' *ᵥ u) (LinearMap.toMatrix' T' *ᵥ v) =
      form F u v := by
    intro u v
    rw [LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec]
    change form F (μ⁻¹ • T u) (μ⁻¹ • T v) = _
    rw [map_smul, map_smul, LinearMap.smul_apply, hc, smul_eq_mul, smul_eq_mul, ← hμ2]
    field_simp
  have h1 : LinearMap.toMatrix' T' * LinearMap.toMatrix' e.symm.toLinearMap = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    have : T' ∘ₗ e.symm.toLinearMap = LinearMap.id := LinearMap.ext fun v => e.apply_symm_apply v
    rw [this, LinearMap.toMatrix'_id]
  have h2 : LinearMap.toMatrix' e.symm.toLinearMap * LinearMap.toMatrix' T' = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    have : e.symm.toLinearMap ∘ₗ T' = LinearMap.id := LinearMap.ext fun v => e.symm_apply_apply v
    rw [this, LinearMap.toMatrix'_id]
  refine ⟨μ, ofMat _ _ h1 h2 hiso, hμ0, fun v => ?_⟩
  rw [mat_ofMat, LinearMap.toMatrix'_mulVec]
  change T v = μ • (μ⁻¹ • T v)
  rw [smul_smul, mul_inv_cancel₀ hμ0, one_smul]

theorem iterate_smul_mat {T : V4 F →+ V4 F} {μ : F} {g : Sp4 F}
    (hT : ∀ v : V4 F, T v = μ • (mat g *ᵥ v)) (k : ℕ) (v : V4 F) :
    T^[k] v = μ ^ k • (mat (g ^ k) *ᵥ v) := by
  induction k with
  | zero => simp [mat_one]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, hT, mulVec_smul, smul_smul, pow_succ, pow_succ',
      mat_mul_mulVec, mul_comm]

theorem exists_eq_mat_of_two_power [Finite F] [CharP F 2] {T : V4 F →+ V4 F}
    (hTb : Function.Bijective T) (hT : Normalizes T)
    (hlin : ∀ (c : F) (v : V4 F), T (c • v) = c • T v) {m : ℕ}
    (hm : ∀ v : V4 F, T^[2 ^ m] v = v) : ∃ g : Sp4 F, ∀ v : V4 F, T v = mat g *ᵥ v := by
  obtain ⟨μ, g, hμ0, hTg⟩ := exists_eq_smul_mat hTb hT hlin
  have hpow : ∀ v : V4 F, mat (g ^ 2 ^ m) *ᵥ v = (μ ^ 2 ^ m)⁻¹ • v := fun v => by
    have := hm v
    rw [iterate_smul_mat hTg] at this
    have hμm : μ ^ 2 ^ m ≠ 0 := pow_ne_zero _ hμ0
    calc mat (g ^ 2 ^ m) *ᵥ v = (μ ^ 2 ^ m)⁻¹ • (μ ^ 2 ^ m • (mat (g ^ 2 ^ m) *ᵥ v)) := by
          rw [smul_smul, inv_mul_cancel₀ hμm, one_smul]
      _ = (μ ^ 2 ^ m)⁻¹ • v := by rw [this]
  have hν := eq_one_of_smul_mem hpow
  have hμ1 : μ ^ 2 ^ m = 1 := by
    rw [inv_eq_one] at hν
    exact hν
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hμ : μ = 1 := by
    have h := sub_pow_char_pow (p := 2) μ 1 m
    rw [hμ1, one_pow, sub_self] at h
    exact sub_eq_zero.1 (pow_eq_zero_iff (pow_ne_zero _ two_ne_zero) |>.1 h)
  exact ⟨g, fun v => by rw [hTg, hμ, one_smul]⟩

theorem semilinear_eq_id_of_fix {T : V4 F →+ V4 F} {σ : F →+* F}
    (hσ : ∀ (c : F) (v : V4 F), T (c • v) = σ c • T v) {v : V4 F} (hv : v ≠ 0)
    (hfix : ∀ c : F, T (c • v) = c • v) : ∀ c : F, σ c = c := by
  intro c
  have h1 := hσ c v
  rw [hfix, show T v = v by simpa using hfix 1] at h1
  have := sub_eq_zero.2 h1
  rw [← sub_smul] at this
  exact (sub_eq_zero.1 ((smul_eq_zero.1 this).resolve_right hv)).symm

theorem card_fixAdd_sq_le [Finite F] {T : V4 F →+ V4 F} {σ : F →+* F}
    (hσ : ∀ (c : F) (v : V4 F), T (c • v) = σ c • T v) (hne : ∃ c : F, σ c ≠ c) :
    Nat.card (KGNat.fixAdd T) ^ 2 ≤ Nat.card (V4 F) := by
  by_contra h
  push Not at h
  obtain ⟨c, hc⟩ := hne
  exact hc (KGNat.semilinear_eq_id_of_card_fix hσ h c)

end CFSG.Quasithin.MS93.MSP
