module

public import CFSG.Quasithin.Vol2.KGNatReal

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.Quasithin

variable {D : FFModel} {K M : Type} [Field K] [AddCommGroup M] [Module K M]
  {W : Type*} [CommGroup W] {LM : LinModel D K M} {H : Subgroup (MulAut W)} {Z : Subgroup W}
  {π : D.Gam →* ↥H} {f : W → M}

namespace IsCoord

variable (hf : IsCoord LM H Z π f)
include hf

@[expose] noncomputable def autMap (τ : MulAut W) (hτ : ∀ z ∈ Z, τ z ∈ Z) : M →+ M :=
  hf.inducedMap (τ : W →* W) hτ

theorem autMap_apply (τ : MulAut W) (hτ : ∀ z ∈ Z, τ z ∈ Z) (w : W) :
    hf.autMap τ hτ (f w) = f (τ w) :=
  hf.inducedMap_apply (τ : W →* W) hτ w

theorem autMap_lin (τ : MulAut W) (hτ : ∀ z ∈ Z, τ z ∈ Z) (γ γ' : D.Gam)
    (h : τ * ((π γ' : ↥H) : MulAut W) * τ⁻¹ = ((π γ : ↥H) : MulAut W)) (x : M) :
    hf.autMap τ hτ (LM.lin γ' x) = LM.lin γ (hf.autMap τ hτ x) := by
  obtain ⟨w, rfl⟩ := hf.surj x
  rw [← hf.act, hf.autMap_apply, hf.autMap_apply, ← hf.act, ← h]
  simp [MulAut.mul_apply]

theorem exists_semilinear
    (hcomm : ∀ T : M →+ M, (∀ (γ : D.Gam) (x : M), T (LM.lin γ x) = LM.lin γ (T x)) →
      ∃ c : K, ∀ x, T x = c • x)
    {x₀ : M} (hx₀ : x₀ ≠ 0) (τ : MulAut W) (hτ : ∀ z ∈ Z, τ z ∈ Z) (hτ' : ∀ z ∈ Z, τ⁻¹ z ∈ Z)
    (hτH' : ∀ h ∈ H, τ⁻¹ * h * τ ∈ H) :
    ∃ σ : K →+* K, ∀ (c : K) (x : M), hf.autMap τ hτ (c • x) = σ c • hf.autMap τ hτ x := by
  set T := hf.autMap τ hτ with hT
  set T' := hf.autMap τ⁻¹ hτ' with hT'
  have hTT' : ∀ x, T (T' x) = x := by
    intro x
    obtain ⟨w, rfl⟩ := hf.surj x
    rw [hT', hf.autMap_apply, hT, hf.autMap_apply, MulAut.apply_inv_self]
  have hT'T : ∀ x, T' (T x) = x := by
    intro x
    obtain ⟨w, rfl⟩ := hf.surj x
    rw [hT, hf.autMap_apply, hT', hf.autMap_apply, MulAut.inv_apply_self]
  have hconj : ∀ γ : D.Gam, ∃ γ' : D.Gam, ∀ x, T' (LM.lin γ x) = LM.lin γ' (T' x) := by
    intro γ
    obtain ⟨γ', hγ'⟩ := hf.onto ⟨τ⁻¹ * ((π γ : ↥H) : MulAut W) * τ, hτH' _ (π γ).2⟩
    refine ⟨γ', hf.autMap_lin τ⁻¹ hτ' γ' γ ?_⟩
    rw [hγ']
    simp [mul_assoc]
  have hconj' : ∀ γ γ' : D.Gam, (∀ x, T' (LM.lin γ x) = LM.lin γ' (T' x)) →
      ∀ x, T (LM.lin γ' x) = LM.lin γ (T x) := by
    intro γ γ' h x
    have := h (T x)
    rw [hT'T] at this
    rw [← this, hTT']
  have hsc : ∀ c : K, ∃ d : K, ∀ x, T (c • T' x) = d • x := by
    intro c
    refine hcomm ((T.comp (DistribSMul.toAddMonoidHom M c)).comp T') fun γ x => ?_
    obtain ⟨γ', hγ'⟩ := hconj γ
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, DistribSMul.toAddMonoidHom_apply]
    rw [hγ', ← LinearMap.map_smul, hconj' γ γ' hγ']
  choose σf hσf using hsc
  have hsmul_inj : ∀ a b : K, a • x₀ = b • x₀ → a = b := fun a b h =>
    smul_left_injective K hx₀ h
  have hσ1 : σf 1 = 1 := hsmul_inj _ _ (by rw [← hσf, one_smul, hTT', one_smul])
  have hσadd : ∀ a b, σf (a + b) = σf a + σf b := fun a b =>
    hsmul_inj _ _ (by rw [← hσf, add_smul, map_add, hσf, hσf, add_smul])
  have hσmul : ∀ a b, σf (a * b) = σf a * σf b := fun a b =>
    hsmul_inj _ _ (by
      rw [← hσf, mul_smul, mul_smul, ← hσf b, ← hσf a, hT'T])
  have hσ0 : σf 0 = 0 := by
    have h := hσadd 0 0
    rw [add_zero] at h
    exact add_eq_left.mp h.symm
  let σ : K →+* K :=
    { toFun := σf
      map_one' := hσ1
      map_mul' := hσmul
      map_zero' := hσ0
      map_add' := hσadd }
  refine ⟨σ, fun c x => ?_⟩
  change T (c • x) = σf c • T x
  rw [← hσf c (T x), hT'T]

end IsCoord

end CFSG.Quasithin.Vol2.KGNat
