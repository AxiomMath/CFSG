module

public import CFSG.LieType.Ree.SmallReeOuterThreeKernel
import CFSG.LieType.Chevalley.DiagramCoordinateFixedStructure
import CFSG.LieType.Chevalley.OddF4CosetDescent
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityCommon
public import CFSG.Open.SignalizerFunctorDefs

public section

open CFSG.Open (signalizerFixedSubgroup)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Ree (ReeTag)
open CFSG.ComponentClassification.UnbalancedCatalog (mem_zpowers_of_fixed)

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

theorem reeGammaFieldAut_baseChange
    {t : ReeTag} {k K : Type} [Field k] [Field K] [Finite k]
    [Finite K] [CharP k t.prime] [CharP K t.prime] (ι : k →+* K) (τ : K ≃+* K) (ρ : k ≃+* k)
    (hτρ : ∀ c, τ (ι c) = ι (ρ c)) {a b : ℕ} (j : t.reeGamma k b)
    (hj : baseChangeGL ι (j : ModGL t.tag k) ∈ t.reeGamma K a) :
    (((t.reeGammaFieldAut K a τ) ⟨baseChangeGL ι (j : ModGL t.tag k), hj⟩ : t.reeGamma K a) :
        ModGL t.tag K) =
      baseChangeGL ι (((t.reeGammaFieldAut k b ρ j : t.reeGamma k b)) : ModGL t.tag k) := by
  rw [ReeTag.coe_reeGammaFieldAut, ReeTag.coe_reeGammaFieldAut,
    units_map_entrywiseHom_eq_baseChangeGL, units_map_entrywiseHom_eq_baseChangeGL,
    baseChangeGL_baseChangeGL, baseChangeGL_baseChangeGL]
  have hcomp : τ.toRingHom.comp ι = ι.comp ρ.toRingHom := RingHom.ext hτρ
  rw [hcomp]

theorem ree_zpowers_of_inner_on_subfield
    {t : ReeTag} {K : Type} [Field K] [Finite K]
    [CharP K t.prime] {a b : ℕ} (σ : K ≃+* K) [CharP (fixSubfield σ) t.prime]
    (hfixed : ((t.reeGammaFieldAut K a σ).toMonoidHom.eqLocus (MonoidHom.id _)).map
        (t.reeGamma K a).subtype =
      (t.reeGamma (fixSubfield σ) b).map (baseChangeGL (fixSubfield σ).subtype))
    (hinner : ∀ ρ : fixSubfield σ ≃+* fixSubfield σ,
      t.reeGammaFieldAut (fixSubfield σ) b ρ ∈
        CFSG.ComponentClassification.OuterAutomorphisms.inner (t.reeGamma (fixSubfield σ) b) →
          ρ = 1)
    (x : t.reeGamma K a) (τ : K ≃+* K)
    (hx : x ∈ signalizerFixedSubgroup (t.reeGammaFieldAut K a σ))
    (hfix : ∀ j ∈ signalizerFixedSubgroup (t.reeGammaFieldAut K a σ),
      x * t.reeGammaFieldAut K a τ j * x⁻¹ = j) : τ ∈ Subgroup.zpowers σ := by
  classical
  set k := fixSubfield σ with hk
  set ι : k →+* K := k.subtype with hι
  set ρ : k ≃+* k := fixSubfieldRestrict τ σ with hρ
  have hτρ : ∀ c, τ (ι c) = ι (ρ c) := fun c => rfl
  have hN : ∀ y : t.reeGamma K a, y ∈ signalizerFixedSubgroup (t.reeGammaFieldAut K a σ) ↔
      (y : ModGL t.tag K) ∈ (t.reeGamma k b).map (baseChangeGL ι) := by
    intro y
    rw [← hfixed]
    constructor
    · intro hy
      exact ⟨y, hy, rfl⟩
    · rintro ⟨z, hz, hzy⟩
      have : z = y := Subtype.ext hzy
      subst this
      exact hz
  obtain ⟨x', hx'Γ, hx'⟩ := (hN x).1 hx
  have hρx : t.reeGammaFieldAut k b ρ = MulAut.conj (⟨x', hx'Γ⟩ : t.reeGamma k b)⁻¹ := by
    refine MulEquiv.ext fun j => ?_
    have hjΓ : baseChangeGL ι (j : ModGL t.tag k) ∈ t.reeGamma K a := by
      have h1 : baseChangeGL ι (j : ModGL t.tag k) ∈ (t.reeGamma k b).map (baseChangeGL ι) :=
        ⟨j, j.2, rfl⟩
      rw [← hfixed] at h1
      obtain ⟨y, -, hy⟩ := h1
      rw [← hy]
      exact y.2
    set jK : t.reeGamma K a := ⟨baseChangeGL ι (j : ModGL t.tag k), hjΓ⟩ with hjK
    have hjN : jK ∈ signalizerFixedSubgroup (t.reeGammaFieldAut K a σ) :=
      (hN jK).2 ⟨j, j.2, rfl⟩
    have h1 := hfix jK hjN
    have h2 := congrArg (fun y : t.reeGamma K a => (y : ModGL t.tag K)) h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
    rw [hjK, reeGammaFieldAut_baseChange (a := a) ι τ ρ hτρ j hjΓ, ← hx'] at h2
    change baseChangeGL ι x' * baseChangeGL ι (t.reeGammaFieldAut k b ρ j : ModGL t.tag k) *
      (baseChangeGL ι x')⁻¹ = baseChangeGL ι (j : ModGL t.tag k) at h2
    rw [← map_inv, ← map_mul, ← map_mul] at h2
    have h3 := baseChangeGL_injective ι h2
    apply Subtype.ext
    change (t.reeGammaFieldAut k b ρ j : ModGL t.tag k) = x'⁻¹ * (j : ModGL t.tag k) * x'
    calc (t.reeGammaFieldAut k b ρ j : ModGL t.tag k)
        = x'⁻¹ * (x' * (t.reeGammaFieldAut k b ρ j : ModGL t.tag k) * x'⁻¹) * x' := by group
      _ = x'⁻¹ * (j : ModGL t.tag k) * x' := by rw [h3]
  have hρ1 : ρ = 1 := hinner ρ (by rw [hρx]; exact ⟨_, rfl⟩)
  refine mem_zpowers_of_fixed fun c hc => ?_
  have := hτρ ⟨c, hc⟩
  rw [hρ1] at this
  exact this

end CFSG.SignalizerFunctorTheorem.CatalogBridge
