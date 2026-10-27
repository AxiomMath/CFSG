module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45FieldFixAut
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangReeF4
import CFSG.SignalizerFunctorTheorem.CatalogBridge.LargeReeFixedEmbed
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45KGForms
import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Ree
open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_full_inner_field_automorphism_normal_form)

section ReeFix

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}

theorem gff_reeGammaFieldAutHom_injective (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Function.Injective (ReeTag.F4.reeGammaFieldAutHom K a) := by
  obtain ⟨-, hNF, -, -⟩ := large_Ree_full_inner_field_automorphism_normal_form a ha K hK
  intro s t h
  change ReeTag.F4.reeGammaFieldAut K a s = ReeTag.F4.reeGammaFieldAut K a t at h
  obtain ⟨q, -, huniq⟩ := hNF (ReeTag.F4.reeGammaFieldAut K a s)
  have h1 := huniq (1, s) (by simp)
  have h2 := huniq (1, t) (by simpa using h)
  exact congrArg Prod.snd (h1.trans h2.symm)

theorem gff_ree_exists_fieldAut (hZ : Subgroup.center (ReeTag.F4.reeGamma K a) = ⊥)
    {φ : MulAut (LargeEvenCenterQuot (ReeTag.F4.reeGamma K a))}
    (hφ : φ ∈ RecipeFieldExcInn.markFieldImage (IsRoot ReeTag.F4.tag) K
      (ReeTag.F4.reeGamma K a)) :
    ∃ σ : K ≃+* K,
      MulAut.congr (centerQuotEquivOfBot hZ) φ = ReeTag.F4.reeGammaFieldAut K a σ := by
  obtain ⟨σ, hG⟩ := hφ
  refine ⟨σ, MulEquiv.ext fun h => ?_⟩
  have hinj : Function.Injective (LargeEvenCenterMk (ReeTag.F4.reeGamma K a)) := by
    rw [← MonoidHom.ker_eq_bot_iff, LargeEvenCenterMk, QuotientGroup.ker_mk', hZ]
  apply hinj
  rw [← congr_centerQuotEquivOfBot_mk hZ]
  exact hG h (ReeTag.F4.reeGammaFieldAut K a σ h) rfl

theorem gff_ree_fixed (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (σ : K ≃+* K) (hσ : orderOf σ = p) :
    ∃ (b : ℕ) (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k ReeTag.F4.prime),
      Nat.card k = 2 ^ (2 * b + 1) ∧ (2 * b + 1) * p = 2 * a + 1 ∧
      Nonempty (↥(ReeTag.F4.reeGamma k b) ≃*
        ↥(ggAutFixedSubgroup (ReeTag.F4.reeGammaFieldAut K a σ))) := by
  obtain ⟨b, hchar, hcard, hb, ι, hι, hrange⟩ :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.exists_fixedPoints_reeGammaFieldAut_odd hK hp hp2
      σ hσ
  have hfix : ι.range = ggAutFixedSubgroup (ReeTag.F4.reeGammaFieldAut K a σ) :=
    Subgroup.ext fun z => hrange z
  have : Finite (fixSubfield σ) := Subtype.finite
  exact ⟨b, _, inferInstance, inferInstance, hchar, hcard, hb,
    ⟨(MonoidHom.ofInjective hι).trans (MulEquiv.subgroupCongr hfix)⟩⟩

end ReeFix

end CFSG.StandardType
