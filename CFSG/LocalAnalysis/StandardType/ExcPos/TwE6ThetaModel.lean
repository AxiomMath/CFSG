module

public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6RootModelDecomp
public import CFSG.LieType.Chevalley.TwistedE6NormalForm
public import CFSG.LocalAnalysis.StandardType.GGFinModelRat

public noncomputable section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Assembly CFSG.Open CFSG.StandardType CFSG.StandardType.GGFinModel
  CFSG.StandardType.LieCore CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.ClassicalPosition
  CFSG.LieType.Universal CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


theorem exists_twE6_model_of_theta {X : Type} [Group X] {f : ℕ} {G₀ : Subgroup X} (hf : 1 ≤ f)
    {θ : ↥G₀ →* ModGL (langTag .twistedE6) GGL} (hθinj : Function.Injective θ)
    (hθrange : θ.range = ⁅ggFixGp .twistedE6 f, ggFixGp .twistedE6 f⁆) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K) (κ : K →+* GGL),
      Nat.card K = (2 ^ f) ^ 2 ∧ (∀ z, σ z = z ^ 2 ^ f) ∧
      ∃ eF : ↥G₀ ≃* ↥(twistedE6RootGroup K σ),
        ∀ g, baseChangeGL (τ := Tag.E6) κ ((eF g : ModGL TwistTag.E6.tag K)) = θ g := by
  classical
  haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  let K := GaloisField 2 (2 * f)
  have hK : Nat.card K = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (Nat.mul_ne_zero (by norm_num) (Nat.one_le_iff_ne_zero.mp hf))]
    rw [← pow_mul, Nat.mul_comm]
  let κ : K →+* GGL := ggRatEmb (2 * f)
  let σ : K ≃+* K := iterateFrobeniusEquiv K 2 f
  have hσ : ∀ z, σ z = z ^ 2 ^ f := fun z => iterateFrobeniusEquiv_def K 2 f z
  have hσ' : ∀ z, σ.toRingHom z = z ^ 2 ^ f := hσ
  have himg := map_baseChangeGL_graphFixedRootGroup_eq TwistTag.E6 Nat.prime_two hf K hK
    σ.toRingHom hσ' κ (ggFrobT_apply f) (ggFrobT_surjective f)
  let S : Subgroup (ModGL Tag.E6 K) := twistedE6RootGroup K σ
  let b : ModGL Tag.E6 K →* ModGL Tag.E6 GGL := baseChangeGL (τ := Tag.E6) κ
  have hrange : θ.range = S.map b := hθrange.trans ((twE6_derived_ggFixGp_eq hf).trans himg.symm)
  let e₁ : ↥S ≃* ↥(S.map b) := Subgroup.equivMapOfInjective S b (baseChangeGL_injective κ)
  let e₂ : ↥G₀ ≃* ↥θ.range := MonoidHom.ofInjective hθinj
  let e₃ : ↥θ.range ≃* ↥(S.map b) := MulEquiv.subgroupCongr hrange
  refine ⟨K, inferInstance, inferInstance, σ, κ, hK, hσ, (e₂.trans e₃).trans e₁.symm, fun g => ?_⟩
  have h1 : ((e₁ (e₁.symm (e₃ (e₂ g))) : ↥(S.map b)) : ModGL Tag.E6 GGL) =
      b ((e₁.symm (e₃ (e₂ g)) : ↥S) : ModGL Tag.E6 K) :=
    Subgroup.coe_equivMapOfInjective_apply S b (baseChangeGL_injective κ) _
  have h2 : ((e₁ (e₁.symm (e₃ (e₂ g))) : ↥(S.map b)) : ModGL Tag.E6 GGL) =
      ((e₃ (e₂ g) : ↥(S.map b)) : ModGL Tag.E6 GGL) := by
    rw [e₁.apply_symm_apply]
  have h3 : ((e₃ (e₂ g) : ↥(S.map b)) : ModGL Tag.E6 GGL) = θ g := rfl
  exact h1.symm.trans (h2.trans h3)

end CFSG.StandardType.LieKnownR2.ExcPos
