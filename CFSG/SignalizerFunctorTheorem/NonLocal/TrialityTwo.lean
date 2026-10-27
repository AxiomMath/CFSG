module

public import CFSG.SignalizerFunctorTheorem.NonLocal.D4Heis
public import CFSG.SignalizerFunctorTheorem.NonLocal.TwistedClosing
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalizedStatements
public import CFSG.RankThree.Chevalley.SteinbergBTTrialityCanonicalField

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley (triality_canonical_field_full_centralizer_and_pointwise_kernel)
open CFSG.LocalAnalysis.ComponentInitial (finite_field_prime_power_characteristic)
open CFSG.SignalizerFunctorTheorem.CatalogBridge

namespace CFSG.SignalizerFunctorTheorem.NonLocal

theorem subfieldNonLocalizedTrialityTwo :
    SubfieldNonLocalizedTrialityTwo := by
  intro p hp hp3 K _ _ hK σ δ hσ hδ
  classical
  have hm3 : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).2 (by omega)
  have hK' : Nat.card K = 2 ^ (3 * 1 * p) := by simpa using hK
  obtain ⟨-, -, hk, -, hord, hJC, -, hsJ, -⟩ :=
    triality_canonical_field_full_centralizer_and_pointwise_kernel Nat.prime_two le_rfl hp.two_le
      hm3 K hK' σ (fun c => by rw [hσ c, one_mul]) δ (fun c => by simpa using hδ c)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two
    (by omega : 1 ≤ 3 * 1 * p) hK'
  have : Finite (fixSubfield δ) := Subtype.finite
  have : CharP (fixSubfield δ) 2 :=
    (RingHom.charP_iff (fixSubfield δ).subtype (fixSubfield δ).subtype.injective 2).mpr ‹CharP K 2›
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hσ₀3 : (fixSubfieldRestrict σ δ).toRingHom ^ 3 = 1 := by
    refine RingHom.ext fun c => ?_
    have h := congrArg (fun ψ : fixSubfield δ ≃+* fixSubfield δ => ψ c)
      (pow_orderOf_eq_one (fixSubfieldRestrict σ δ))
    rw [hord] at h
    exact h
  have hK₀ : Nat.card (fixSubfield δ) = 8 := by rw [hk]; norm_num
  have h28 : TwistTag.D4.tag.rank + TwistTag.D4.tag.rootCount = 28 := by decide
  have hsimple : IsSimpleGroup ↥(((graphFixedRootGroup TwistTag.D4 (fixSubfield δ)
      (fixSubfieldRestrict σ δ).toRingHom).map (baseChangeGL (fixSubfield δ).subtype)).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :=
    (Subgroup.subgroupOfEquivOfLe hJC).isSimpleGroup
  exact nonLocalized_twisted_of_no_small_action TwistTag.D4 2 (fixSubfield δ).subtype
    σ.toRingHom (fixSubfieldRestrict σ δ).toRingHom (fixSubfieldRestrict σ δ).surjective
    (fun c => (coe_fixSubfieldRestrict σ δ c).symm) hsimple
    (fun Λ _ hΛ π hπ => no_small_faithful_action_D4 (fixSubfieldRestrict σ δ) hσ₀3 hK₀
      (by rw [h28] at hΛ; exact hΛ) π hπ)

end CFSG.SignalizerFunctorTheorem.NonLocal
