module

public import CFSG.SignalizerFunctorTheorem.CatalogBridge.LargeReeFixed

public section

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree

theorem exists_fixedPoints_reeGammaFieldAut_odd
    {k : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * k + 1)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (β : K ≃+* K) (hβ : orderOf β = p) :
    ∃ (b : ℕ) (_ : CharP (fixSubfield β) ReeTag.F4.prime),
      Nat.card (fixSubfield β) = 2 ^ (2 * b + 1) ∧ (2 * b + 1) * p = 2 * k + 1 ∧
      ∃ ι : ReeTag.F4.reeGamma (fixSubfield β) b →* ReeTag.F4.reeGamma K k,
        Function.Injective ι ∧
        ∀ z, z ∈ ι.range ↔ ReeTag.F4.reeGammaFieldAut K k β z = z := by
  classical
  obtain ⟨b, hbp, hk', hfixeq⟩ := largeRee_fixed_data_odd hK hp hp2 β hβ
  have : Finite (fixSubfield β) := Subtype.finite
  have hchar : CharP (fixSubfield β) ReeTag.F4.prime := by
    have : Fintype (fixSubfield β) := Fintype.ofFinite _
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (p := 2) (f := 2 * b + 1) (by
      rw [← Nat.card_eq_fintype_card, hk'])
  have hmem : ∀ y : ReeTag.F4.reeGamma (fixSubfield β) b,
      baseChangeGL (fixSubfield β).subtype (y : ModGL ReeTag.F4.tag (fixSubfield β)) ∈
        ReeTag.F4.reeGamma K k := by
    intro y
    have hy : baseChangeGL (fixSubfield β).subtype (y : ModGL ReeTag.F4.tag (fixSubfield β)) ∈
        (ReeTag.F4.reeGamma (fixSubfield β) b).map (baseChangeGL (fixSubfield β).subtype) :=
      ⟨y, y.2, rfl⟩
    rw [← hfixeq] at hy
    obtain ⟨z, -, hz⟩ := hy
    rw [← hz]
    exact z.2
  set ι : ReeTag.F4.reeGamma (fixSubfield β) b →* ReeTag.F4.reeGamma K k :=
    ((baseChangeGL (fixSubfield β).subtype).comp
      (ReeTag.F4.reeGamma (fixSubfield β) b).subtype).codRestrict _ hmem with hι
  have hιinj : Function.Injective ι := by
    intro y y' h
    have h' := congrArg (fun z : ReeTag.F4.reeGamma K k => (z : ModGL ReeTag.F4.tag K)) h
    exact Subtype.ext (baseChangeGL_injective (τ := ReeTag.F4.tag) (fixSubfield β).subtype h')
  refine ⟨b, hchar, hk', hbp, ι, hιinj, fun z => ⟨?_, fun hz => ?_⟩⟩
  · rintro ⟨y, rfl⟩
    have hy' : (ι y : ModGL ReeTag.F4.tag K) ∈
        (ReeTag.F4.reeGamma (fixSubfield β) b).map (baseChangeGL (fixSubfield β).subtype) :=
      ⟨y, y.2, rfl⟩
    rw [← hfixeq] at hy'
    obtain ⟨z, hz, hzy⟩ := hy'
    have hzy' : z = ι y := Subtype.ext hzy
    rw [← hzy']
    exact hz
  · have hz' : (z : ModGL ReeTag.F4.tag K) ∈
        ((ReeTag.F4.reeGammaFieldAut K k β).toMonoidHom.eqLocus
          (MonoidHom.id _)).map (ReeTag.F4.reeGamma K k).subtype := ⟨z, hz, rfl⟩
    rw [hfixeq] at hz'
    obtain ⟨y, hy, hyz⟩ := hz'
    exact ⟨⟨y, hy⟩, Subtype.ext hyz⟩

end CFSG.SignalizerFunctorTheorem.CatalogBridge
