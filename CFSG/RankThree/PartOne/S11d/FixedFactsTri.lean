module

public import CFSG.RankThree.PartOne.S11d.FixedFacts
public import CFSG.RankThree.PartOne.S11c.Sec66D4Tri
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalTrialityMain
public import CFSG.SignalizerFunctorTheorem.NonLocal.TrialityTwo

public section

namespace CFSG.RankThree.PartOne.FieldFix

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley SteinbergBT CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Sec66T
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.LieType.CurtisTits (lieModel_of_mulEquiv)
open CFSG.SignalizerFunctorTheorem.CatalogBridge (NonLocalized)


theorem tagFixedFacts_trialityD4 : TagFixedFacts .trialityD4 := by
  intro T _ _ p hp hp5 _ n f₀ hf₀ hM α₀ _ _ _ hX₀ α hαp hαinn _ _
  obtain ⟨hn0, hCEM⟩ := lieModel_trialityD4_iff.mp hM
  subst hn0
  have hf : 1 ≤ p * f₀ := Nat.mul_pos hp.pos hf₀
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, hKf, hKfin, σ, hKcard, hσ, ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card .D4 Nat.prime_two hf hCEM.2
  have hK : Nat.card K = (2 ^ (p * f₀)) ^ 3 := hKcard
  have hK3 : Nat.card K = 2 ^ (3 * (p * f₀)) := by rw [hK, ← pow_mul, mul_comm]
  have : Finite (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := Finite.of_equiv T e.toEquiv
  obtain ⟨hα'inn, hα'ord⟩ := congr_noninner_prime hp e hαp hαinn
  set α' : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := MulAut.congr e α with hα'
  obtain ⟨-, -, ⟨Θ, hΘ, -⟩, hcyc, -⟩ :=
    even_triality_exact_automorphism_normal_form hf K hK σ hσ
  obtain ⟨hηord, hpf, ⟨h₀, hh₀⟩, -⟩ :=
    triality_noninner_large_prime_field_descent_and_local_core_trivial Nat.prime_two hf K hK σ hσ
      Θ hΘ hp (by omega) ⊤ le_top ⟨α', Subgroup.mem_top _⟩ hα'inn
      (by rw [Subgroup.orderOf_mk]; exact hα'ord)
  obtain ⟨f', hff'⟩ := hpf
  have hf'f₀ : f' = f₀ := (Nat.eq_of_mul_eq_mul_left hp.pos hff').symm
  have hd : 1 ≤ f' := by omega
  have hm3 : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).2 (by omega)
  obtain ⟨φ, hφ, hφord, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two (by omega : 1 ≤ 3 * (p * f₀)) hK3
  obtain ⟨δc, hδcdef⟩ : ∃ δc, φ ^ (3 * f') = δc := ⟨_, rfl⟩
  have hδc : ∀ c, δc c = c ^ 2 ^ (3 * f') := fun c => by
    rw [← hδcdef]
    exact ringAut_pow_apply_of_frobenius hφ _ c
  have hδcord : orderOf δc = p := by
    rw [← hδcdef, orderOf_pow_of_dvd (by omega) (by rw [hφord, hff']; exact ⟨p, by ring⟩),
      hφord, hff', show 3 * (p * f') = 3 * f' * p by ring, Nat.mul_div_cancel_left p (by omega)]
  have hzp : Subgroup.zpowers (Θ α') = Subgroup.zpowers δc := by
    have h1 : Nat.card (Subgroup.zpowers (Θ α')) = p := by rw [Nat.card_zpowers]; exact hηord
    have h2 : Nat.card (Subgroup.zpowers δc) = p := by rw [Nat.card_zpowers, hδcord]
    have : Finite (Subgroup.zpowers (Θ α')) :=
      Nat.finite_of_card_ne_zero (by rw [h1]; exact hp.ne_zero)
    have : Finite (Subgroup.zpowers δc) :=
      Nat.finite_of_card_ne_zero (by rw [h2]; exact hp.ne_zero)
    exact IsCyclic.subgroup_eq_iff_card_eq.mpr (h1.trans h2.symm)
  have hfix_eq : fixSub (MulAut.conj h₀ * MulAut.congr e α * (MulAut.conj h₀)⁻¹) =
      fixSub (fieldActor σ δc) := by
    have h1 : MulAut.conj h₀ * MulAut.congr e α * (MulAut.conj h₀)⁻¹ = fieldActor σ (Θ α') := hh₀
    rw [h1]
    apply fixSub_eq_of_zpowers_eq
    have h2 := congrArg (Subgroup.map (fieldActorHom (t := TwistTag.D4) σ)) hzp
    rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers] at h2
    exact h2
  have hK' : Nat.card K = 2 ^ (3 * f' * p) := by rw [hK3, hff']; ring
  have hσ' : ∀ c, σ c = c ^ 2 ^ (f' * p) := fun c => by rw [hσ, hff', mul_comm]
  obtain ⟨-, -, hk, hres, -, -, hfixJ, hsimple, hnc, -⟩ :=
    triality_canonical_field_full_centralizer_and_pointwise_kernel Nat.prime_two hd hp.two_le hm3
      K hK' σ hσ' δc hδc
  have : Finite (fixSubfield δc) := Subtype.finite
  have : Fintype (fixSubfield δc) := Fintype.ofFinite _
  set J := trialityFieldImage σ δc
  let e3 : ↥(fixSub (fieldActor σ δc)) ≃* ↥J :=
    (Subgroup.equivMapOfInjective _ (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype_injective).trans
      (MulEquiv.subgroupCongr hfixJ)
  have hK0 : Nat.card (fixSubfield δc) = (2 ^ f') ^ 3 := by rw [hk, ← pow_mul, mul_comm]
  have hcardK0 : Fintype.card (fixSubfield δc) = 2 ^ (3 * f') := by
    rw [← Nat.card_eq_fintype_card, hk]
  have hσ0pow : ∀ c : fixSubfield δc, fixSubfieldRestrict σ δc c = c ^ 2 ^ (f' * p) := fun c =>
    Subtype.ext (by rw [hres c, hσ', SubmonoidClass.coe_pow])
  obtain ⟨j, r, hr, hpjr⟩ : ∃ j r : ℕ, (r = 1 ∨ r = 2) ∧ p = 3 * j + r := by
    have h3 : p % 3 ≠ 0 := fun h => by
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 (Nat.dvd_of_mod_eq_zero h)
      omega
    rcases (show p % 3 = 1 ∨ p % 3 = 2 by omega) with h | h
    · exact ⟨p / 3, 1, Or.inl rfl, by omega⟩
    · exact ⟨p / 3, 2, Or.inr rfl, by omega⟩
  have hpowj : ∀ c : fixSubfield δc, c ^ (2 ^ (3 * f')) ^ j = c := fun c => by
    have h := FiniteField.pow_card_pow j c
    rwa [hcardK0] at h
  have hσ0pow' : ∀ c : fixSubfield δc, fixSubfieldRestrict σ δc c = c ^ 2 ^ (f' * r) := fun c => by
    have h2 : 2 ^ (f' * p) = (2 ^ (3 * f')) ^ j * 2 ^ (f' * r) := by
      rw [hpjr]
      ring
    rw [hσ0pow c, h2, pow_mul, hpowj c]
  have hσ0orient : (∀ c : fixSubfield δc, fixSubfieldRestrict σ δc c = c ^ 2 ^ f') ∨
      ∀ c : fixSubfield δc, fixSubfieldRestrict σ δc c = c ^ (2 ^ f') ^ 2 := by
    rcases hr with rfl | rfl
    · exact Or.inl fun c => by rw [hσ0pow' c, mul_one]
    · exact Or.inr fun c => by rw [hσ0pow' c, ← pow_mul]
  have hXmodel : LieModel ↥J .trialityD4 0 2 f₀ := by
    rw [← hf'f₀]
    exact lieModel_of_mulEquiv
      ((graphFixedRootGroup TwistTag.D4 (fixSubfield δc)
        (fixSubfieldRestrict σ δc).toRingHom).equivMapOfInjective _ (baseChangeGL_injective _))
      (lieModel_graphFixedRootGroup_trialityD4 hd hK0 (fixSubfieldRestrict σ δc) hσ0orient)
  have hnc' : ∃ a b : ↥J, a * b ≠ b * a := by
    push Not at hnc
    exact hnc
  have : IsSimpleGroup ↥J := hsimple
  have hNL : NonLocalized (J.subgroupOf (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
    have hTri := SignalizerFunctorTheorem.CatalogBridge.subfieldNonLocalizedTriality_of
      SignalizerFunctorTheorem.NonLocal.subfieldNonLocalizedTrialityTwo
    exact hTri 2 f' p Nat.prime_two hd hp (by omega) K hK' σ δc hσ' hδc
  have hfixsub : fixSub (fieldActor σ δc) =
      J.subgroupOf (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
    ext x
    rw [Subgroup.mem_subgroupOf, ← hfixJ]
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      exact (Subtype.ext hyx) ▸ hy
  set φ' : T ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    e.trans (MulAut.conj h₀) with hφ'
  have hφα : MulAut.congr φ' α = MulAut.conj h₀ * MulAut.congr e α * (MulAut.conj h₀)⁻¹ := rfl
  have hfixβ : fixSub (MulAut.congr φ' α) = fixSub (fieldActor σ δc) := by rw [hφα, hfix_eq]
  exact fixedFacts_of_simple φ' α hM hf₀ ((MulEquiv.subgroupCongr hfixβ).trans e3) hnc'
    (by rw [hfixβ, hfixsub]; exact hNL) (Or.inl hXmodel)

end CFSG.RankThree.PartOne.FieldFix
