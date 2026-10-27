module

public import CFSG.Quasithin.H13.NQTermExcludesG2
public import CFSG.Quasithin.H13.NQTermTrialityCyclic

public section

namespace CFSG.Quasithin.H13.NQTerm

open Subgroup CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial (pairAutSubgroup pairAutRestrict)
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Quasithin.SteinbergCC (normalizerFrattiniConj)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem original_characteristic_witness_excludes_normal_even_triality_quotient
    {T L M : Subgroup G} (h : QTNQ T L M) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {X : Subgroup G} (hXL : X ≤ L) (hXc : (X.subgroupOf L).Characteristic)
    (hXA : IsPGroup p (X ⧸ CFSG.pCore 2 X))
    (hW : Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2)
    (hLW : ∃ l : normalizer (X : Set G), (l : G) ∈ L ∧ normalizerFrattiniConj X l ≠ 1)
    {Y K₀ : Subgroup G} (hXTY : X ⊔ T ≤ Y) (hKY : K₀ ≤ Y) (hKn : (K₀.subgroupOf Y).Normal)
    (hXK : X ≤ K₀) (hZ : ¬ p ∣ Nat.card (center (K₀ ⧸ CFSG.pCore 2 K₀))) :
    ∀ f : ℕ, 1 ≤ f → ¬ CFSG.Blueprint.ChevalleyExceptionalModel
      ((K₀ ⧸ CFSG.pCore 2 K₀) ⧸ center (K₀ ⧸ CFSG.pCore 2 K₀)) .trialityD4 2 f := by
  classical
  intro f hf hmod
  obtain ⟨-, F, _, _, hF, σ, hσ, ⟨η⟩⟩ := hmod
  have hF3 : Nat.card F = (2 ^ f) ^ 3 := hF
  obtain ⟨σ', rfl⟩ : ∃ σ' : F ≃+* F, σ'.toRingHom = σ :=
    ⟨RingEquiv.ofBijective σ (Finite.injective_iff_bijective.mp σ.injective),
      RingHom.ext fun _ => rfl⟩
  obtain ⟨-, -, -, -, -, -, -, ⟨e⟩⟩ :=
    even_triality_exact_automorphism_normal_form hf F hF3 σ' hσ
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf p X
  have hPp : IsPGroup p (P.subgroupOf K₀) := by
    obtain ⟨Q, hQ⟩ := hP
    rw [← hQ]
    exact (Q.2.map X.subtype).comap_of_injective K₀.subtype K₀.subtype_injective
  obtain ⟨-, ⟨U', hU'⟩, hAU, hnc⟩ :=
    original_characteristic_witness_normal_quotient_common_normalizer_action_is_noncyclic h hp
      hp5 hXL hXc hXA hW hLW hXTY hKY hKn hXK hZ P hP
  set σ₀ : K₀ →* (K₀ ⧸ CFSG.pCore 2 K₀) ⧸ center (K₀ ⧸ CFSG.pCore 2 K₀) :=
    (QuotientGroup.mk' (center (K₀ ⧸ CFSG.pCore 2 K₀))).comp
      (QuotientGroup.mk' (CFSG.pCore 2 K₀))
  set A := (P.subgroupOf K₀).map σ₀
  set U := (T.subgroupOf K₀).map σ₀
  let ψ : ((K₀ ⧸ CFSG.pCore 2 K₀) ⧸ center (K₀ ⧸ CFSG.pCore 2 K₀)) ≃*
      graphFixedRootGroup TwistTag.D4 F σ'.toRingHom := η.trans e
  obtain ⟨Ustar, hUstar⟩ : ∃ Ustar : Sylow 2 (graphFixedRootGroup TwistTag.D4 F σ'.toRingHom),
      (Ustar : Subgroup (graphFixedRootGroup TwistTag.D4 F σ'.toRingHom)) =
        U.map ψ.toMonoidHom :=
    have hsurj : Function.Surjective ψ.toMonoidHom := ψ.surjective
    ⟨U'.mapSurjective hsurj, by rw [Sylow.coe_mapSurjective, hU']⟩
  obtain ⟨m, hm⟩ := (hPp.map σ₀).exists_card_eq
  have hcardA : Nat.card (A.map ψ.toMonoidHom) = p ^ m := by
    rw [Subgroup.card_map_of_injective ψ.injective]
    exact hm
  have hAodd : Odd (Nat.card (A.map ψ.toMonoidHom)) := by
    rw [hcardA]
    exact (hp.odd_of_ne_two (by omega)).pow
  have hA3 : ¬ 3 ∣ Nat.card (A.map ψ.toMonoidHom) := by
    rw [hcardA]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hAUstar : ((A.map ψ.toMonoidHom : Subgroup (graphFixedRootGroup TwistTag.D4 F
      σ'.toRingHom)) : Set (graphFixedRootGroup TwistTag.D4 F σ'.toRingHom)) *
        ((Ustar : Subgroup (graphFixedRootGroup TwistTag.D4 F σ'.toRingHom)) :
          Set (graphFixedRootGroup TwistTag.D4 F σ'.toRingHom)) =
      ((Ustar : Subgroup (graphFixedRootGroup TwistTag.D4 F σ'.toRingHom)) :
          Set (graphFixedRootGroup TwistTag.D4 F σ'.toRingHom)) *
        ((A.map ψ.toMonoidHom : Subgroup (graphFixedRootGroup TwistTag.D4 F σ'.toRingHom)) :
          Set (graphFixedRootGroup TwistTag.D4 F σ'.toRingHom)) := by
    rw [hUstar, Subgroup.coe_map ψ.toMonoidHom A, Subgroup.coe_map ψ.toMonoidHom U,
      ← Set.image_mul, hAU, Set.image_mul]
  obtain ⟨-, -, ⟨hcyc, -⟩, -⟩ := even_triality_common_sylow_odd_subgroup_normalizer_action_is_cyclic
    hf F hF3 σ'.toRingHom hσ Ustar (A.map ψ.toMonoidHom) hAodd hA3 hAUstar
  rw [hUstar] at hcyc
  exact hnc (isCyclic_pairAutRestrict_range_of_mulEquiv ψ A U hcyc)

end CFSG.Quasithin.H13.NQTerm
