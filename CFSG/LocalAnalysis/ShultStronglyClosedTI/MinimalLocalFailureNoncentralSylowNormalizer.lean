module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureNoncentralSylowSelection
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowConsequences
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalizedIntersection
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionPrimeNormalizerProper

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open
open CFSG.ProperTwoGeneratedCore
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionSubgroupSylow

variable {G : Type*} [Group G] [Finite G]

theorem noncentralSylow_odd_core_normalizing_pair_flip
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (hdoubly : ∀ a b c d : pointRightCosetSpace H, a ≠ b → c ≠ d →
      ∃ g : G, pointRightCosetMul H a g = c ∧ pointRightCosetMul H b g = d)
    (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (p : ℕ) (hp : p.Prime)
    (P : Sylow p ((CFSG.oddCore (triplePointStabilizer H z beta)).map
      (triplePointStabilizer H z beta).subtype)) :
    ∃ t : G, t ∈ rightPairFlipFiber H z beta ∧
      t ∈ Subgroup.normalizer
        (((P : Subgroup ((CFSG.oddCore (triplePointStabilizer H z beta)).map
          (triplePointStabilizer H z beta).subtype)).map
          ((CFSG.oddCore (triplePointStabilizer H z beta)).map
            (triplePointStabilizer H z beta).subtype).subtype : Subgroup G) : Set G) := by
  let E := triplePointStabilizer H z beta
  let B := pairPointStabilizer H beta
  let J := pairOddCore H beta
  let V := (CFSG.oddCore E).map E.subtype
  obtain ⟨t₀, ht₀⟩ := original_pair_flip_exists h beta hbeta
  have hBJ : B ≤ Subgroup.normalizer (J : Set G) :=
    Subgroup.le_normalizer.trans
      (generatedPairGrowth_normalizer_le_characteristic_image B (CFSG.oddCore B)
        (CFSG.ComponentClassification.OddCore.characteristic B))
  have hclosure : Subgroup.closure ((B : Set G) ∪ {t₀}) ≤
      Subgroup.normalizer (J : Set G) := by
    apply (Subgroup.closure_le _).mpr
    exact Set.union_subset hBJ (Set.singleton_subset_iff.mpr
      (generatedPairGrowth_flip_normalizes_pair_odd_core h hbeta ht₀))
  have hV : V = J ⊓ E := triple_odd_core_eq_pair_intersection h S hzS hzcenter beta hbeta
  have hall := local_involution_point_normalized_intersection_sylow_flips
    H z h S hzS hzcenter hdoubly beta hbeta t₀ ht₀ J hclosure p hp
  rw [← hV] at hall
  obtain ⟨t, htclass, htnorm⟩ := hall P
  have htfiber : t ∈ rightPairFlipFiber H z beta := by
    rw [pair_flip_fiber_eq_stabilizer_class h S hzS hzcenter hbeta ht₀]
    exact htclass
  exact ⟨t, htfiber, htnorm⟩

theorem noncentralSylow_selected_proper_normalizer
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (hnoncentral : triplePointStabilizer H z beta ≠
      pairPointStabilizer H beta ⊓ Subgroup.centralizer ({z} : Set G)) :
    let E := triplePointStabilizer H z beta
    let V := (CFSG.oddCore E).map E.subtype
    V = pairOddCore H beta ⊓ E ∧
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ p ∣ Nat.card (conjugacyWithin H z) ∧
      ∃ P : Sylow p V,
        let U := (P : Subgroup V).map V.subtype
        U ≠ ⊥ ∧ ¬ U ≤ Subgroup.centralizer ({z} : Set G) ∧
        ∃ t : G, t ∈ rightPairFlipFiber H z beta ∧
          z ∈ Subgroup.normalizer (U : Set G) ∧
          t ∈ Subgroup.normalizer (U : Set G) ∧
          Subgroup.normalizer (U : Set G) ≠ ⊤ ∧
          ¬ Subgroup.normalizer (U : Set G) ≤ H ∧
          (∀ hzM : z ∈ Subgroup.normalizer (U : Set G),
            InvolutionPointLocalEmbedding
              (H.subgroupOf (Subgroup.normalizer (U : Set G)))
              (⟨z, hzM⟩ : Subgroup.normalizer (U : Set G)) ∧
            ∃ (T : Sylow 2 (Subgroup.normalizer (U : Set G)))
              (hzT : (⟨z, hzM⟩ : Subgroup.normalizer (U : Set G)) ∈
                (T : Subgroup (Subgroup.normalizer (U : Set G)))),
              (⟨(⟨z, hzM⟩ : Subgroup.normalizer (U : Set G)), hzT⟩ :
                (T : Subgroup (Subgroup.normalizer (U : Set G)))) ∈
                  Subgroup.center (T : Subgroup (Subgroup.normalizer (U : Set G)))) ∧
          (∀ A : Subgroup G, U ≤ A → ¬ A ≤ Subgroup.centralizer ({z} : Set G)) := by
  let E := triplePointStabilizer H z beta
  let V := (CFSG.oddCore E).map E.subtype
  obtain ⟨S, hzS, hzcenter⟩ := h.central_sylow
  have hdoubly := (minimalLocalFailureSylowFixedPoints h).2.2.1
  have hV := triple_odd_core_eq_pair_intersection h.local_datum S hzS hzcenter beta hbeta
  obtain ⟨p, hp, hpodd, hpm, _, P, hUne, hzU, hUnoncentral⟩ :=
    noncentralSylow_triple_odd_invariant_sylow h.local_datum S hzS hzcenter beta hbeta
      hnoncentral
  obtain ⟨t, htfiber, htU⟩ := noncentralSylow_odd_core_normalizing_pair_flip
    h.local_datum S hzS hzcenter hdoubly beta hbeta p hp P
  let U := (P : Subgroup V).map V.subtype
  let M := Subgroup.normalizer (U : Set G)
  obtain ⟨hsimple, hnonab⟩ := minimalLocalFailure_nonabelian_simple h
  let := hsimple
  have hMproper : M ≠ ⊤ :=
    prime_subgroup_normalizer_ne_top hnonab p hp U (P.isPGroup'.map V.subtype) hUne
  have hMescape : ¬ M ≤ H := fun hMH =>
    pair_flip_not_mem_point hbeta htfiber (hMH htU)
  refine ⟨hV, p, hp, hpodd, hpm, P, hUne, hUnoncentral, t, htfiber, hzU, htU,
    hMproper, hMescape, ?_, ?_⟩
  · intro hzM
    obtain ⟨hlocal, hcentral⟩ := involution_point_subgroup_inheritance
      h.local_datum M hzM hMescape
    exact ⟨hlocal, hcentral ⟨S, hzS, hzcenter⟩⟩
  · intro A hUA hAC
    exact hUnoncentral (hUA.trans hAC)

end CFSG.ShultStronglyClosedTI
