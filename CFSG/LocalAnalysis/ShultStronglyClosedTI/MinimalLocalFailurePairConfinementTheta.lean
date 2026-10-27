module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionGeneratedPairGrowthPair
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionGeneratedPairGrowthCanonical
public import CFSG.Assembly.Defs

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.SignalizerFunctor.Helpers
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

universe u

variable {G : Type u} [Group G]

@[expose] def minimalLocalFailurePairConfinementTheta (p : ℕ) (D : Subgroup G) :
    Subgroup G :=
  (piCore (generatedPairGrowthCanonicalPrimes p) D).map D.subtype

theorem pairConfinement_theta_le (p : ℕ) (D : Subgroup G) :
    minimalLocalFailurePairConfinementTheta p D ≤ D := Subgroup.map_subtype_le _

variable [Finite G]

theorem pairConfinement_theta_order (p : ℕ) (hp : p.Prime) (D : Subgroup G) :
    Odd (Nat.card (minimalLocalFailurePairConfinementTheta p D)) ∧
      Nat.Coprime p (Nat.card (minimalLocalFailurePairConfinementTheta p D)) := by
  unfold minimalLocalFailurePairConfinementTheta
  rw [Subgroup.card_subtype, ← generatedPairGrowth_literal_core_eq_canonical]
  exact (generatedPairGrowth_prime_supported_iff hp).mp
    (prime_set_core_supported (generatedPairGrowthPrimes p))

theorem pairConfinement_theta_normalizer (p : ℕ) (D : Subgroup G) :
    Subgroup.normalizer (D : Set G) ≤
      Subgroup.normalizer (minimalLocalFailurePairConfinementTheta p D : Set G) := by
  apply generatedPairGrowth_normalizer_le_characteristic_image
  rw [← generatedPairGrowth_literal_core_eq_canonical]
  exact prime_set_core_characteristic _

theorem pairConfinement_theta_normal (p : ℕ) (D : Subgroup G) :
    ((minimalLocalFailurePairConfinementTheta p D).subgroupOf D).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (pairConfinement_theta_le p D)).mpr
    (Subgroup.le_normalizer.trans (pairConfinement_theta_normalizer p D))

omit [Finite G] in
theorem pairConfinement_theta_maximal (p : ℕ) (hp : p.Prime)
    (D Y : Subgroup G) (hYD : Y ≤ D) (hYn : (Y.subgroupOf D).Normal)
    (hYodd : Odd (Nat.card Y)) (hYcop : Nat.Coprime p (Nat.card Y)) :
    Y ≤ minimalLocalFailurePairConfinementTheta p D := by
  have hcard : Nat.card (Y.subgroupOf D) = Nat.card Y :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYD).toEquiv
  have hcore : Y.subgroupOf D ≤ piCore (generatedPairGrowthCanonicalPrimes p) D := by
    rw [← generatedPairGrowth_literal_core_eq_canonical]
    apply prime_set_core_contains _ _ hYn
    apply (generatedPairGrowth_prime_supported_iff hp).mpr
    simpa only [hcard] using And.intro hYodd hYcop
  have hmap := Subgroup.map_mono (f := D.subtype) hcore
  rwa [Subgroup.map_subgroupOf_eq_of_le hYD] at hmap

theorem pairConfinement_theta_restrict (p : ℕ) (hp : p.Prime)
    (D E : Subgroup G) (hED : E ≤ D)
    (htheta : minimalLocalFailurePairConfinementTheta p D ≤ E) :
    minimalLocalFailurePairConfinementTheta p D ≤
      minimalLocalFailurePairConfinementTheta p E := by
  obtain ⟨hodd, hcop⟩ := pairConfinement_theta_order p hp D
  have hnormal : ((minimalLocalFailurePairConfinementTheta p D).subgroupOf E).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer htheta).mpr
      (hED.trans (Subgroup.le_normalizer.trans (pairConfinement_theta_normalizer p D)))
  exact pairConfinement_theta_maximal p hp E _ htheta hnormal hodd hcop

theorem pairConfinement_theta_strict_card (p : ℕ) (D E : Subgroup G)
    (hstrict : minimalLocalFailurePairConfinementTheta p D <
      minimalLocalFailurePairConfinementTheta p E) :
    Nat.card (minimalLocalFailurePairConfinementTheta p D) <
      Nat.card (minimalLocalFailurePairConfinementTheta p E) :=
  Set.Finite.card_lt_card (Set.toFinite _) hstrict

theorem pairConfinement_theta_escape_of_growth (p : ℕ) (hp : p.Prime)
    (H J D : Subgroup G) (hDH : D ≤ H)
    (hgrowth : minimalLocalFailurePairConfinementTheta p (D ⊓ (H ⊓ J)) <
      minimalLocalFailurePairConfinementTheta p (H ⊓ J))
    (hmax : Nat.card (minimalLocalFailurePairConfinementTheta p (H ⊓ J)) ≤
      Nat.card (minimalLocalFailurePairConfinementTheta p D)) :
    ¬ minimalLocalFailurePairConfinementTheta p D ≤ J := by
  intro hconfined
  have hE : minimalLocalFailurePairConfinementTheta p D ≤ D ⊓ (H ⊓ J) :=
    le_inf (pairConfinement_theta_le p D)
      (le_inf ((pairConfinement_theta_le p D).trans hDH) hconfined)
  have hcore := pairConfinement_theta_restrict p hp D (D ⊓ (H ⊓ J)) inf_le_left hE
  have hcard : Nat.card (minimalLocalFailurePairConfinementTheta p D) ≤
      Nat.card (minimalLocalFailurePairConfinementTheta p (D ⊓ (H ⊓ J))) :=
    Nat.card_le_card_of_injective (Subgroup.inclusion hcore) (Subgroup.inclusion_injective hcore)
  have hlt := pairConfinement_theta_strict_card p _ _ hgrowth
  omega

theorem pairConfinement_theta_maximizing_conjugate
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (N : Subgroup G) (hescape : ¬ N ≤ H) (p : ℕ) :
    ∃ s ∈ conjugacyWithin N z, s ∉ H ∧
      ∀ r ∈ conjugacyWithin N z, r ∉ H →
        Nat.card (minimalLocalFailurePairConfinementTheta p (H ⊓ rightConjugate H r)) ≤
          Nat.card (minimalLocalFailurePairConfinementTheta p (H ⊓ rightConjugate H s)) := by
  let T : Set G := conjugacyWithin N z \ (H : Set G)
  have hT : T.Nonempty := by
    obtain ⟨n, hn, hnH⟩ := IsConcreteLE.not_le_iff_exists.mp hescape
    refine ⟨rightConjugateElem z n, ⟨⟨⟨n, hn⟩, rfl⟩, ?_⟩⟩
    exact fun hmem => hnH ((pointClass_conjugate_mem_iff h n).mp hmem)
  obtain ⟨s, hs, hmax⟩ := Set.exists_max_image T
    (fun r => Nat.card (minimalLocalFailurePairConfinementTheta p
      (H ⊓ rightConjugate H r))) (Set.toFinite T) hT
  exact ⟨s, hs.1, hs.2, fun r hr hnH => hmax r ⟨hr, hnH⟩⟩

end CFSG.ShultStronglyClosedTI
