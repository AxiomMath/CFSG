module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyProper
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailurePairSylow

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime

variable {G : Type*} [Group G] [Finite G]

theorem minimalLocalFailureSylowFixedPointsFromProperCommutingImages
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G) :
    Odd (Nat.card (conjugacyWithin H z)) ∧
      1 < Nat.card (conjugacyWithin H z) ∧
      (∀ a b c d : pointRightCosetSpace H, a ≠ b → c ≠ d →
        ∃ g : G, pointRightCosetMul H a g = c ∧ pointRightCosetMul H b g = d) ∧
      (∀ p : ℕ, p.Prime → p ∣ Nat.card (conjugacyWithin H z) →
        (∀ P : Sylow p G, Nat.card (pointFixedSet H (P : Subgroup G)) = 2 ∧
          ∃ lambda mu : pointRightCosetSpace H, lambda ≠ mu ∧
            pointFixedSet H (P : Subgroup G) = {lambda, mu}) ∧
        ∀ lambda mu : pointRightCosetSpace H, lambda ≠ mu →
          ∀ P : Sylow p (rightCosetStabilizer H lambda ⊓ rightCosetStabilizer H mu : Subgroup G),
            (∃ T : Sylow p G, (T : Subgroup G) =
              (P : Subgroup (rightCosetStabilizer H lambda ⊓ rightCosetStabilizer H mu : Subgroup G)).map
                (rightCosetStabilizer H lambda ⊓ rightCosetStabilizer H mu : Subgroup G).subtype) ∧
              pointFixedSet H
                ((P : Subgroup (rightCosetStabilizer H lambda ⊓ rightCosetStabilizer H mu : Subgroup G)).map
                  (rightCosetStabilizer H lambda ⊓ rightCosetStabilizer H mu : Subgroup G).subtype) =
                {lambda, mu}) := by
  classical
  by_cases hgen : BasePointPairGeneration H z
  · obtain ⟨hodd, hgt, hfixed, hdoubly⟩ :=
      minimalLocalFailurePairSylow h (fullPointPairGeneration_of_base h.local_datum hgen)
    refine ⟨hodd, hgt, hdoubly, ?_⟩
    intro p hp hpdiv
    constructor
    · intro P
      have hcard := hfixed p hp hpdiv P
      obtain ⟨lambda, mu, hne, heq⟩ := Set.ncard_eq_two.mp
        (show (pointFixedSet H (P : Subgroup G)).ncard = 2 from hcard)
      exact ⟨hcard, lambda, mu, hne, heq⟩
    · intro lambda mu hne P
      exact pair_sylow_full_fixed_set_of_double_transitivity H p hp hdoubly
        (hfixed p hp hpdiv) lambda mu hne P
  · obtain ⟨beta, hbeta, t, ht, hproper⟩ :=
      sylowAssemblyProper_exists_failed_pair h hgen
    obtain ⟨hQH, hQnormal, _, hQtwo, hzQ⟩ :=
      sylowAssemblyProper_normal_point_two_hull h hcomm hbeta ht hproper
    exact minimalLocalFailure_normal_point_two_subgroup_sylow_conclusions
      h hQH hQnormal hQtwo hzQ

end CFSG.ShultStronglyClosedTI
