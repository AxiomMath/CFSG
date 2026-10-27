module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssembly
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperCommutingImages

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime

variable {G : Type*} [Group G] [Finite G]

theorem minimalLocalFailureSylowFixedPoints
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z) :
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
  exact minimalLocalFailureSylowFixedPointsFromProperCommutingImages h
    (properStrongEmbeddingCommutingImages G)

end CFSG.ShultStronglyClosedTI
