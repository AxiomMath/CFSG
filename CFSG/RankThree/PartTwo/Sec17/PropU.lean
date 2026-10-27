module

public import CFSG.RankThree.PartTwo.Sec17.Item1723NRouteProofDeltaMax
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS

@[expose] def Claim1724DeltaUp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ Y₁ S : Subgroup G) (p : ℕ)
    (P : Subgroup G) (w : G) (Q : Subgroup G), Sec17W G A c L Y₀ Y₁ S p P w Q →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
      ∀ R T : Subgroup G, R ∈ scriptQPi A (lB A) ⊤ (piOf p) → R ≠ ⊥ →
        Y₀ = (Y₀ ⊓ Subgroup.centralizer (R : Set G)) ⊔ CFSG.Open.pCoreOf 2 Y₀ →
        T ∈ scriptQPi A (lB A) ⊤ (piOf p) → R ≤ T → T ≤ Subgroup.normalizer (R : Set G) →
        Y₀ = (Y₀ ⊓ Subgroup.centralizer (T : Set G)) ⊔ CFSG.Open.pCoreOf 2 Y₀

theorem claim1724DeltaNorm_of_up (hU : Claim1724DeltaUp) : Claim1724DeltaNorm := by
  intro G _ _ A c L Y₀ Y₁ S p P w Q h hJ R hR T hT hRT hTN
  exfalso
  have hT1 : T ≠ ⊥ := fun hbot => hR.prop.2.1 (le_bot_iff.mp (hbot ▸ hRT.le))
  have hTΛ := hU G A c L Y₀ Y₁ S p P w Q h hJ R T hR.prop.1 hR.prop.2.1 hR.prop.2.2 hT hRT.le hTN
  exact absurd (hR.2 ⟨hT, hT1, hTΛ⟩ hRT.le) (not_le_of_gt hRT)

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ Y₁ S : Subgroup G}
  {p : ℕ} {P : Subgroup G} {w : G} {Q : Subgroup G}

end CFSG.RankThree.PartTwo.Sec17
