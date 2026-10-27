module

public import CFSG.RankThree.PartTwo.Sec15.Ronan152SixBigDefs
public import CFSG.RankThree.PartTwo.Sec15.Y4CoreProofDefs
public import CFSG.RankThree.PartTwo.Sec15.Item158StepsProof159
import CFSG.RankThree.PartTwo.Sec15.Item15Res6ProofTools
public import CFSG.RankThree.PartTwo.Sec14.Concl142HJ

public section

namespace CFSG.RankThree.PartTwo.Sec15.Ronan154Big

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def Y4CoreMemAt (A : Subgroup G) : Prop :=
  ∀ M ∈ scriptY2 A, generalizedFitting ↥M = CFSG.pCore 2 ↥M →
    ∀ J ∈ comp3In (delta A (lB A) M), A ≤ Subgroup.normalizer (J : Set G) →
      J ∈ scriptY0 A (lB A)

@[expose] noncomputable def Y4BigNHJR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ¬ AllPointsHJ A → ∀ X ∈ scriptY4 A (lB A), Big152 X

theorem not_allPointsHJ_of_ctx159 {A L : Subgroup G} {c : G} (ctx : Ctx159 G A c L) :
    ¬ AllPointsHJ A :=
  Proof15Res6.not_allPointsHJ_of_isEmpty ctx.toSec15R.toSec14Std
    (Proof15Res6.isEmpty_j2_of_types ctx.types)

end CFSG.RankThree.PartTwo.Sec15.Ronan154Big
