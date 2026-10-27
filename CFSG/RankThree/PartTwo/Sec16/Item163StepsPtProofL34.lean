module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartTwo.Sec15.HypR
public import CFSG.RankThree.PartTwo.Sec15.Notation
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

@[expose] def Step163NoL34 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃*
      CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)) →
    Nat.card (A ⊓ L : Subgroup G) = 9 → (scriptY0 A (lB A)).Nonempty → False

end CFSG.RankThree.PartTwo.Sec16
