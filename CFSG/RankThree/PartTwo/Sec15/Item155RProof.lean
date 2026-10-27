module

public import CFSG.RankThree.PartTwo.Sec15.Item1514StepsRoute
public import CFSG.RankThree.PartTwo.Sec15.Item155RProofUp
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS

@[expose] noncomputable def Item154R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Item154 A (lB A) L

@[expose] noncomputable def Item154HJR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L →
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
        Item154 A (lB A) L

@[expose] noncomputable def Step155UpR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step155Up A c L

@[expose] noncomputable def Step155UpPiR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step155UpPi A c L

theorem step155UpR_of_piR (h : Step155UpPiR) : Step155UpR :=
  fun G _ _ A c L hR => step155Up_of_pi (h G A c L hR)

@[expose] noncomputable def Step155NR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step155N A c L

theorem step155NR_of_claim153NormalR (h149 : Sec16.Item149S14) (hn : Claim153NormalR) :
    Step155NR :=
  fun G _ _ A c L hR =>
    step155N_of_claim153Normal (h149 G A c L hR.toSec14Std) (hn G A c L hR)

@[expose] noncomputable def Item155HJR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L →
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
        Item155 A (lB A)

theorem item155HJR_of_item155R (h : Item155R) : Item155HJR :=
  fun G _ _ A c L hR _ => h G A c L hR

end CFSG.RankThree.PartTwo.Sec15
