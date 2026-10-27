module

public import CFSG.RankThree.PartTwo.Sec17.RouteForms
public import CFSG.RankThree.PartTwo.Sec14.Item148StepPoint
public import CFSG.RankThree.PartTwo.Sec14.Item148StepsNHJ
import CFSG.RankThree.PartTwo.Sec14.Item1411HJ

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.GH74.GLS

theorem item142R_of_wired (h : Item142AllS14) : Item142R :=
  fun G _ _ A c L hR => h G A c L hR.toSec14Std

section Item148

theorem item148HJS14_of_wired (h : Item148S14) : Item148HJS14 :=
  fun G _ _ A c L hs _ => h G A c L hs

end Item148

@[expose] noncomputable def Item1444S14 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → Item1444 A (lB A)

@[expose] noncomputable def Step1421R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Fail1411 A (lB A) →
      ∀ c' : G, Subgroup.zpowers c' ∈ gammaA A (lB A) → ∀ L' ∈ lA A c',
        Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.M22)

@[expose] noncomputable def Step1422R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Fail1411 A (lB A) →
      ∀ c' : G, Subgroup.zpowers c' ∈ gammaA A (lB A) → ∀ L' ∈ lA A c',
        IsEmpty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.M22)

@[expose] noncomputable def Item1411_3NHJR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L →
      IsEmpty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
        Item1411_3 A (lB A)

theorem item1411_3_of_hj_wired
    {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G}
    (hR : Sec15R G A c L) (h146 : Item146 A (lB A))
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥) (h142 : Concl142 A (lB A))
    (hN : IsEmpty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
      Item1411_3 A (lB A)) :
    Item1411_3 A (lB A) := by
  by_cases hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)
  · exact rank3II_14_11_3_HJ_of hR.toSec14Std h146 hbot
      (h142 c hR.toSec14Std.toSec13Data.zpowers_mem_omegaA) hJ
  · exact hN (not_nonempty_iff.mp hJ)

end CFSG.RankThree.PartTwo.Sec14
