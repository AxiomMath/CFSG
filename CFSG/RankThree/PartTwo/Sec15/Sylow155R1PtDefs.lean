module

public import CFSG.RankThree.PartTwo.Sec15.Gagen155Y1Defs
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Defs

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

@[expose] def Res1RoutePt (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G)
    (L : Subgroup G) : Prop :=
  ((omegaA A).ncard ≤ 9 ∧ ¬ Sec8.IsZ3PGLThreePi (lBarA c L A) ∧
      IsEmpty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M12) ∧
      IsEmpty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)) ∨
    ((omegaA A).ncard < 3 ∧
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))

@[expose] def Step155HostE0WRes1TypeFPt
    (Pt : ∀ (G : Type) [Group G] [Finite G], Subgroup G → G → Subgroup G → Prop)
    (P : ∀ (Y : Type) [Group Y], Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Pt G A c L →
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) →
    Sec14Std G A c L → ∀ X K Y M T P' : Subgroup G, Ctx155 A X K Y M T → MaxT155 A X K T →
    Above155w A X → End155N A X K Y M T P' → Item146 A (lB A) →
    CFSG.Open.pCoreOf 2 Y ≤ P' →
    delta A (lB A) M ≤ Subgroup.normalizer (X : Set G) →
    ∀ Yc : Subgroup (Res1Q A L), Res1AtOf A c L M Yc → IsSimpleGroup ↥Yc → P ↥Yc →
    layerOddPreimage (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) ≤
      Subgroup.centralizer (A : Set G) →
    layerOddPreimage (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) =
      pPrimeCoreOf 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) →
    (∀ u : ↥(Res1C A L), (u : G) ∈
        pPrimeCoreOf 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) →
      (∀ y ∈ Yc, QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) u * y =
        y * QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) u) → u = 1) →
    (∃ x : ↥(Res1C A L),
      (x : G) ∈ CFSG.Open.pCoreOf 2 Y ⊓ Subgroup.centralizer (A : Set G) ∧
        ∃ y ∈ Yc, QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) x * y ≠
          y * QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) x) →
    pPrimeCoreOf 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) ≤
      n155 A K

@[expose] def Step155HostE0WRes1TypePt
    (Pt : ∀ (G : Type) [Group G] [Finite G], Subgroup G → G → Subgroup G → Prop)
    (P : ∀ (Y : Type) [Group Y], Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Pt G A c L →
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) →
    Sec14Std G A c L → ∀ X K Y M T P' : Subgroup G, Ctx155 A X K Y M T → MaxT155 A X K T →
    Above155w A X → End155N A X K Y M T P' → Item146 A (lB A) →
    CFSG.Open.pCoreOf 2 Y ≤ P' →
    delta A (lB A) M ≤ Subgroup.normalizer (X : Set G) →
    ∀ Yc : Subgroup (Res1Q A L), Res1AtOf A c L M Yc → IsSimpleGroup ↥Yc → P ↥Yc →
      layerOddPreimage (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) ≤
        n155 A K

@[expose] def Step155HostE0WRes1RPt
    (Pt : ∀ (G : Type) [Group G] [Finite G], Subgroup G → G → Subgroup G → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Pt G A c L →
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) →
      Step155HostE0WRes1 A c L

@[expose] def Res1J2Pt (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G)
    (L : Subgroup G) : Prop :=
  (omegaA A).ncard < 3 ∧
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)

end CFSG.RankThree.PartTwo.Sec15
