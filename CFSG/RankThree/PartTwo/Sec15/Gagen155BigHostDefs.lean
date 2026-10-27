module

public import CFSG.RankThree.PartTwo.Sec15.Ronan152SixBigDefs
public import CFSG.RankThree.PartTwo.Sec15.Gagen155Y1Defs
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Defs

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

@[expose] def Step155HostE0WBig (A : Subgroup G) (c : G) (L : Subgroup G) : Prop :=
  Sec14Std G A c L → ∀ X K Y M T P : Subgroup G, Ctx155 A X K Y M T → Big152 X →
    MaxT155 A X K T → Above155w A X → End155N A X K Y M T P → Item146 A (lB A) →
    CFSG.Open.pCoreOf 2 Y ≤ P →
    delta A (lB A) M ≤ Subgroup.normalizer (X : Set G) →
      layerOddPreimage (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) ≤
        n155 A K

@[expose] def Step155HostE0WRBig : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step155HostE0WBig A c L

@[expose] noncomputable def Step155FrattiniNWPBig (A : Subgroup G) (c : G) (L : Subgroup G) :
    Prop :=
  Sec14Std G A c L → ∀ X K Y M T P : Subgroup G, Ctx155 A X K Y M T → Big152 X →
    MaxT155 A X K T → Above155w A X → End155N A X K Y M T P → CFSG.Open.pCoreOf 2 Y ≤ P →
      b155 A M X ≤ n155 A K → delta A (lB A) M ≤ n155 A K

@[expose] noncomputable def Step155FrattiniNWPRBig : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step155FrattiniNWPBig A c L

@[expose] def Step155HostE0WRes1Big (A : Subgroup G) (c : G) (L : Subgroup G) : Prop :=
  Sec14Std G A c L → ∀ X K Y M T P : Subgroup G, Ctx155 A X K Y M T → Big152 X →
    MaxT155 A X K T → Above155w A X → End155N A X K Y M T P → Item146 A (lB A) →
    CFSG.Open.pCoreOf 2 Y ≤ P →
    delta A (lB A) M ≤ Subgroup.normalizer (X : Set G) →
    Res1At A c L M →
      layerOddPreimage (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) ≤
        n155 A K

@[expose] def Step155HostE0WRes1TypePtBig
    (Pt : ∀ (G : Type) [Group G] [Finite G], Subgroup G → G → Subgroup G → Prop)
    (P : ∀ (Y : Type) [Group Y], Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Pt G A c L →
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) →
    Sec14Std G A c L → ∀ X K Y M T P' : Subgroup G, Ctx155 A X K Y M T → Big152 X →
    MaxT155 A X K T → Above155w A X → End155N A X K Y M T P' → Item146 A (lB A) →
    CFSG.Open.pCoreOf 2 Y ≤ P' →
    delta A (lB A) M ≤ Subgroup.normalizer (X : Set G) →
    ∀ Yc : Subgroup (Res1Q A L), Res1AtOf A c L M Yc → IsSimpleGroup ↥Yc → P ↥Yc →
      layerOddPreimage (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) ≤
        n155 A K

@[expose] def Step155HostE0WRes1RPtBig
    (Pt : ∀ (G : Type) [Group G] [Finite G], Subgroup G → G → Subgroup G → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Pt G A c L →
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) →
      Step155HostE0WRes1Big A c L

@[expose] def RouteHostJ2SmallBig : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (b : G) (Lb : Subgroup G),
    Sec15R G A b Lb → (omegaA A).ncard ≤ 3 →
    Nonempty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.J2) →
    Step155HostE0WBig A b Lb

@[expose] def RouteHostJ2LtBig : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (b : G) (Lb : Subgroup G),
    Sec15R G A b Lb → (omegaA A).ncard < 3 →
    Nonempty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.J2) →
    Step155HostE0WBig A b Lb

@[expose] def RouteHostGoodBig : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (b : G) (Lb : Subgroup G),
    Sec15R G A b Lb → (omegaA A).ncard ≤ 9 → ¬ Sec8.IsZ3PGLThreePi (lBarA b Lb A) →
    IsEmpty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.M12) →
    IsEmpty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.J2) →
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers b : Set G) →
    Step155HostE0WBig A b Lb

theorem step155HostE0WBig_of {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Step155HostE0W A c L) : Step155HostE0WBig A c L :=
  fun hS X K Y M T P hC _ hmax hab hE h146 hRP hIX =>
    h hS X K Y M T P hC hmax hab hE h146 hRP hIX

end CFSG.RankThree.PartTwo.Sec15
