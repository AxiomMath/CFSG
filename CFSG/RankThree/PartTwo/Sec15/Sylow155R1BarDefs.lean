module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Defs
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1OpenSplit

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

@[expose] def Step155HostE0WRes1TypeFBar (Q : ∀ (X : Type) [Group X], Prop)
    (P : ∀ (Y : Type) [Group Y], Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Q (↥L ⧸ aschbacherSolvableCore 3 ↥L) →
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

theorem step155HostE0WRes1TypeFBar_of_type_or {Q : ∀ (X : Type) [Group X], Prop}
    {P P₁ P₂ : ∀ (Y : Type) [Group Y], Prop} (hP : ∀ (Y : Type) [Group Y], P Y → P₁ Y ∨ P₂ Y)
    (h₁ : Step155HostE0WRes1TypeFBar Q P₁) (h₂ : Step155HostE0WRes1TypeFBar Q P₂) :
    Step155HostE0WRes1TypeFBar Q P := by
  intro G _ _ A c L hR hq hN hS X K Y M T P' hC hmax habove hE h146 hRP hIX Yc hY hsimple hP'
    hEA hEO hcomm hfield
  rcases hP _ hP' with hP₁ | hP₂
  · exact h₁ G A c L hR hq hN hS X K Y M T P' hC hmax habove hE h146 hRP hIX Yc hY hsimple hP₁
      hEA hEO hcomm hfield
  · exact h₂ G A c L hR hq hN hS X K Y M T P' hC hmax habove hE h146 hRP hIX Yc hY hsimple hP₂
      hEA hEO hcomm hfield

theorem step155HostE0WRes1TypeFBar_open_of_split {Q : ∀ (X : Type) [Group X], Prop}
    (hL2 : Step155HostE0WRes1TypeFBar Q Res1OpenL2Type)
    (hSU3 : Step155HostE0WRes1TypeFBar Q Res1OpenSU3Type) :
    Step155HostE0WRes1TypeFBar Q Res1OpenType :=
  step155HostE0WRes1TypeFBar_of_type_or (fun _ _ h => h) hL2 hSU3

@[expose] def Step155HostE0WRes1TypeFBarLe (Q : ∀ (X : Type) [Group X], Prop)
    (P : ∀ (Y : Type) [Group Y], Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Q (↥L ⧸ aschbacherSolvableCore 3 ↥L) →
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
    L ≤ X →
    pPrimeCoreOf 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) ≤
      n155 A K

@[expose] def Step155HostE0WRes1TypeFBarNotLe (Q : ∀ (X : Type) [Group X], Prop)
    (P : ∀ (Y : Type) [Group Y], Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Q (↥L ⧸ aschbacherSolvableCore 3 ↥L) →
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
    ¬ L ≤ X →
    pPrimeCoreOf 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) ≤
      n155 A K

theorem step155HostE0WRes1TypeFBar_of_le {Q : ∀ (X : Type) [Group X], Prop}
    {P : ∀ (Y : Type) [Group Y], Prop} (h₁ : Step155HostE0WRes1TypeFBarLe Q P)
    (h₂ : Step155HostE0WRes1TypeFBarNotLe Q P) : Step155HostE0WRes1TypeFBar Q P := by
  intro G _ _ A c L hR hq hN hS X K Y M T P' hC hmax habove hE h146 hRP hIX Yc hY hsimple hP
    hEA hEO hcomm hfield
  by_cases hLX : L ≤ X
  · exact h₁ G A c L hR hq hN hS X K Y M T P' hC hmax habove hE h146 hRP hIX Yc hY hsimple hP
      hEA hEO hcomm hfield hLX
  · exact h₂ G A c L hR hq hN hS X K Y M T P' hC hmax habove hE h146 hRP hIX Yc hY hsimple hP
      hEA hEO hcomm hfield hLX

end CFSG.RankThree.PartTwo.Sec15
