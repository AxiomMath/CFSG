module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1T112

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

@[expose] noncomputable def Item1514RQ (Q : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Q (↥L ⧸ aschbacherSolvableCore 3 ↥L) → Item1514 A (lB A) c L

@[expose] def Res1DeltaQ (Q : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Q (↥L ⧸ aschbacherSolvableCore 3 ↥L) →
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) →
    L ≤ delta A (lB A) L

theorem res1DeltaQ_a7 (h142 : Concl142S14) :
    Res1DeltaQ (fun X _ => Nonempty (X ≃* alternatingGroup (Fin 7))) :=
  fun G _ _ A c L hR h7 _ => le_delta_of_a7 hR (h142 G A c L hR.toSec14Std) h7

theorem res1DeltaQ_m22 (h22 : Step142LowerGenM22) (h142 : Concl142S14) :
    Res1DeltaQ (fun X _ => Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22)) :=
  fun G _ _ A c L hR hM _ => le_delta_of_m22 h22 hR (h142 G A c L hR.toSec14Std) hM

@[expose] def Res1ZExclLe (Q : ∀ (X : Type) [Group X], Prop)
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
    L ≤ X → L ≤ delta A (lB A) L → K = X ⊔ CFSG.Open.pCoreOf 2 K →
    omegaA A = {Subgroup.zpowers c} →
    ¬ pPrimeCoreOf 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) ≤
      n155 A K →
    ∀ z : G, orderOf z = 2 → z ∈ CFSG.Open.pCoreOf 2 K →
      z ∈ Subgroup.centralizer (CFSG.Open.pCoreOf 2 K : Set G) → z ∈ CFSG.Open.pCoreOf 2 Y →
      A ≤ Subgroup.centralizer ({z} : Set G) → K ≤ Subgroup.centralizer ({z} : Set G) →
      Subgroup.centralizer ({z} : Set G) ≤ n155 A K →
      ⁅pPrimeCoreOf 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))),
        Subgroup.zpowers z⁆ ≠ ⊥ → False

variable {G : Type} [Group G] [Finite G]

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
