module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight90Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CatalogueThreePrime

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase
open CFSG.ABGLocalTools (IsSylowOf)

@[expose] def Lemma1_1_890 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Data G),
    PartOne.Section8.R856 D → PartOne.Section8.R881 D → PartOne.Section8.R885 D →
    PartOne.Section8.R886 D →
    PartOne.Section8.R887 D → PartOne.Section8.R888 D → PartOne.Section8.R889 D →
    PartOne.Section8.J2NotSL3PiType →
    (∀ L P : Subgroup G, Set880 D L P → ¬ Group.IsSolvable ↥(F08.CentOverO2 D.M L) →
      ∀ Y : Subgroup G, Y ≤ P → Nat.card Y = 3 → Y ∉ MConjSet D.M (ZOf (P ⊓ L)) →
        normalizer (Y : Set G) ≤ D.M) →
    PartOne.Section8.R890 D

@[expose] def LNormal_890 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Data G) (L P : Subgroup G),
    Set880 D L P → PartOne.Section8.R882 D → PartOne.Section8.R885 D → D.M ≤ normalizer (L : Set G)

@[expose] def Prop2_2_890 : Prop :=
  UCK.K318 → PartTwo.Inputs1719.K_CatalogueThreePrimeSz →
  ∀ (G : Type) [Group G] [Finite G] (D : Data G) (L P : Subgroup G),
    Set880 D L P → D.M ≤ normalizer (L : Set G) → PartOne.Section8.R885 D →
    PartOne.Section8.R889 D → ¬ Group.IsSolvable ↥(F08.CentOverO2 D.M L) →
    ∃ (J : Subgroup G) (n : ℕ), J ∈ calC D.M ∧ D.M ≤ normalizer (J : Set G) ∧
      J ≤ F08.CentOverO2 D.M L ∧ IsSz (Bar2 J) n ∧ 3 ≤ n ∧ Odd n

@[expose] def Prop3_5_890 : Prop :=
  J2ThreeBFix_890 →
  ∀ (G : Type) [Group G] [Finite G] (D : Data G) (L P J Y : Subgroup G) (n : ℕ),
    Cfg890 D L P J Y n → Y ∉ MConjSet D.M (ZOf (P ⊓ L)) → PartOne.Section8.R885 D →
    PartOne.Section8.R886 D → PartOne.Section8.R889 D →
    ⁅perfInter890 J (centralizer (Y : Set G)), perfInter890 J (centralizer (Y : Set G))⁆ =
        perfInter890 J (centralizer (Y : Set G)) ∧
      IsSz (Bar2 (perfInter890 J (centralizer (Y : Set G)))) n ∧
      pCoreOf 2 (perfInter890 J (centralizer (Y : Set G))) ≠ ⊥ ∧
      Fstar (perfInter890 J (centralizer (Y : Set G))) =
        pCoreOf 2 (perfInter890 J (centralizer (Y : Set G)))

open scoped commutatorElement Pointwise

@[expose] def Lemma3_1_890 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Data G) (L P J Y : Subgroup G) (n : ℕ),
    Cfg890 D L P J Y n → PartOne.Section8.R885 D → ⁅L, J⁆ ≤ pCoreOf 2 L ⊓ pCoreOf 2 J

@[expose] def Lemma3_2a_890 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Data G) (L P J Y : Subgroup G) (n : ℕ),
    Cfg890 D L P J Y n → PartOne.Section8.R889 D → ⁅L, J⁆ ≤ pCoreOf 2 L ⊓ pCoreOf 2 J →
    perfInter890 J (centralizer (Y : Set G)) ⊔ pCoreOf 2 J = J ∧
      ⁅perfInter890 J (centralizer (Y : Set G)), perfInter890 J (centralizer (Y : Set G))⁆ =
        perfInter890 J (centralizer (Y : Set G)) ∧
      pCoreOf 2 (perfInter890 J (centralizer (Y : Set G))) =
        perfInter890 J (centralizer (Y : Set G)) ⊓ pCoreOf 2 J ∧
      IsSimpleGroup (Bar2 (perfInter890 J (centralizer (Y : Set G)))) ∧
      IsSz (Bar2 (perfInter890 J (centralizer (Y : Set G)))) n

@[expose] def Y3B_890 : Prop :=
  J2OrderThree_890 →
  ∀ (G : Type) [Group G] [Finite G] (D : Data G) (L P J Y : Subgroup G) (n : ℕ),
    Cfg890 D L P J Y n → Y ∉ MConjSet D.M (ZOf (P ⊓ L)) → PartOne.Section8.R885 D →
    PartOne.Section8.R886 D → PartOne.Section8.R889 D →
    (Nat.card (centralizer (barImg_890 L Y : Set (Bar2 L)))).factorization 3 = 2

@[expose] def QuasiOfFstarNe_890 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K : Subgroup G), ⁅K, K⁆ = K → IsSimpleGroup (Bar2 K) →
    Fstar K ≠ pCoreOf 2 K →
    CFSG.Open.IsQuasisimple ↥K ∧ pCoreOf 2 K ≤ centralizer (K : Set G)

@[expose] def Step2Comm_890 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Data G) (L P J Y : Subgroup G) (n : ℕ),
    Cfg890 D L P J Y n →
    ⁅pCoreOf 2 J ⊓ centralizer (Y : Set G), perfInter890 J (centralizer (Y : Set G))⁆ ≤
      perfInter890 J (centralizer (Y : Set G)) ⊓ pCoreOf 2 J

@[expose] def ChiefFactorExists_890 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Data G) (L P J Y : Subgroup G) (n : ℕ),
    Cfg890 D L P J Y n →
    ∃ A B : Subgroup G, LJChief_890 L J A B ∧ ¬ ⁅A, J⁆ ≤ B ∧ ⁅A, pCoreOf 2 J⁆ ≤ B ∧
      ⁅A, pCoreOf 2 L⁆ ≤ B

@[expose] def Step5_890 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Data G) (L P J Y : Subgroup G) (n : ℕ),
    Cfg890 D L P J Y n → PartOne.Section8.R889 D → ∀ A B : Subgroup G, LJChief_890 L J A B →
    ⁅A, pCoreOf 2 J⁆ ≤ B → ¬ ⁅A, J⁆ ≤ B →
    perfInter890 J (centralizer (Y : Set G)) ⊔ pCoreOf 2 J = J →
    ⁅pCoreOf 2 J ⊓ centralizer (Y : Set G), perfInter890 J (centralizer (Y : Set G))⁆ = ⊥ →
    ∀ a ∈ A, (∀ y ∈ Y, ⁅a, y⁆ ∈ B) → a ∈ B

@[expose] def Step6_890 : Prop :=
  J2ThreeBFix_890 →
  ∀ (G : Type) [Group G] [Finite G] (D : Data G) (L P J Y : Subgroup G) (n : ℕ),
    Cfg890 D L P J Y n → PartOne.Section8.R885 D → PartOne.Section8.R889 D →
    ∀ A B : Subgroup G, LJChief_890 L J A B → ⁅A, pCoreOf 2 L⁆ ≤ B →
    (Nat.card (centralizer (barImg_890 L Y : Set (Bar2 L)))).factorization 3 = 2 →
    ∃ a ∈ A, a ∉ B ∧ ∀ y ∈ Y, ⁅a, y⁆ ∈ B

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
