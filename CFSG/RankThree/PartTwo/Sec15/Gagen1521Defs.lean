module

public import CFSG.RankThree.PartTwo.Sec15.Item15Steps

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise

@[expose] noncomputable def Step1521T : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y, Ctx1514 A (lB A) c L Y →
      ∀ (p : ℕ) (P : Subgroup G), Data1519 A (lB A) L p P →
        ∀ X ∈ scriptY2 A, P ≤ X →
          P ≤ inSubgroup CFSG.solvableRadical (pPrimeCoreOf 3 (delta A (lB A) X)) →
          ∃ T ∈ scriptQPiStar A (lB A) ⊤ (piOf 2),
            ((P ⊔ T : Subgroup G) : Set G) = (T : Set G) * (P : Set G)

@[expose] noncomputable def Step1521CY : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y, Ctx1514 A (lB A) c L Y →
      ∀ (p : ℕ) (P : Subgroup G), Data1519 A (lB A) L p P →
        ¬ CFSG.Open.pCoreOf 2 Y ≤ Subgroup.centralizer ({c} : Set G)

@[expose] def KS1521SubTwoCore : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), 1 ≤ n → Sec4.IsoLThreePi X 2 n →
    ∀ (K : Subgroup X) (N : Subgroup ↥K) [N.Normal], IsPGroup 2 ↥N →
      ∀ (r f : ℕ) [Fact r.Prime], IsLThreeEpsAt (↥K ⧸ N) r f → N = ⊥

end CFSG.RankThree.PartTwo.Sec15
