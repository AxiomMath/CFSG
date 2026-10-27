module

public import CFSG.Quasithin.Vol2.GoldschmidtE217R3Star
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch3E213MDefs
public import CFSG.Quasithin.Vol2.GoldschmidtE217Torus

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6 E2 Ch3E213M E217R1

namespace E217R3

variable {G : Type} [Group G] [Finite G]

structure Setting2 (H T M V K : Subgroup G) : Prop where
  toHyp2 : Hyp2 H T M V
  not_solvable : ¬ Group.IsSolvable H
  mem_cComp : K ∈ cComp H
  eq_sup : H = K ⊔ T
  quasisimple : CFSG.Open.IsQuasisimple (↥K ⧸ CFSG.Open.pCore 2 ↥K)
  sqtk : SQTKGroup (E2.StarQuot M H)

@[expose] def R3Pkg1a : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V K : Subgroup G), Setting2 H T M V K →
    (T ⊓ Subgroup.centralizer (V : Set G)).relIndex T < 8 → Case1 H T M K →
    ∀ n : ℕ, 2 ≤ n → (IsPSL 2 2 n ↥(E2.star M H K) ∨ IsSz n ↥(E2.star M H K)) →
    E2.IsBorelIn (E2.star M H K) (E2.star M H (M ⊓ K)) → False

@[expose] def R3Pkg1b : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V K : Subgroup G), Setting2 H T M V K →
    (T ⊓ Subgroup.centralizer (V : Set G)).relIndex T < 8 → Case1 H T M K →
    ∀ p : ℕ, p.Prime → (p % 8 = 1 ∨ p % 8 = 7) → IsPSL 2 p 1 ↥(E2.star M H K) →
    E2.star M H (M ⊓ K) =
      E2.star M H K ⊓ Subgroup.centralizer (zStar H T M K : Set (E2.StarQuot M H)) →
    8 < E2.autCard (E2.star M H T) (E2.star M H K) → False

@[expose] def R3Pkg2a : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V K : Subgroup G), Setting2 H T M V K →
    (T ⊓ Subgroup.centralizer (V : Set G)).relIndex T < 8 → Case2 H T M K →
    ∀ n : ℕ, E2.IsBenderOf n ↥(E2.star M H K) →
    E2.IsBorelIn (E2.star M H K) (E2.star M H (M ⊓ K)) → False

@[expose] def R3Pkg2b : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V K : Subgroup G), Setting2 H T M V K →
    (T ⊓ Subgroup.centralizer (V : Set G)).relIndex T < 8 → Case2 H T M K →
    ∀ n : ℕ, 1 ≤ n → (IsPSL 3 2 n ↥(E2.star M H K) ∨ E2.IsSp4Prime n ↥(E2.star M H K)) →
    E2.IsDiagramNontrivial (E2.star M H T) (E2.star M H K) (E2.star M H (T ⊓ K)) →
    E2.IsBorelIn (E2.star M H K) (E2.star M H (M ⊓ K)) → False

@[expose] def R3Pkg2c : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V K : Subgroup G), Setting2 H T M V K →
    (T ⊓ Subgroup.centralizer (V : Set G)).relIndex T < 8 → Case2 H T M K →
    ∀ p e : ℕ, p.Prime → 3 < p → (e = 1 ∨ e = 2) → (p ^ e % 8 = 1 ∨ p ^ e % 8 = 7) →
    IsPSL 2 p e ↥(E2.star M H K) →
    E2.star M H (M ⊓ K) =
      E2.star M H K ⊓ Subgroup.centralizer (zStar H T M K : Set (E2.StarQuot M H)) →
    8 < E2.autCard (E2.star M H T) (E2.star M H K) → False

@[expose] def R3Pkg2d : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V K : Subgroup G), Setting2 H T M V K →
    (T ⊓ Subgroup.centralizer (V : Set G)).relIndex T < 8 → Case2 H T M K →
    ∀ p : ℕ, p.Prime → p ≠ 2 →
    ((p % 4 = 1 ∧ IsPSU 3 p 1 ↥(E2.star M H K)) ∨
      (p % 4 = 3 ∧ IsPSL 3 p 1 ↥(E2.star M H K) ∧
        E2.InducesOuter (E2.star M H T) (E2.star M H K))) →
    E2.star M H (M ⊓ K) =
      E2.star M H K ⊓ Subgroup.centralizer (zStar H T M K : Set (E2.StarQuot M H)) → False

end E217R3

end CFSG.Quasithin
