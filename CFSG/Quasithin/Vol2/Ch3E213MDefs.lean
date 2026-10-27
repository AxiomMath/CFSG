module

public import CFSG.Quasithin.Vol2.Ch3nE2
public import CFSG.Quasithin.Background.E2Two

public section

namespace CFSG.Quasithin.Ch3E213M

open CFSG.Open CFSG.QuasithinUnique B6

@[expose] def E213Concl {G : Type} [Group G] (H T M V : Subgroup G) : Prop :=
  ∃ g ∈ H, E2.Pair (Ch3n.pairI V g) (T ⊓ Ch3n.pairI V g) (M ⊓ Ch3n.pairI V g) V g ∧
    CharTwo (Ch3n.pairI V g) ∧ Ch3n.pairI V g ≠ V ∧
    (kerIn (M ⊓ Ch3n.pairI V g) (Ch3n.pairI V g) ⊓ V).relIndex V ≤
      (V ⊓ conjSub g V).relIndex (kerIn (M ⊓ Ch3n.pairI V g) (Ch3n.pairI V g) ⊓ V)

structure Setting {G : Type} [Group G] [Finite G] (H T M V K : Subgroup G) : Prop where
  hyp : E2.Hyp28 H T M V
  charTwo : CharTwo H
  not_solvable : ¬ Group.IsSolvable H
  four_le : 4 ≤ (V ⊓ pCoreOf 2 H).relIndex V
  mem_cComp : K ∈ cComp H
  eq_sup : H = K ⊔ T
  quasisimple : CFSG.Open.IsQuasisimple (↥K ⧸ CFSG.Open.pCore 2 ↥K)
  sqtk : SQTKGroup (E2.StarQuot M H)

@[expose] def Case1 {G : Type} [Group G] (H T M K : Subgroup G) : Prop :=
  kerIn M H = pCoreOf 2 H ∧ ∃ t ∈ T, cjSub t K ≠ K ∧ M = (M ⊓ K) ⊔ cjSub t (M ⊓ K) ⊔ T

@[expose] def Case2 {G : Type} [Group G] (H T M K : Subgroup G) : Prop :=
  T ≤ Subgroup.normalizer (K : Set G) ∧
    ∀ x : G, x ∈ kerIn M H ↔ x ∈ K ⊔ pCoreOf 2 H ∧
      ∀ y ∈ K ⊔ pCoreOf 2 H, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 H

@[expose] def zStar {G : Type} [Group G] (H T M K : Subgroup G) : Subgroup (E2.StarQuot M H) :=
  E2.star M H (T ⊓ K) ⊓ Subgroup.centralizer (E2.star M H (T ⊓ K) : Set (E2.StarQuot M H))

@[expose] def PkgL2Paired : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V K : Subgroup G), Setting H T M V K →
    Case1 H T M K → ∀ n : ℕ, 2 ≤ n → IsPSL 2 2 n ↥(E2.star M H K) →
    E2.IsBorelIn (E2.star M H K) (E2.star M H (M ⊓ K)) → E213Concl H T M V

@[expose] def PkgSzPaired : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V K : Subgroup G), Setting H T M V K →
    Case1 H T M K → ∀ n : ℕ, 2 ≤ n → IsSz n ↥(E2.star M H K) →
    E2.IsBorelIn (E2.star M H K) (E2.star M H (M ⊓ K)) → E213Concl H T M V

@[expose] def PkgOddPaired : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V K : Subgroup G), Setting H T M V K →
    Case1 H T M K → ∀ p : ℕ, p.Prime → (p % 8 = 1 ∨ p % 8 = 7) →
    IsPSL 2 p 1 ↥(E2.star M H K) →
    E2.star M H (M ⊓ K) =
      E2.star M H K ⊓ Subgroup.centralizer (zStar H T M K : Set (E2.StarQuot M H)) →
    8 < E2.autCard (E2.star M H T) (E2.star M H K) → E213Concl H T M V

@[expose] def PkgBenderSingle : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V K : Subgroup G), Setting H T M V K →
    Case2 H T M K → ∀ n : ℕ, E2.IsBenderOf n ↥(E2.star M H K) →
    E2.IsBorelIn (E2.star M H K) (E2.star M H (M ⊓ K)) → E213Concl H T M V

@[expose] def PkgL3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V K : Subgroup G), Setting H T M V K →
    Case2 H T M K → ∀ n : ℕ, 1 ≤ n → IsPSL 3 2 n ↥(E2.star M H K) →
    E2.IsDiagramNontrivial (E2.star M H T) (E2.star M H K) (E2.star M H (T ⊓ K)) →
    E2.IsBorelIn (E2.star M H K) (E2.star M H (M ⊓ K)) → E213Concl H T M V

@[expose] def PkgSp4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V K : Subgroup G), Setting H T M V K →
    Case2 H T M K → ∀ n : ℕ, 1 ≤ n → E2.IsSp4Prime n ↥(E2.star M H K) →
    E2.IsDiagramNontrivial (E2.star M H T) (E2.star M H K) (E2.star M H (T ⊓ K)) →
    E2.IsBorelIn (E2.star M H K) (E2.star M H (M ⊓ K)) → E213Concl H T M V

@[expose] def PkgOddSingle : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V K : Subgroup G), Setting H T M V K →
    Case2 H T M K → ∀ p e : ℕ, p.Prime → 3 < p → (e = 1 ∨ e = 2) →
    (p ^ e % 8 = 1 ∨ p ^ e % 8 = 7) → IsPSL 2 p e ↥(E2.star M H K) →
    E2.star M H (M ⊓ K) =
      E2.star M H K ⊓ Subgroup.centralizer (zStar H T M K : Set (E2.StarQuot M H)) →
    8 < E2.autCard (E2.star M H T) (E2.star M H K) → E213Concl H T M V

@[expose] def PkgOddL3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V K : Subgroup G), Setting H T M V K →
    Case2 H T M K → ∀ p : ℕ, p.Prime → p ≠ 2 →
    ((p % 4 = 1 ∧ IsPSU 3 p 1 ↥(E2.star M H K)) ∨
      (p % 4 = 3 ∧ IsPSL 3 p 1 ↥(E2.star M H K) ∧
        E2.InducesOuter (E2.star M H T) (E2.star M H K))) →
    E2.star M H (M ⊓ K) =
      E2.star M H K ⊓ Subgroup.centralizer (zStar H T M K : Set (E2.StarQuot M H)) →
    E213Concl H T M V

end CFSG.Quasithin.Ch3E213M
