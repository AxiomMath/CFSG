module

public import CFSG.Quasithin.Vol2.Ch3E213MDefs

public section

namespace CFSG.Quasithin.Ch3E215M

open CFSG.Open CFSG.QuasithinUnique B6 Ch3E213M

@[expose] def E215DataOf {G : Type} [Group G] (X M V : Subgroup G) (g : G) : Prop :=
  (kerIn M X ⊓ V).relIndex V < (V ⊓ conjSub g V).relIndex (kerIn M X ⊓ V) ∨
    (M ≤ Subgroup.normalizer (V : Set G) →
      ⁅kerIn M X ⊓ V, conjSub g (kerIn M X ⊓ V)⁆ = ⊥)

@[expose] def E215Concl {G : Type} [Group G] (H T M V : Subgroup G) : Prop :=
  ∃ g ∈ H, E2.Pair (Ch3n.pairI V g) (T ⊓ Ch3n.pairI V g) (M ⊓ Ch3n.pairI V g) V g ∧
    CharTwo (Ch3n.pairI V g) ∧ Ch3n.pairI V g ≠ V ∧
    (kerIn (M ⊓ Ch3n.pairI V g) (Ch3n.pairI V g) ⊓ V).relIndex V ≤
      (V ⊓ conjSub g V).relIndex (kerIn (M ⊓ Ch3n.pairI V g) (Ch3n.pairI V g) ⊓ V) ∧
    E215DataOf (Ch3n.pairI V g) (M ⊓ Ch3n.pairI V g) V g

@[expose] def PkgL2Paired215 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V K : Subgroup G), Setting H T M V K →
    Case1 H T M K → ∀ n : ℕ, 2 ≤ n → IsPSL 2 2 n ↥(E2.star M H K) →
    E2.IsBorelIn (E2.star M H K) (E2.star M H (M ⊓ K)) → E215Concl H T M V

@[expose] def PkgSzPaired215 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V K : Subgroup G), Setting H T M V K →
    Case1 H T M K → ∀ n : ℕ, 2 ≤ n → IsSz n ↥(E2.star M H K) →
    E2.IsBorelIn (E2.star M H K) (E2.star M H (M ⊓ K)) → E215Concl H T M V

@[expose] def PkgOddPaired215 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V K : Subgroup G), Setting H T M V K →
    Case1 H T M K → ∀ p : ℕ, p.Prime → (p % 8 = 1 ∨ p % 8 = 7) →
    IsPSL 2 p 1 ↥(E2.star M H K) →
    E2.star M H (M ⊓ K) =
      E2.star M H K ⊓ Subgroup.centralizer (zStar H T M K : Set (E2.StarQuot M H)) →
    8 < E2.autCard (E2.star M H T) (E2.star M H K) → E215Concl H T M V

@[expose] def PkgBenderSingle215 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V K : Subgroup G), Setting H T M V K →
    Case2 H T M K → ∀ n : ℕ, E2.IsBenderOf n ↥(E2.star M H K) →
    E2.IsBorelIn (E2.star M H K) (E2.star M H (M ⊓ K)) → E215Concl H T M V

@[expose] def PkgL3215 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V K : Subgroup G), Setting H T M V K →
    Case2 H T M K → ∀ n : ℕ, 1 ≤ n → IsPSL 3 2 n ↥(E2.star M H K) →
    E2.IsDiagramNontrivial (E2.star M H T) (E2.star M H K) (E2.star M H (T ⊓ K)) →
    E2.IsBorelIn (E2.star M H K) (E2.star M H (M ⊓ K)) → E215Concl H T M V

@[expose] def PkgSp4215 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V K : Subgroup G), Setting H T M V K →
    Case2 H T M K → ∀ n : ℕ, 1 ≤ n → E2.IsSp4Prime n ↥(E2.star M H K) →
    E2.IsDiagramNontrivial (E2.star M H T) (E2.star M H K) (E2.star M H (T ⊓ K)) →
    E2.IsBorelIn (E2.star M H K) (E2.star M H (M ⊓ K)) → E215Concl H T M V

@[expose] def PkgOddSingle215 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V K : Subgroup G), Setting H T M V K →
    Case2 H T M K → ∀ p e : ℕ, p.Prime → 3 < p → (e = 1 ∨ e = 2) →
    (p ^ e % 8 = 1 ∨ p ^ e % 8 = 7) → IsPSL 2 p e ↥(E2.star M H K) →
    E2.star M H (M ⊓ K) =
      E2.star M H K ⊓ Subgroup.centralizer (zStar H T M K : Set (E2.StarQuot M H)) →
    8 < E2.autCard (E2.star M H T) (E2.star M H K) → E215Concl H T M V

@[expose] def PkgOddL3215 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V K : Subgroup G), Setting H T M V K →
    Case2 H T M K → ∀ p : ℕ, p.Prime → p ≠ 2 →
    ((p % 4 = 1 ∧ IsPSU 3 p 1 ↥(E2.star M H K)) ∨
      (p % 4 = 3 ∧ IsPSL 3 p 1 ↥(E2.star M H K) ∧
        E2.InducesOuter (E2.star M H T) (E2.star M H K))) →
    E2.star M H (M ⊓ K) =
      E2.star M H K ⊓ Subgroup.centralizer (zStar H T M K : Set (E2.StarQuot M H)) →
    E215Concl H T M V

end CFSG.Quasithin.Ch3E215M
