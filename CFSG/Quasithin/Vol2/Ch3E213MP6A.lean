module

public import CFSG.Quasithin.Vol2.Ch3E213MSp4
public import CFSG.Quasithin.Vol2.Ch3E213MSp4Irr

public section

namespace CFSG.Quasithin.Ch3E213M

open CFSG.Open CFSG.QuasithinUnique B6
open CFSG.Quasithin.SteinbergBS (rootLong)

@[expose] def PkgSp4Diag : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V K : Subgroup G), Setting H T M V K →
    Case2 H T M K →
    E2.IsDiagramNontrivial (E2.star M H T) (E2.star M H K) (E2.star M H (T ⊓ K)) →
    E2.IsBorelIn (E2.star M H K) (E2.star M H (M ⊓ K)) →
    ∀ (k : Type) [Field k] [Finite k] [CharP k 2] (n : ℕ), 2 ≤ n → Nat.card k = 2 ^ n →
    ∀ D : Sp4Data H T M V K k, ∀ μ : k, μ ≠ 0 → coordIn D.θ V ≤ zLine 1 μ →
    E213Concl H T M V

@[expose] def PkgSp4Transv : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V K : Subgroup G), Setting H T M V K →
    Case2 H T M K →
    E2.IsDiagramNontrivial (E2.star M H T) (E2.star M H K) (E2.star M H (T ⊓ K)) →
    E2.IsBorelIn (E2.star M H K) (E2.star M H (M ⊓ K)) →
    ∀ (k : Type) [Field k] [Finite k] [CharP k 2] (n : ℕ), 2 ≤ n → Nat.card k = 2 ^ n →
    ∀ D : Sp4Data H T M V K k, coordIn D.θ V ⊓ rootLong k ≠ ⊥ → E213Concl H T M V

@[expose] def PkgSp4C2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V K : Subgroup G), Setting H T M V K →
    Case2 H T M K →
    E2.IsDiagramNontrivial (E2.star M H T) (E2.star M H K) (E2.star M H (T ⊓ K)) →
    E2.IsBorelIn (E2.star M H K) (E2.star M H (M ⊓ K)) →
    ∀ (k : Type) [Field k] [Finite k] [CharP k 2] (n : ℕ), 2 ≤ n → Nat.card k = 2 ^ n →
    ∀ D : Sp4Data H T M V K k, coordIn D.θ V ⊓ rootLong k = ⊥ →
    (∀ μ : k, μ ≠ 0 → ¬ coordIn D.θ V ≤ zLine 1 μ) → E213Concl H T M V

end CFSG.Quasithin.Ch3E213M
