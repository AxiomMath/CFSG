module

public import CFSG.Open.WalterAbelianSylowTwoMilestoneDefs
public import CFSG.Blueprint.Catalog
public import CFSG.Open.Defs

public section

namespace CFSG.Walter

open scoped MatrixGroups
open CFSG.Open CFSG.Assembly.LowTwoRank

@[expose] def WalterOrderForm : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ P : Sylow 2 G, IsMulCommutative (P : Subgroup G) →
      (∃ f : ℕ, 2 ≤ f ∧ Nonempty (G ≃* PSL(2, GaloisField 2 f))) ∨
      (∃ p f : ℕ, ∃ _hp : Fact p.Prime, Odd p ∧ 0 < f ∧ 5 ≤ p ^ f ∧
          (p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) ∧ Nonempty (G ≃* PSL(2, GaloisField p f))) ∨
      (∃ m : ℕ, 1 ≤ m ∧ Nat.card G = ordRee (3 ^ (2 * m + 1))) ∨
      Nonempty (G ≃* walterJ1)

@[expose] def WalterModelsForm : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ P : Sylow 2 G, IsMulCommutative (P : Subgroup G) →
      (∃ f : ℕ, 2 ≤ f ∧ StatedClassicalModel G .PSL 2 2 f) ∨
      (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
        (p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) ∧ StatedClassicalModel G .PSL 2 p f) ∨
      (∃ f : ℕ, Odd f ∧ 3 ≤ f ∧ Blueprint.ReeTitsModel G .twistedG2 3 f) ∨
      Blueprint.NativeSporadic.IsSporadic G .J1

@[expose] def WalterModelsTauCeti : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ P : Sylow 2 G, IsMulCommutative (P : Subgroup G) →
      (∃ f : ℕ, 2 ≤ f ∧ Models.LieModel G .PSL 2 2 f) ∨
      (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
        (p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) ∧ Models.LieModel G .PSL 2 p f) ∨
      (∃ f : ℕ, Odd f ∧ 3 ≤ f ∧ Models.LieModel G .twistedG2 0 3 f) ∨
      Blueprint.NativeSporadic.IsSporadic G .J1

end CFSG.Walter
