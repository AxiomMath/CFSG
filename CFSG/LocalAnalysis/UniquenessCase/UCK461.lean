module

public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.FFModules (fixSub)
open scoped MatrixGroups

@[expose] def HigmanNatSL2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n : ℕ), LieModel G .PSL 2 2 n →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
      (ρ : Representation (ZMod 2) G V), Function.Injective ρ → ρ.IsIrreducible →
    ∀ D : Subgroup G, Nat.card D = 3 → fixSub ρ D = ⊥ → NatSL2 ρ n

@[expose] def InspJ1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSpor G .J1 → ∀ D : Subgroup G, Nat.card D = 3 →
    ∃ R : Subgroup G, IsPGroup 7 R ∧ IsMulCommutative ↥R ∧ R ≠ ⊥ ∧
      D ≤ normalizer (R : Set G) ∧ ⁅D, R⁆ = R

@[expose] def InspL3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G],
    ((∃ p f : ℕ, p ^ f % 3 = 2 ∧ LieModel G .PSL 3 p f) ∨
      (∃ p f : ℕ, p ^ f % 3 = 1 ∧ LieModel G .PSU 3 p f)) →
    ∀ D : Subgroup G, Nat.card D = 3 →
      ∃ (ℓ : ℕ) (R : Subgroup G), ℓ.Prime ∧ ℓ ≠ 2 ∧ ℓ ≠ 3 ∧ IsPGroup ℓ R ∧ IsMulCommutative ↥R ∧
        R ≠ ⊥ ∧ D ≤ normalizer (R : Set G) ∧ ⁅D, R⁆ = R

@[expose] def InspL2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p f : ℕ), p ≠ 2 → LieModel G .PSL 2 p f →
    CFSG.Open.pRank 3 (⊤ : Subgroup G) = 1 → ∀ D : Subgroup G, Nat.card D = 3 →
      ∃ S : Subgroup G, CFSG.Open.IsElemAbelian 2 S ∧ Nat.card S = 4 ∧
        D ≤ normalizer (S : Set G) ∧ ⁅D, S⁆ = S

@[expose] def L2Exceptional : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p f : ℕ), p ≠ 2 → LieModel G .PSL 2 p f →
    (p ^ f = 5 → LieModel G .PSL 2 2 2) ∧ (p ^ f = 7 → LieModel G .PSL 3 2 1) ∧
      (p ^ f = 9 → CFSG.Open.pRank 3 (⊤ : Subgroup G) = 2)

@[expose] def K46List : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.Open.IsKGroup G →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
      (ρ : Representation (ZMod 2) G V), Function.Injective ρ → ρ.IsIrreducible →
    ∀ D : Subgroup G, Nat.card D = 3 → Subgroup.normalClosure (D : Set G) = ⊤ → fixSub ρ D = ⊥ →
      CFSG.Open.pRank 3 (⊤ : Subgroup G) = 1 → commutator G = ⊤ →
      (∃ p f : ℕ, LieModel G .PSL 2 p f) ∨
      (∃ p f : ℕ, p ^ f % 3 = 2 ∧ LieModel G .PSL 3 p f) ∨
      (∃ p f : ℕ, p ^ f % 3 = 1 ∧ LieModel G .PSU 3 p f) ∨ IsSpor G .J1 ∨
      (∃ (F : Type) (_ : Field F) (_ : Finite F), Odd (Nat.card F) ∧ Nonempty (G ≃* SL(2, F)))

end CFSG.LocalAnalysis.UniquenessCase.UCK
