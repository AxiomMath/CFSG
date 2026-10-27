module

public import CFSG.RankThree.GroupTheory.SteinbergCEQuaternionDihedral
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.RankThree.GroupTheory

namespace FiveAction

@[expose] def Shape (S A : Type) [Group S] [Group A] (φ : A →* MulAut S) : Prop :=
  (IsElementaryAbelian 2 S ∧ Nat.card S = 16 ∧
      ∀ U : Subgroup S, (∀ a : A, ∀ x ∈ U, φ a x ∈ U) → U = ⊥ ∨ U = ⊤) ∨
    Nonempty (S ≃* QD32)

@[expose] def FixedVector : Prop :=
  ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 →
    ∀ (S A : Type) [Group S] [Finite S] [Group A] [Finite A] (φ : A →* MulAut S),
      Nat.card φ.range = 5 → Shape S A φ →
      ∀ (W : Type) [AddCommGroup W] [Module (ZMod q) W] [FiniteDimensional (ZMod q) W]
        (ρ : Representation (ZMod q) (S ⋊[φ] A) W),
        ρ.IsIrreducible → Function.Injective (ρ.comp SemidirectProduct.inl) →
        ∃ s : S, s ≠ 1 ∧
          1 ≤ Module.finrank (ZMod q)
            (Module.End.eigenspace (ρ (SemidirectProduct.inl s)) 1)

@[expose] def ScalarBound : Prop :=
  ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → (q % 5 = 2 ∨ q % 5 = 3) →
    ∀ (S A : Type) [Group S] [Finite S] [Group A] [Finite A] (φ : A →* MulAut S),
      Nat.card φ.range = 5 → Shape S A φ →
      ∀ b : A, (∀ s : S, φ b s = s) → (∀ a : A, a * b = b * a) → orderOf b = 5 →
      ∀ (W : Type) [AddCommGroup W] [Module (ZMod q) W] [FiniteDimensional (ZMod q) W]
        (ρ : Representation (ZMod q) (S ⋊[φ] A) W),
        ρ.IsIrreducible → Function.Injective (ρ.comp SemidirectProduct.inl) →
        ρ (SemidirectProduct.inr b) ≠ 1 →
        ∃ s : S, s ≠ 1 ∧
          8 ≤ Module.finrank (ZMod q)
            (Module.End.eigenspace (ρ (SemidirectProduct.inl s)) 1)

end FiveAction

end CFSG.RankThree.PartOne
