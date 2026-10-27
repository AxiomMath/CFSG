module

public import CFSG.RankThree.PartTwo.Sec4.Notation

public section

namespace CFSG.RankThree.PartTwo.KFacts

@[expose] def KS18GL33 : Prop :=
  ∀ (V : Type) [Group V] [Finite V], CFSG.Assembly.IsElemAbelian 3 (⊤ : Subgroup V) →
    Nat.card V = 27 → ∀ F : Subgroup V, Nat.card F = 9 → ∀ X : Subgroup (MulAut V),
      (∀ σ ∈ X, F.map σ.toMonoidHom = F) →
      Sec4.IsExtOf X (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))
        (Multiplicative (ZMod 3) × Multiplicative (ZMod 3)) →
      ∃ σ ∈ X, (∀ f ∈ F, σ f = f) ∧ (∀ v : V, σ v * v⁻¹ ∈ F) ∧ ∀ v : V, v ∉ F → σ v ≠ v

end CFSG.RankThree.PartTwo.KFacts
