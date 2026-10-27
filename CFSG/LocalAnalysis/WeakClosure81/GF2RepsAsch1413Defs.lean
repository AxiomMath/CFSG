module

public import CFSG.LocalAnalysis.WeakClosure81.W18Asch66

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)

@[expose] def Shape1413Prime (L : Type) [Group L] : Prop :=
  LieModel L .PSL 3 3 1 ∨ ∃ p : ℕ, p.Prime ∧ 5 < p ∧ LieModel L .PSp 2 p 1

@[expose] def Asch1413For (S : ∀ (L : Type) [Group L], Prop) : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ ρ : Q →* MulAut V, Function.Injective ρ →
    ∀ (L A : Subgroup Q), genFittingFStar Q = L → S ↥L → Nat.card A = 4 →
      IsElemAbelian 2 A → IsQuadraticOn ρ A → False

@[expose] def Asch1413RedFor (S : ∀ (L : Type) [Group L], Prop) : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ ρ : Q →* MulAut V, Function.Injective ρ →
    ∀ (L A : Subgroup Q), genFittingFStar Q = L → S ↥L → Nat.card A = 4 →
      IsElemAbelian 2 A → IsQuadraticOn ρ A →
      (∀ v : V, (∀ l ∈ L, ρ l v = v) → v = 1) → False

@[expose] def Asch5_14_13Prime : Prop := Asch1413For Shape1413Prime

end CFSG.LocalAnalysis.WeakClosure81

end
