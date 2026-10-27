module

public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeNbrKnownDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint TableB

@[expose] def GGTwE6BigLabel (lab' : LargeEvenLabel) : Prop :=
  lab' = ⟨.D, 4, 1⟩ ∨ lab' = ⟨.triD4, 0, 1⟩ ∨ lab' = ⟨.twA, 5, 1⟩ ∨ lab' = ⟨.twA, 4, 1⟩ ∨
    lab' = ⟨.twD, 5, 1⟩

@[expose] def GGTwE6BigSetting {R : Type} [Group R] (I : Set (MulAut R)) {L' : Type} [Group L']
    (ψ : L' →* R) (A : Subgroup (MulAut L')) (a₀ : MulAut L') (J₁ : Subgroup L') : Prop :=
  IsElemAbelian 3 A ∧ (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) ∧ 3 ^ 5 ≤ Nat.card A ∧
    a₀ ∈ A ∧ a₀ ≠ 1 ∧ IsComponentOf J₁ (ggFix a₀)

@[expose] def GGTwE6BigLabelsKnown : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → lab.tag = .twE6 → lab.n = 1 →
    LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
        ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
        ∀ (A : Subgroup (MulAut L')) (a₀ : MulAut L') (J₁ : Subgroup L'),
          GGTwE6BigSetting I ψ A a₀ J₁ →
            LargeEvenMarking ↥J₁ fun lab' _ _ _ _ _ => GGTwE6BigLabel lab'

end CFSG.StandardType

end
