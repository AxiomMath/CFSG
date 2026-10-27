module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylCompDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGTriD4LineKnown (p : ℕ) (R : Type) [Group R] (I F : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
      (∀ a ∈ A, ∃ φ ∈ Subgroup.closure (I ∪ F), ∀ l : L', φ (ψ l) = ψ (a l)) →
      Nat.card A ≤ p ^ 3 ∧
      (p ^ 3 ≤ Nat.card A → GGTorusSelfCent p A →
        ∀ a₀ ∈ A, a₀ ≠ 1 → (∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a₀ l)) → GGFixCompCyclic p a₀ →
          (∃ n : L', (∀ a ∈ A, (n * (a n)⁻¹) ^ p = 1 ∧
              ∀ a' ∈ A, a' (n * (a n)⁻¹) = n * (a n)⁻¹) ∧
            MulAut.conj n * a₀ * (MulAut.conj n)⁻¹ ∉ Subgroup.zpowers a₀) ∨
          ∃ f ∈ A, f ∉ Subgroup.zpowers a₀ ∧
            ∀ J₁ : Subgroup L', IsComponentOf J₁ (ggFix a₀) → ∀ l ∈ J₁, f l = l)

@[expose] def GGNbrKGFieldTriD4ThreeLine : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → lab.tag = .triD4 → 2 ≤ lab.n →
    3 ∣ 2 ^ lab.n - 1 →
    LargeEvenLabelAll lab fun R _ I F => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      GGTriD4LineKnown 3 R I F

end CFSG.StandardType

end
