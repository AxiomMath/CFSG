module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylCompDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNineSCr
public import CFSG.LocalAnalysis.StandardType.GGTableBF4Basic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB NbrInnerRest

@[expose] def GGTorusNbrSCrComp (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      p ^ r ≤ Nat.card A → p ^ 3 ≤ Nat.card A → GGTorusSelfCent p A →
      (∃ a₀ ∈ A, a₀ ≠ 1 ∧ GGFixCompCyclic p a₀) →
      ∃ W : Set L',
        (∀ n ∈ W, ∀ a ∈ A, (n * (a n)⁻¹) ^ p = 1 ∧ ∀ a' ∈ A, a' (n * (a n)⁻¹) = n * (a n)⁻¹) ∧
        ∀ Y : Subgroup (MulAut L'),
          (∀ n ∈ W, ∀ a ∈ A, MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A) →
          (∀ n ∈ W, ∀ φ ∈ Y, MulAut.conj n * φ * (MulAut.conj n)⁻¹ ∈ Y) →
          (∀ φ ∈ Y, ∀ a ∈ A, φ * a * φ⁻¹ ∈ A) →
          (∀ φ ∈ Y, ∃ k : ℕ, ∀ a ∈ A, φ ^ p ^ k * a = a * φ ^ p ^ k) →
          ∀ φ ∈ Y, ∀ a ∈ A, φ * a = a * φ

theorem ggTorusNbrSCrComp_of_ggTorusNbrSCr {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (h : GGTorusNbrSCr p r R I) : GGTorusNbrSCrComp p r R I :=
  fun L' _ _ ψ hψ hker hperf A hA hAI hr h3 hsc _ => h L' ψ hψ hker hperf A hA hAI hr h3 hsc

@[expose] def GGNbrKGF4ThreeAddSC : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 3 ∣ Nat.card K + 1 →
    GGTorusNbrSCrComp 3 3 (TableBF4.RecipeGroup K) (TableBF4.RecipeID K)

end CFSG.StandardType

end
