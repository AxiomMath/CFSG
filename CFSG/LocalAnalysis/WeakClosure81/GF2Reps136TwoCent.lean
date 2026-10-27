module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136CentDichotomy
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136CentStructure

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

theorem perfect_cent {Q : Type} [CommGroup Q] [Finite Q] (hQ : ∀ x : Q, x ^ 2 = 1)
    {Λ : Subgroup (MulAut Q)} {k : ℕ} (hk : k ≤ 3) {I : Fin k → Subgroup Q}
    (hstab : ∀ i, StableUnder Λ (I i))
    (hsimple : ∀ i, I i ≠ ⊥ ∧ ∀ J : Subgroup Q, StableUnder Λ J → J ≤ I i → J = ⊥ ∨ J = I i)
    (hspan : ⨆ i, I i = ⊤) (hind : ∀ i, I i ⊓ (⨆ (j : Fin k) (_ : j ≠ i), I j) = ⊥)
    (hend : ∀ i j, i ≠ j → SecIsoOn Λ (I i) ⊥ (I j) ⊥ → ∀ f : Q →* Q,
      (∀ g ∈ Λ, ∀ x, f (g x) = g (f x)) → (∀ x ∈ I i, f x ∈ I i) →
      (∀ j', j' ≠ i → ∀ x ∈ I j', f x = 1) → (∀ x ∈ I i, f x = x) ∨ (∀ x ∈ I i, f x = 1))
    {X : Subgroup (MulAut Q)} (hXc : X ≤ Subgroup.centralizer (Λ : Set (MulAut Q)))
    (hXp : ⁅X, X⁆ = X) :
    X = ⊥ ∨ (k = 3 ∧ (∀ i j, SecIsoOn Λ (I i) ⊥ (I j) ⊥) ∧ Nat.card X = 168 ∧
      (∀ i, Nat.card (I i) ^ 3 = Nat.card Q) ∧
      (∃ x ∈ X, orderOf x = 7 ∧ ∀ q : Q, x q = q → q = 1) ∧
      (∀ N : Subgroup Q, StableUnder Λ N → StableUnder X N → N = ⊥ ∨ N = ⊤) ∧
      Subgroup.centralizer ((Λ ⊔ X : Subgroup (MulAut Q)) : Set (MulAut Q)) = ⊥ ∧
      ∀ N : Subgroup Q, StableUnder Λ N → N ≠ ⊥ → ∃ x ∈ X, ∃ n ∈ N, x n ≠ n) := by
  rcases cent_dichotomy hQ hk hstab hsimple hspan hind hend hXc hXp with hX | hrest
  · exact Or.inl hX
  · obtain ⟨hk3, hiso, hcardX, hcardI⟩ := hrest
    obtain ⟨hord, hirr, hcent, hmove⟩ :=
      cent_structure hQ hk3 hstab hsimple hspan hind hend hXc hXp hiso hcardX
    exact Or.inr ⟨hk3, hiso, hcardX, hcardI, hord, hirr, hcent, hmove⟩

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
