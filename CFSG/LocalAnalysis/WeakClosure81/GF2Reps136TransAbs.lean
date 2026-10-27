module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12d
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136SimpleNoniso
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136SimpleIso

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W]

theorem trans_abs {Q : Type} [CommGroup Q] [Finite Q] (hQ : ∀ x : Q, x ^ 2 = 1)
    {Λ N : Subgroup (MulAut Q)} (hΛN : Λ ≤ N) (hnorm : ∀ n ∈ N, ∀ l ∈ Λ, n * l * n⁻¹ ∈ Λ)
    {k : ℕ} (hk : k ≤ 3) {I : Fin k → Subgroup Q} (hstab : ∀ i, StableUnder Λ (I i))
    (hsimple : ∀ i, I i ≠ ⊥ ∧ ∀ J : Subgroup Q, StableUnder Λ J → J ≤ I i → J = ⊥ ∨ J = I i)
    (hspan : ⨆ i, I i = ⊤) (hind : ∀ i, I i ⊓ (⨆ (j : Fin k) (_ : j ≠ i), I j) = ⊥)
    (hend : ∀ i j, i ≠ j → SecIsoOn Λ (I i) ⊥ (I j) ⊥ → ∀ f : Q →* Q,
      (∀ g ∈ Λ, ∀ x, f (g x) = g (f x)) → (∀ x ∈ I i, f x ∈ I i) →
      (∀ j', j' ≠ i → ∀ x ∈ I j', f x = 1) → (∀ x ∈ I i, f x = x) ∨ (∀ x ∈ I i, f x = 1))
    (hirr : ∀ M : Subgroup Q, StableUnder N M → M = ⊥ ∨ M = ⊤) :
    ∀ S₁ S₂ : Subgroup Q,
      (S₁ ≠ ⊥ ∧ StableUnder Λ S₁ ∧ ∀ J : Subgroup Q, StableUnder Λ J → J ≤ S₁ → J = ⊥ ∨ J = S₁) →
      (S₂ ≠ ⊥ ∧ StableUnder Λ S₂ ∧ ∀ J : Subgroup Q, StableUnder Λ J → J ≤ S₂ → J = ⊥ ∨ J = S₂) →
      ∃ n ∈ N, S₂ = S₁.map n.toMonoidHom := by
  classical
  by_cases hiso : ∃ i j, i ≠ j ∧ SecIsoOn Λ (I i) ⊥ (I j) ⊥
  · exact w1369_ta_iso_case hQ hΛN hnorm hk hstab hsimple hspan hind hend hiso hirr
  · have hnoniso : ∀ i j, i ≠ j → ¬ SecIsoOn Λ (I i) ⊥ (I j) ⊥ := by
      intro i j hij hs
      exact hiso ⟨i, j, hij, hs⟩
    let P := w1369_ta_mkProj hstab hspan hind
    exact w1369_ta_noniso hnorm P hstab
      (fun i => ⟨(hsimple i).1, hstab i, (hsimple i).2⟩) hind hnoniso hirr

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
