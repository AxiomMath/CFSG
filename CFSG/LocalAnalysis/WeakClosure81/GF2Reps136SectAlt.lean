module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136SectIso
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136SectLattice

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W]

theorem w1369_second_alt_transfer (hw2 : ∀ w : W, w ^ 2 = 1) {U C : Subgroup W}
    (hCU : C ≤ U) {Λ X : Subgroup (MulAut W)} (hΛ : StabPair Λ U C) (hX : StabPair X U C)
    {k : ℕ} (hk : k ≤ 3) {J : Fin k → Subgroup W} (hCJ : ∀ i, C ≤ J i)
    (hJU : ∀ i, J i ≤ U)
    (h : k = 3 ∧
      (∀ i j, SecIsoOn (secSub U C Λ) (w1369_im U C (J i)) ⊥
        (w1369_im U C (J j)) ⊥) ∧
      Nat.card (secSub U C X) = 168 ∧
      (∀ i, Nat.card (w1369_im U C (J i)) ^ 3 = Nat.card (Sect U C)) ∧
      (∃ x ∈ secSub U C X, orderOf x = 7 ∧ ∀ q : Sect U C, x q = q → q = 1) ∧
      (∀ N : Subgroup (Sect U C), StableUnder (secSub U C Λ) N →
        StableUnder (secSub U C X) N → N = ⊥ ∨ N = ⊤) ∧
      Subgroup.centralizer (((secSub U C Λ) ⊔ (secSub U C X) :
        Subgroup (MulAut (Sect U C))) : Set (MulAut (Sect U C))) = ⊥ ∧
      ∀ N : Subgroup (Sect U C), StableUnder (secSub U C Λ) N → N ≠ ⊥ →
        ∃ x ∈ secSub U C X, ∃ n ∈ N, x n ≠ n) :
    k = 3 ∧ (∀ i j, SecIsoOn Λ (J i) C (J j) C) ∧
      (∀ i, Nat.card (Sect (J i) C) ^ 3 = Nat.card (Sect U C)) ∧
      (∀ M : Subgroup W, C ≤ M → M ≤ U → StableUnder Λ M → StableUnder X M →
        M = C ∨ M = U) ∧
      (∀ M : Subgroup W, C < M → M ≤ U → StableUnder Λ M → ¬ commSub M X ≤ C) ∧
      (∃ x ∈ X, Odd (orderOf x) ∧ ∀ u ∈ U, x u * u⁻¹ ∈ C → u ∈ C) ∧
      Subgroup.centralizer ((secSub U C (Λ ⊔ X) : Subgroup (MulAut (Sect U C))) :
        Set (MulAut (Sect U C))) = ⊥ ∧
      Nat.card (secSub U C X) = 168 := by
  obtain ⟨hk3, hiso, hcard, hord, hx7, hirr, hcent, hnc⟩ := h
  refine ⟨hk3, fun i j => (w1369_secIsoOn_im_iff hw2 hΛ (hCJ i) (hJU i) (hCJ j) (hJU j)).mp
    (hiso i j), fun i => ?_, w1369_alt_irr hCU hΛ hX hirr, w1369_alt_notcent hCU hΛ hX hnc,
    w1369_alt_odd hX hx7, ?_, hcard⟩
  · rw [← w1369_im_card (hCJ i) (hJU i)]
    exact hord i
  · rw [secSub_sup hΛ hX]
    exact hcent

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
