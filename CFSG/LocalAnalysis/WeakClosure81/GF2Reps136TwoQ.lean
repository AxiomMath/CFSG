module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136TwoCent
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136SectEnd
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136SectAlt

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W]

@[expose] def GL3Case (Λ X : Subgroup (MulAut W)) (U C : Subgroup W) : Prop :=
  (∀ M : Subgroup W, C ≤ M → M ≤ U → StableUnder Λ M → StableUnder X M → M = C ∨ M = U) ∧
  (∀ M : Subgroup W, C < M → M ≤ U → StableUnder Λ M → ¬ commSub M X ≤ C) ∧
  (∃ x ∈ X, Odd (orderOf x) ∧ ∀ u ∈ U, x u * u⁻¹ ∈ C → u ∈ C) ∧
  Subgroup.centralizer ((secSub U C (Λ ⊔ X) : Subgroup (MulAut (Sect U C))) :
    Set (MulAut (Sect U C))) = ⊥ ∧
  Nat.card (secSub U C X) = 168

theorem perfect_cent_sec (hw2 : ∀ w : W, w ^ 2 = 1) {U C : Subgroup W} (hCU : C ≤ U)
    {Λ X : Subgroup (MulAut W)} (hΛ : StabPair Λ U C) (hX : StabPair X U C) {k : ℕ} (hk : k ≤ 3)
    {J : Fin k → Subgroup W} (hCJ : ∀ i, C ≤ J i) (hJU : ∀ i, J i ≤ U)
    (hirr : ∀ i, IsIrrOn Λ (J i) C)
    (hind : ∀ i, J i ⊓ (C ⊔ ⨆ (j : Fin k) (_ : j ≠ i), J j) ≤ C) (hspan : C ⊔ ⨆ i, J i = U)
    (hend : ∀ i, (∃ j, j ≠ i ∧ SecIsoOn Λ (J i) C (J j) C) →
      Subgroup.centralizer ((secSub (J i) C Λ : Subgroup (MulAut (Sect (J i) C))) :
        Set (MulAut (Sect (J i) C))) = ⊥)
    (hXc : ⁅X, Λ⁆ = ⊥) (hXp : ⁅X, X⁆ = X) :
    (∀ x ∈ X, ∀ u ∈ U, x u * u⁻¹ ∈ C) ∨
      (k = 3 ∧ (∀ i j, SecIsoOn Λ (J i) C (J j) C) ∧
        (∀ i, Nat.card (Sect (J i) C) ^ 3 = Nat.card (Sect U C)) ∧ GL3Case Λ X U C) := by
  have hQ : ∀ x : Sect U C, x ^ 2 = 1 := sect_exp_two hw2 U C
  have hstab : ∀ i, StableUnder (secSub U C Λ) (w1369_im U C (J i)) :=
    fun i => (w1369_irr_transfer hΛ (hCJ i) (hJU i) (hirr i)).2.1
  have hsimple : ∀ i, w1369_im U C (J i) ≠ ⊥ ∧
      ∀ J' : Subgroup (Sect U C), StableUnder (secSub U C Λ) J' →
        J' ≤ w1369_im U C (J i) → J' = ⊥ ∨ J' = w1369_im U C (J i) :=
    fun i => ⟨ne_of_gt (w1369_irr_transfer hΛ (hCJ i) (hJU i) (hirr i)).1,
      fun J' hJ' hJ'sub =>
        (w1369_irr_transfer hΛ (hCJ i) (hJU i) (hirr i)).2.2.2 J' hJ' bot_le hJ'sub⟩
  have hspan' : ⨆ i, w1369_im U C (J i) = ⊤ := by
    have h1 : w1369_im U C (C ⊔ ⨆ i, J i) =
        w1369_im U C C ⊔ w1369_im U C (⨆ i, J i) :=
      w1369_im_sup hCU (iSup_le hJU)
    rw [hspan, w1369_im_top, w1369_im_C, bot_sup_eq] at h1
    exact (w1369_im_iSup hJU).symm.trans h1.symm
  have hXc' : secSub U C X ≤
      Subgroup.centralizer (secSub U C Λ : Set (MulAut (Sect U C))) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
    rw [secSub_commutator hX hΛ, hXc, w1369_secSub_bot]
  have hXp' : ⁅secSub U C X, secSub U C X⁆ = secSub U C X := by
    rw [secSub_commutator hX hX, hXp]
  rcases perfect_cent (Q := Sect U C) (Λ := secSub U C Λ)
      (I := fun i => w1369_im U C (J i)) (X := secSub U C X)
      hQ hk hstab hsimple hspan' (w1369_hind_im hCJ hJU hind)
      (w1369_perfect_cent_hend hw2 hCU hΛ hCJ hJU hirr hend) hXc' hXp' with hbot | hrest
  · left
    exact (w1369_secSub_eq_bot_iff hCU hX).mp hbot
  · right
    exact w1369_second_alt_transfer hw2 hCU hΛ hX hk hCJ hJU hrest

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
