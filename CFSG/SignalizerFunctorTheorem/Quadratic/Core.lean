module

public import CFSG.SignalizerFunctorTheorem.Quadratic.Structure
public import CFSG.SignalizerFunctorTheorem.Quadratic.Diagonal

public section

open scoped MatrixGroups

namespace CFSG.SignalizerFunctorTheorem.Quadratic

variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [Finite V]

theorem core {r : ℕ} {H X : Subgroup (LGL p V)} (hH : Hyp H)
    (hS3 : (⨆ (A : Subgroup (LGL p V)) (_ : IsAV H A), A) = H) (hne : H ≠ ⊥) (hr : r.Prime)
    (hXr : IsElemAb r X) (hXH : X ≤ Subgroup.normalizer (H : Set (LGL p V)))
    (hcop : Nat.Coprime r (Nat.card H)) :
    (p = 2 ∨ p = 3) ∧
      (∀ P : Subgroup (LGL p V), IsSyl p P H →
        H ≤ (H ⊓ Subgroup.centralizer (X : Set (LGL p V))) ⊔ P) ∧
      (p = 2 → ∃ W : Submodule (ZMod p) V, W ≤ fixSub X ∧ Nat.card W = p ^ 2 ∧
        ∃ d ∈ H ⊓ Subgroup.centralizer (X : Set (LGL p V)),
          d ^ 3 = 1 ∧ (∀ w ∈ W, d w ∈ W) ∧ ∀ w ∈ W, d w = w → w = 0) ∧
      (p = 3 → ∃ W : Submodule (ZMod p) V, W ≤ fixSub X ∧ Nat.card W = p ^ 2 ∧
        ∃ D : Subgroup (LGL p V), D ≤ H ⊓ Subgroup.centralizer (X : Set (LGL p V)) ∧
          ∃ φ : D →* SL(2, ZMod p), Function.Surjective φ) := by
  obtain ⟨hp23, hsys, hjoin⟩ := structure_theorem hH hS3
  have hp23 := hp23 hne
  have hex : (blocks H).Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    apply hne
    rw [hjoin, hempty]
    simp
  obtain ⟨E, hE⟩ := hex
  have hEblock := hsys.isBlock E hE
  have hEH : E ≤ H := by
    rw [hjoin]
    exact le_iSup₂ (f := fun E (_ : E ∈ blocks H) => E) E hE
  have h6 : 6 ∣ Nat.card H := by
    have hd : Nat.card E ∣ Nat.card H := Subgroup.card_dvd_of_le hEH
    rw [hEblock.card] at hd
    refine dvd_trans ?_ hd
    rcases hp23 with rfl | rfl <;> norm_num
  have hr2 : r ≠ 2 := by
    rintro rfl
    have : 2 ∣ Nat.card H := dvd_trans (by norm_num) h6
    exact (Nat.Prime.coprime_iff_not_dvd hr).mp hcop this
  have hr3 : r ≠ 3 := by
    rintro rfl
    have : 3 ∣ Nat.card H := dvd_trans (by norm_num) h6
    exact (Nat.Prime.coprime_iff_not_dvd hr).mp hcop this
  have hX : ∀ x ∈ X, ∀ E ∈ blocks H, cj x E ∈ blocks H := fun x hx E hE =>
    blocks_cj (hXH hx) hE
  refine ⟨hp23, ?_, ?_, ?_⟩
  · intro P hP
    rw [hjoin] at hP
    have := diag_gen hp23 hsys hr hr2 hr3 hXr hX hP
    rwa [← hjoin] at this
  · intro hp2
    have := diag_two hp2 hsys ⟨E, hE⟩ hr hr2 hr3 hXr hX
    rwa [← hjoin] at this
  · intro hp3
    have := diag_three hp3 hsys ⟨E, hE⟩ hr hr2 hr3 hXr hX
    rwa [← hjoin] at this

end CFSG.SignalizerFunctorTheorem.Quadratic
