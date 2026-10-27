module

public import CFSG.LocalAnalysis.WeakClosure81.EightEightDefs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTwentyTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G]

@[expose] noncomputable def fIndex (H : Subgroup G) : ℕ∞ :=
  ⨅ i ∈ {i : ℕ | WeakClosure81.InFSq i H}, (i : ℕ∞)

@[expose] noncomputable def fIndexSum (Γ : Set (Subgroup G)) : ℕ∞ :=
  ∑ᶠ H ∈ Γ, fIndex H

@[expose] noncomputable def fIndexMax (Δ : Set (Subgroup G)) : ℕ∞ :=
  ⨆ H ∈ Δ, fIndex H

theorem fIndex_le_iff [Finite G] {H : Subgroup G} {i : ℕ} :
    fIndex H ≤ (i : ℕ∞) ↔ WeakClosure81.InFSq i H := by
  constructor
  · intro hle
    by_contra hi
    have hge : ((i + 1 : ℕ) : ℕ∞) ≤ fIndex H := by
      unfold fIndex
      refine le_iInf₂ fun j hj => ?_
      have hlt : i < j := by
        by_contra h
        exact hi (TwelveTwentyTwo.inFSq_mono (Nat.le_of_not_gt h) hj)
      exact WithTop.coe_le_coe.mpr (Nat.succ_le_of_lt hlt)
    have hcontr : ((i + 1 : ℕ) : ℕ∞) ≤ (i : ℕ∞) := hge.trans hle
    exact Nat.not_succ_le_self i (WithTop.coe_le_coe.mp hcontr)
  · intro hi
    unfold fIndex
    exact iInf₂_le (f := fun j (_ : WeakClosure81.InFSq j H) => (j : ℕ∞)) i hi

theorem fIndexMax_le_iff [Finite G] {Δ : Set (Subgroup G)} {i : ℕ} :
    fIndexMax Δ ≤ (i : ℕ∞) ↔ ∀ H ∈ Δ, WeakClosure81.InFSq i H := by
  constructor
  · intro hle H hH
    exact fIndex_le_iff.mp ((le_iSup₂ (f := fun H (_ : H ∈ Δ) => fIndex H) H hH).trans hle)
  · intro h
    unfold fIndexMax
    exact iSup₂_le fun H hH => fIndex_le_iff.mpr (h H hH)

theorem inFSq_toNat_fIndex [Finite G] {H : Subgroup G} (h : fIndex H ≠ ⊤) :
    WeakClosure81.InFSq (fIndex H).toNat H :=
  fIndex_le_iff.mp (le_of_eq (ENat.coe_toNat h).symm)

theorem le_fIndexMax {Δ : Set (Subgroup G)} {H : Subgroup G} (hH : H ∈ Δ) :
    fIndex H ≤ fIndexMax Δ := by
  unfold fIndexMax
  exact le_iSup₂_of_le H hH le_rfl

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
