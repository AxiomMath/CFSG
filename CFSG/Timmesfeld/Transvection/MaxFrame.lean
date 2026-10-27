module

public import CFSG.Timmesfeld.Transvection.FrameResidue

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS

variable {H : Type*} [Group H] {Δ : Set (Subgroup H)} {r : ℕ} {P Q : Fin r → Subgroup H}

theorem IsMaxFrame.comp_equiv {s : ℕ} (hF : IsMaxFrame Δ P Q) (e : Fin s ≃ Fin r) :
    IsMaxFrame Δ (P ∘ e) (Q ∘ e) where
  toIsFrame := hF.toIsFrame.comp_equiv e
  maximal := by
    intro X hX hc
    exact hF.maximal X hX fun i => by simpa using hc (e.symm i)

theorem frameResidue_comp_perm (σ : Equiv.Perm (Fin r)) (k : Fin r) :
    frameResidue Δ (P ∘ σ) (Q ∘ σ) k = frameResidue Δ P Q (σ k) := by
  ext X
  simp only [frameResidue, Function.comp_apply, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hX, hc⟩
    refine ⟨hX, fun j hj => ?_⟩
    have hjk : σ.symm j ≠ k := fun h => hj (by rw [← h]; exact (Equiv.apply_symm_apply σ j).symm)
    simpa using hc (σ.symm j) hjk
  · rintro ⟨hX, hc⟩
    refine ⟨hX, fun i hi => ?_⟩
    have hik : σ i ≠ σ k := fun h => hi (σ.injective h)
    simpa using hc (σ i) hik

theorem isSmallFrame_comp_perm_iff (hF : IsFrame Δ P Q) (σ : Equiv.Perm (Fin r)) (k : Fin r) :
    IsSmallFrame Δ (P ∘ σ) (Q ∘ σ) k ↔ IsSmallFrame Δ P Q (σ k) := by
  rw [isSmallFrame_iff (hF.comp_equiv σ), isSmallFrame_iff hF, frameResidue_comp_perm]
  rfl

theorem IsMaxFrame.exists_not_small_last (hfr : IsMaxFrame Δ P Q) {k : Fin r}
    (hk : ¬ IsSmallFrame Δ P Q k) :
    IsMaxFrame Δ (P ∘ Equiv.swap k
        ⟨r - 1, Nat.sub_one_lt_of_lt (Nat.zero_lt_of_lt k.isLt)⟩)
      (Q ∘ Equiv.swap k
        ⟨r - 1, Nat.sub_one_lt_of_lt (Nat.zero_lt_of_lt k.isLt)⟩) ∧
      ¬ IsSmallFrame Δ (P ∘ Equiv.swap k
        ⟨r - 1, Nat.sub_one_lt_of_lt (Nat.zero_lt_of_lt k.isLt)⟩)
        (Q ∘ Equiv.swap k
          ⟨r - 1, Nat.sub_one_lt_of_lt (Nat.zero_lt_of_lt k.isLt)⟩)
          ⟨r - 1, Nat.sub_one_lt_of_lt (Nat.zero_lt_of_lt k.isLt)⟩ := by
  have hlast :
      Equiv.swap k ⟨r - 1, by have := k.isLt; omega⟩
        ⟨r - 1, by have := k.isLt; omega⟩ = k := by
    by_cases h : k = ⟨r - 1, by have := k.isLt; omega⟩
    · rw [← h]
      simp
    · exact Equiv.swap_apply_right _ _
  refine ⟨hfr.comp_equiv _, ?_⟩
  rw [isSmallFrame_comp_perm_iff hfr.toIsFrame, hlast]
  exact hk

end CFSG.Timmesfeld.Transvection
