module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89KCoverPG

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KInputs

private theorem k91c3_hom {ws : List (List (Fin 3 × Bool))} (f : Fin 3 → Multiplicative (ZMod 6))
    (h : ∀ w ∈ ws, (w.map fun x => cond x.2 (f x.1) (f x.1)⁻¹).prod = 1) (i : Fin 3)
    (hi : f i ≠ 1) :
    ∃ χ : CFSG.CosetTable.PG 3 ws →* Multiplicative (ZMod 6), χ ≠ 1 := by
  refine ⟨PresentedGroup.toGroup (f := f) ?_, fun hχ => hi ?_⟩
  · intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    rw [FreeGroup.lift_mk]
    exact h w hw
  · have := DFunLike.congr_fun hχ (PresentedGroup.of i)
    rwa [PresentedGroup.toGroup.of, MonoidHom.one_apply] at this

theorem coverPG3_cases_of_bounds (h : ∀ k l, k < 2 → l < 3 → Finite (CoverPG 3 0 0 k l) ∧
      Nat.card (CoverPG 3 0 0 k l) ≤ if l = 0 then 1080 else 360) (k l : ℕ) (hk : k < 2)
    (hl : l < 3) :
    Finite (CoverPG 3 0 0 k l) ∧ (Nat.card (CoverPG 3 0 0 k l) < 1080 ∨
      (Nat.card (CoverPG 3 0 0 k l) ≤ 1080 ∧ ((k = 1 ∧ l = 0) ∨
        ∃ χ : CoverPG 3 0 0 k l →* Multiplicative (ZMod 6), χ ≠ 1))) := by
  obtain ⟨hf, hc⟩ := h k l hk hl
  refine ⟨hf, ?_⟩
  rcases Nat.eq_zero_or_pos l with rfl | hl0
  · rw [if_pos rfl] at hc
    interval_cases k
    · exact Or.inr ⟨hc, Or.inr (k91c3_hom ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 0,
        Multiplicative.ofAdd 2] (by decide) 2 (by decide))⟩
    · exact Or.inr ⟨hc, Or.inl ⟨rfl, rfl⟩⟩
  · rw [if_neg hl0.ne'] at hc
    exact Or.inl (by omega)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KInputs
