module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89KCoverPG

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KInputs

private theorem k91c6_hom {ws : List (List (Fin 3 × Bool))} (f : Fin 3 → Multiplicative (ZMod 6))
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

theorem coverPG6_cases_of_bounds (h : ∀ i j k l, i < 2 → j < 2 → k < 2 → l < 3 →
      Finite (CoverPG 6 i j k l) ∧
        Nat.card (CoverPG 6 i j k l) ≤ (if i = j then 2160 else 1080) / (if l = 0 then 1 else 3))
    (i j k l : ℕ) (hi : i < 2) (hj : j < 2) (hk : k < 2) (hl : l < 3) :
    Finite (CoverPG 6 i j k l) ∧ (Nat.card (CoverPG 6 i j k l) < 2160 ∨
      (Nat.card (CoverPG 6 i j k l) ≤ 2160 ∧ ((i = 1 ∧ j = 1 ∧ k = 1 ∧ l = 0) ∨
        ∃ χ : CoverPG 6 i j k l →* Multiplicative (ZMod 6), χ ≠ 1))) := by
  obtain ⟨hf, hN⟩ := h i j k l hi hj hk hl
  refine ⟨hf, ?_⟩
  by_cases hbig : i = j ∧ l = 0
  · obtain ⟨rfl, rfl⟩ := hbig
    rw [if_pos rfl, if_pos rfl, Nat.div_one] at hN
    interval_cases i <;> interval_cases k
    · exact Or.inr ⟨hN, Or.inr (k91c6_hom ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 0,
        Multiplicative.ofAdd 1] (by decide) 2 (by decide))⟩
    · exact Or.inr ⟨hN, Or.inr (k91c6_hom ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 3,
        Multiplicative.ofAdd 3] (by decide) 2 (by decide))⟩
    · exact Or.inr ⟨hN, Or.inr (k91c6_hom ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 0,
        Multiplicative.ofAdd 2] (by decide) 2 (by decide))⟩
    · exact Or.inr ⟨hN, Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩
  · have hlt : (if i = j then 2160 else 1080) / (if l = 0 then 1 else 3) < 2160 := by
      by_cases h1 : i = j
      · rw [if_pos h1, if_neg fun h2 => hbig ⟨h1, h2⟩]
        norm_num
      · rw [if_neg h1]
        split_ifs <;> norm_num
    exact Or.inl (lt_of_le_of_lt hN hlt)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KInputs
