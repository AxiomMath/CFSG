module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80L3Levi

public section

namespace CFSG.Quasithin.E2P.Asc80

open Matrix CFSG.Quasithin.A38c15
open scoped MatrixGroups

variable {p : ℕ} [Fact p.Prime]

@[expose] def lowerUni (p : ℕ) [Fact p.Prime] : SL(3, ZMod p) :=
  ⟨!![1, 0, 0; 1, 1, 0; 0, 0, 1], by norm_num [Matrix.det_fin_three]⟩

@[expose] def upperUni (p : ℕ) [Fact p.Prime] : SL(3, ZMod p) :=
  ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by norm_num [Matrix.det_fin_three]⟩

theorem lowerUni_mem : lowerUni p ∈ leviBlock p :=
  mem_leviBlock_iff.mpr (by simp [lowerUni])

theorem upperUni_mem : upperUni p ∈ leviBlock p :=
  mem_leviBlock_iff.mpr (by simp [upperUni])

theorem levi_fixed_line {v : Fin 3 → ZMod p}
    (h : ∀ g ∈ leviBlock p, ∃ c : ZMod p, (g : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ v = c • v) :
    v 0 = 0 ∧ v 1 = 0 := by
  obtain ⟨c3, h3⟩ := h _ (lowerUni_mem (p := p))
  obtain ⟨c4, h4⟩ := h _ (upperUni_mem (p := p))
  have e30 := congrFun h3 0
  have e31 := congrFun h3 1
  have e40 := congrFun h4 0
  have e41 := congrFun h4 1
  simp [lowerUni, upperUni, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at e30 e31 e40 e41
  have ha : v 0 = 0 := by
    by_contra ha
    have hc : c3 = 1 := by
      have : v 0 * (1 - c3) = 0 := by linear_combination e30
      rcases mul_eq_zero.mp this with h0 | h0
      · exact absurd h0 ha
      · linear_combination -h0
    rw [hc] at e31
    apply ha
    linear_combination e31
  have hb : v 1 = 0 := by
    by_contra hb
    have hc : c4 = 1 := by
      have : v 1 * (1 - c4) = 0 := by linear_combination e41
      rcases mul_eq_zero.mp this with h0 | h0
      · exact absurd h0 hb
      · linear_combination -h0
    rw [hc] at e40
    apply hb
    linear_combination e40
  exact ⟨ha, hb⟩

theorem levi_fixed_row {f : Fin 3 → ZMod p}
    (h : ∀ g ∈ leviBlock p, ∃ c : ZMod p, f ᵥ* (g : Matrix (Fin 3) (Fin 3) (ZMod p)) = c • f) :
    f 0 = 0 ∧ f 1 = 0 := by
  obtain ⟨c3, h3⟩ := h _ (lowerUni_mem (p := p))
  obtain ⟨c4, h4⟩ := h _ (upperUni_mem (p := p))
  have e30 := congrFun h3 0
  have e31 := congrFun h3 1
  have e40 := congrFun h4 0
  have e41 := congrFun h4 1
  simp [lowerUni, upperUni, Matrix.vecMul, dotProduct, Fin.sum_univ_three] at e30 e31 e40 e41
  have hb : f 1 = 0 := by
    by_contra hb
    have hc : c3 = 1 := by
      have : f 1 * (1 - c3) = 0 := by linear_combination e31
      rcases mul_eq_zero.mp this with h0 | h0
      · exact absurd h0 hb
      · linear_combination -h0
    rw [hc] at e30
    apply hb
    linear_combination e30
  have ha : f 0 = 0 := by
    by_contra ha
    have hc : c4 = 1 := by
      have : f 0 * (1 - c4) = 0 := by linear_combination e40
      rcases mul_eq_zero.mp this with h0 | h0
      · exact absurd h0 ha
      · linear_combination -h0
    rw [hc] at e41
    apply ha
    linear_combination e41
  exact ⟨ha, hb⟩

theorem le_linePar_or_le_planePar {Y : Subgroup SL(3, ZMod p)} (hB : leviBlock p ≤ Y)
    (hred : ¬ IsIrreducibleSL3 Y) : Y ≤ linePar p ∨ Y ≤ planePar p := by
  rcases exists_line_or_row Y hred with ⟨v, hv, hY⟩ | ⟨f, hf, hY⟩
  · left
    obtain ⟨h0, h1⟩ := levi_fixed_line fun g hg => hY g (hB hg)
    have hv2 : v 2 ≠ 0 := fun h2 => hv (by
      funext i
      fin_cases i <;> simp [h0, h1, h2])
    intro g hg
    obtain ⟨c, hc⟩ := hY g hg
    have e0 := congrFun hc 0
    have e1 := congrFun hc 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h0, h1] at e0 e1
    refine ⟨?_, ?_⟩
    · exact e0.resolve_right hv2
    · exact e1.resolve_right hv2
  · right
    obtain ⟨h0, h1⟩ := levi_fixed_row fun g hg => hY g (hB hg)
    have hf2 : f 2 ≠ 0 := fun h2 => hf (by
      funext i
      fin_cases i <;> simp [h0, h1, h2])
    intro g hg
    obtain ⟨c, hc⟩ := hY g hg
    have e0 := congrFun hc 0
    have e1 := congrFun hc 1
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three, h0, h1] at e0 e1
    refine ⟨?_, ?_⟩
    · exact e0.resolve_left hf2
    · exact e1.resolve_left hf2

end CFSG.Quasithin.E2P.Asc80
