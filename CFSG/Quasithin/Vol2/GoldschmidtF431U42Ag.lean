module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Cover

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin CFSG.Open U42F431
open scoped Pointwise

theorem agOK_spec {p k : ℕ} (hp : p < 45) (hp0 : p ≠ 0) (hk : k < 27)
    (hk0 : k ≠ 0) : agOK p k = true := by
  have h := Certificates.certificate4161.2.2.2.2.2.2.1
  simp only [chkAg, List.all_eq_true, Bool.or_eq_true, beq_iff_eq, List.mem_range] at h
  rcases h p hp with h0 | h1
  · exact absurd h0 hp0
  · rcases h1 k hk with h0 | h2
    · exact absurd h0 hk0
    · exact h2

theorem agOK_cases {p k : ℕ} (h : agOK p k = true) :
    (∃ i < 64, i ∉ agH p k ∧ ∀ j ∈ agH p k, (commTab.getD i []).getD j false = true) ∨
    (∀ j ∈ agH p k, zclT.getD j false = false ∨ Tl.getD j [] = xL) := by
  unfold agOK at h
  rcases Bool.or_eq_true_iff.1 h with h1 | h2
  · left
    obtain ⟨i, hi, hi'⟩ := List.any_eq_true.1 h1
    rw [Bool.and_eq_true] at hi'
    refine ⟨i, List.mem_range.1 hi, ?_, fun j hj => List.all_eq_true.1 hi'.2 j hj⟩
    intro hm
    have := List.contains_iff_mem.2 hm
    have h3 := hi'.1
    rw [this] at h3
    exact absurd h3 (by decide)
  · right
    intro j hj
    have := List.all_eq_true.1 h2 j hj
    rcases Bool.or_eq_true_iff.1 this with h3 | h3
    · left
      simpa using h3
    · right
      simpa using h3

theorem commTab_eq {i j : ℕ} (hi : i < 64) (hj : j < 64)
    (h : (commTab.getD i []).getD j false = true) :
    comp (Tl.getD i []) (Tl.getD j []) = comp (Tl.getD j []) (Tl.getD i []) := by
  simp only [commTab, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range, hi, hj,
    Option.map_some, Option.getD_some, beq_iff_eq] at h
  simpa using h

theorem zclT_true {j : ℕ} (hj : j < 64) (h : tpTab.contains (Tl.getD j []) = true) :
    zclT.getD j false = true := by
  simp only [zclT, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range, hj,
    Option.map_some, Option.getD_some]
  exact h

theorem conj_mem_of_normalizer {D : Subgroup Y} {n : Y} (hn : n ∈ Subgroup.normalizer (D : Set Y))
    {d : Y} (hd : d ∈ D) : n⁻¹ * d * n ∈ D := by
  have h := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hn) d).1 hd
  simpa using h

theorem D_fix_zero {D : Subgroup Y} (hDT : D ≤ T) {d : Y}
    (hd : d ∈ D) : (d : P45) 0 = 0 := (mem_P1_iff _).1 (B0_le_P1 (T_le_B0 (hDT hd)))

theorem D_fix_L0 {D : Subgroup Y} (hDT : D ≤ T) {d : Y}
    (hd : d ∈ D) : (d : P45) '' L0S = L0S := (mem_P2_iff _).1 (B0_le_P2 (T_le_B0 (hDT hd)))

theorem normalizer_le_P1_of_unique_point {D : Subgroup Y}
    (hDT : D ≤ T) (hP : ∀ p : Fin 45, p ≠ 0 → ∃ d ∈ D, (d : P45) p ≠ p) :
    Subgroup.normalizer (D : Set Y) ≤ P1 := by
  intro n hn
  rw [mem_P1_iff]
  by_contra h0
  obtain ⟨d, hd, hne⟩ := hP ((n : P45) 0) h0
  have h1 := D_fix_zero hDT (conj_mem_of_normalizer hn hd)
  apply hne
  have h2 : ((n : P45)⁻¹ * (d : P45) * (n : P45)) 0 = 0 := h1
  simp only [Equiv.Perm.mul_apply] at h2
  have h3 : (d : P45) ((n : P45) 0) = (n : P45) 0 := by
    have := congrArg (fun q => (n : P45) q) h2
    simpa using this
  exact h3

theorem normalizer_le_P2_of_unique_line {D : Subgroup Y}
    (hDT : D ≤ T)
    (hL : ∀ k < 27, k ≠ 0 → ∃ d ∈ D, (d : P45) '' lnS k ≠ lnS k) :
    Subgroup.normalizer (D : Set Y) ≤ P2 := by
  intro n hn
  obtain ⟨k, hk, hnk⟩ := line_stable n.2 (k := 0) (by norm_num)
  rw [lnS_zero] at hnk
  by_cases hk0 : k = 0
  · subst hk0
    rw [lnS_zero] at hnk
    exact (mem_P2_iff _).2 hnk
  · exfalso
    obtain ⟨d, hd, hne⟩ := hL k hk hk0
    apply hne
    have h1 := D_fix_L0 hDT (conj_mem_of_normalizer hn hd)
    rw [← hnk]
    have h2 : (d : P45) '' ((n : P45) '' L0S) = (n : P45) '' L0S := by
      rw [Set.image_image]
      have : ((d : P45) * (n : P45)) = (n : P45) * ((n⁻¹ * d * n : Y) : P45) := by
        simp [mul_assoc]
      show ((fun x => (d : P45) ((n : P45) x))) '' L0S = _
      have e2 : (fun x => (d : P45) ((n : P45) x)) =
          (fun x => (n : P45) (((n⁻¹ * d * n : Y) : P45) x)) := by
        funext x
        simp
      rw [e2, ← Set.image_image (fun x => (n : P45) x) (fun x => ((n⁻¹ * d * n : Y) : P45) x)]
      show (n : P45) '' (((n⁻¹ * d * n : Y) : P45) '' L0S) = _
      rw [h1]
    exact h2

end CFSG.Quasithin.H13.F431.U42
