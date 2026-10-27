module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35F2aBase

public section

namespace CFSG.Quasithin.F53.Stellmacher.S35.F2a

open Equiv CFSG.Quasithin CFSG.Quasithin.F53Mod CFSG.Quasithin.F53.Stellmacher.S35.Fin

theorem move_cover : ∀ k : Perm (Fin 5), k 4 ≠ 4 → ∃ s ∈ S5SylF, ∃ t ∈ S5SylF,
    k = s * r4 * t ∨ k = s * r8 * t := by
  unfold r4 r8
  decide +kernel

theorem S5Syl_sup_r4 (P : Subgroup (Perm (Fin 5))) (hS : S5Syl ≤ P) (hr : r4 ∈ P) : P = ⊤ := by
  have hg : S5g ∈ P := hS ((mem_S5Syl_iff _).mpr (by unfold S5SylF; decide +kernel))
  have h2 : swap 0 2 ∈ P := hS ((mem_S5Syl_iff _).mpr (by unfold S5SylF; decide +kernel))
  have hT : ∀ t ∈ [S5g, swap 0 2, r4], t ∈ P := by
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;> assumption
  refine eq_top_of_words P hT [0, 0, 0, 2, 0, 1, 2, 0, 2] [0, 1, 2, 0, 1, 2, 0, 1, 2]
    [1, 2, 0, 1, 2, 0, 2] [2] ?_ ?_ ?_ ?_ <;> unfold evalW <;> unfold S5g r4 <;> decide +kernel

theorem S5Syl_sup_r8 (P : Subgroup (Perm (Fin 5))) (hS : S5Syl ≤ P) (hr : r8 ∈ P) : P = ⊤ := by
  have hg : S5g ∈ P := hS ((mem_S5Syl_iff _).mpr (by unfold S5SylF; decide +kernel))
  have h2 : swap 0 2 ∈ P := hS ((mem_S5Syl_iff _).mpr (by unfold S5SylF; decide +kernel))
  have hT : ∀ t ∈ [S5g, swap 0 2, r8], t ∈ P := by
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;> assumption
  refine eq_top_of_words P hT [0, 2, 0, 2, 1] [1, 0, 2, 0, 2] [0, 2, 0, 2, 0] [0, 2, 0, 2, 0, 2]
    ?_ ?_ ?_ ?_ <;> unfold evalW <;> unfold S5g r8 <;> decide +kernel

theorem eq_top_of_S5Syl_le_of_move {P : Subgroup (Perm (Fin 5))} (hS : S5Syl ≤ P) {x : Perm (Fin 5)}
    (hx : x ∈ P) (h4 : x 4 ≠ 4) : P = ⊤ := by
  obtain ⟨s, hs, t, ht, h⟩ := move_cover x h4
  have hs' : s ∈ P := hS ((mem_S5Syl_iff s).mpr hs)
  have ht' : t ∈ P := hS ((mem_S5Syl_iff t).mpr ht)
  rcases h with rfl | rfl
  · have : r4 = s⁻¹ * (s * r4 * t) * t⁻¹ := by group
    exact S5Syl_sup_r4 P hS (this ▸ P.mul_mem (P.mul_mem (P.inv_mem hs') hx) (P.inv_mem ht'))
  · have : r8 = s⁻¹ * (s * r8 * t) * t⁻¹ := by group
    exact S5Syl_sup_r8 P hS (this ▸ P.mul_mem (P.mul_mem (P.inv_mem hs') hx) (P.inv_mem ht'))

theorem overgroup_std {P : Subgroup (Perm (Fin 5))} (hS : S5Syl ≤ P) :
    P = S5Syl ∨ P = ptStab 4 ∨ P = ⊤ := by
  by_cases hmove : ∃ x ∈ P, x 4 ≠ 4
  · obtain ⟨x, hx, h4⟩ := hmove
    exact Or.inr (Or.inr (eq_top_of_S5Syl_le_of_move hS hx h4))
  · push Not at hmove
    have hle : P ≤ ptStab 4 := fun x hx => mem_ptStab.mpr (hmove x hx)
    have h1 : 8 ∣ Nat.card P := card_S5Syl ▸ Subgroup.card_dvd_of_le hS
    have h2 : Nat.card P ∣ 24 := card_ptStab 4 ▸ Subgroup.card_dvd_of_le hle
    have h3 : Nat.card P = 8 ∨ Nat.card P = 24 := by
      obtain ⟨k, hk⟩ := h1
      have : k ∣ 3 := by
        rw [hk] at h2
        exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 8) (by simpa [mul_comm] using h2)
      rcases (Nat.dvd_prime Nat.prime_three).mp this with rfl | rfl <;> simp [hk]
    rcases h3 with h3 | h3
    · exact Or.inl (Subgroup.eq_of_le_of_card_ge hS (by rw [h3, card_S5Syl])).symm
    · exact Or.inr (Or.inl (Subgroup.eq_of_le_of_card_ge hle (by rw [h3, card_ptStab])))

theorem overgroup_sylow {D P : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8) (hDP : D ≤ P) :
    P = D ∨ P = ptStab (fixPt D) ∨ P = ⊤ := by
  obtain ⟨g, rfl⟩ := exists_cj hD
  have hfix : fixPt (cj g S5Syl) = g 4 := by rw [fixPt_cj card_S5Syl, fixPt_std]
  have h : S5Syl ≤ cj g⁻¹ P := by
    have := (cj_le_cj_iff g⁻¹).mpr hDP
    rwa [cj_inv_cj] at this
  have hP : P = cj g (cj g⁻¹ P) := by rw [← cj_mul]; simp [cj_one]
  rcases overgroup_std h with h1 | h1 | h1
  · left; rw [hP, h1]
  · right; left; rw [hP, h1, cj_ptStab, hfix]
  · right; right; rw [hP, h1, cj_top]

theorem isFixPt_of_le_ptStab {E : Subgroup (Perm (Fin 5))} {p : Fin 5} (h : E ≤ ptStab p) :
    IsFixPt E p := fun _ he => mem_ptStab.mp (h he)

theorem sup_eq_top_of_fixPt_ne {D E : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8)
    (hE : Nat.card E = 8) (h : fixPt D ≠ fixPt E) : D ⊔ E = ⊤ := by
  rcases overgroup_sylow hD (le_sup_left : D ≤ D ⊔ E) with h1 | h1 | h1
  · exfalso
    have : E ≤ D := h1 ▸ le_sup_right
    exact h (fixPt_eq hE (fun e he => isFixPt_fixPt hD e (this he))).symm
  · exfalso
    have : E ≤ ptStab (fixPt D) := h1 ▸ le_sup_right
    exact h (fixPt_eq hE (isFixPt_of_le_ptStab this)).symm
  · exact h1

theorem sup_eq_ptStab_of_fixPt_eq {D E : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8)
    (hE : Nat.card E = 8) (hne : D ≠ E) (h : fixPt D = fixPt E) :
    D ⊔ E = ptStab (fixPt D) := by
  have hle : D ⊔ E ≤ ptStab (fixPt D) :=
    sup_le (le_ptStab_fixPt hD) (h ▸ le_ptStab_fixPt hE)
  rcases overgroup_sylow hD (le_sup_left : D ≤ D ⊔ E) with h1 | h1 | h1
  · exfalso
    have : E ≤ D := h1 ▸ le_sup_right
    exact hne (Subgroup.eq_of_le_of_card_ge this (by rw [hD, hE])).symm
  · exact h1
  · rw [h1] at hle
    exfalso
    have : (⊤ : Subgroup (Perm (Fin 5))) ≤ ptStab (fixPt D) := hle
    have h24 := card_ptStab (fixPt D)
    have : Nat.card (ptStab (fixPt D)) = Nat.card (Perm (Fin 5)) :=
      Subgroup.card_eq_iff_eq_top _ |>.mpr (top_le_iff.mp this)
    rw [h24, Nat.card_eq_fintype_card, Fintype.card_perm] at this
    simp [Nat.factorial] at this

end CFSG.Quasithin.F53.Stellmacher.S35.F2a
