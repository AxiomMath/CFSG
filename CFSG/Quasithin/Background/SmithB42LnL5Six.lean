module

public import CFSG.Quasithin.Background.SmithB42LnL5Rank
public import CFSG.Quasithin.Background.SmithB42LnL5Par

public section

namespace CFSG.Quasithin.B42Ln

open CFSG.Quasithin.JonesParshall CFSG.Quasithin.JonesParshall.Curtis Matrix

@[expose] def q1Codes : List ℕ := (List.range 128).filter (fun c => c % 2 = 0)

@[expose] def q2Codes : List ℕ :=
  [0, 4, 8, 12, 32, 36, 40, 44, 64, 68, 72, 76, 96, 100, 104, 108, 128, 132, 136, 140, 160, 164,
    168, 172, 192, 196, 200, 204, 224, 228, 232, 236, 256, 260, 264, 268, 288, 292, 296, 300, 320,
    324, 328, 332, 352, 356, 360, 364, 384, 388, 392, 396, 416, 420, 424, 428, 448, 452, 456, 460,
    480, 484, 488, 492]

set_option maxRecDepth 100000 in
theorem codes_sub : ∀ x ∈ sqCodes, 64 ≤ commCnt x → x ∈ q1Codes ∨ x ∈ q2Codes := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem not_comm_codes : ∀ x ∈ q2Codes, x ∉ q1Codes → ∀ y ∈ q1Codes, y ∉ q2Codes →
    bmul (upB x) (upB y) ≠ bmul (upB y) (upB x) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem card_q1Codes : q1Codes.toFinset.card = 64 := by decide +kernel

set_option maxRecDepth 100000 in
theorem card_q2Codes : q2Codes.toFinset.card = 64 := by decide +kernel

theorem eT04_mem_Ugrp : eT 0 4 (by decide) ∈ Ugrp := by
  show IsUpU (eTM 0 4)
  intro a b
  fin_cases a <;> fin_cases b <;> decide

theorem eT14_mem_Ugrp : eT 1 4 (by decide) ∈ Ugrp := by
  show IsUpU (eTM 1 4)
  intro a b
  fin_cases a <;> fin_cases b <;> decide

theorem codeOf_eT04 : codeOf (eT 0 4 (by decide)) = 8 := by decide

theorem codeOf_eT14 : codeOf (eT 1 4 (by decide)) = 64 := by decide

theorem card_le_commCnt {E : Subgroup G5} (hEU : E ≤ Ugrp)
    (hc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (h2 : ∀ a ∈ E, a * a = 1) {u : G5} (hu : u ∈ E) :
    Nat.card E ≤ commCnt (codeOf u) := by
  classical
  set S : Finset ℕ := Finset.univ.image fun w : ↥E => codeOf (w : G5) with hS
  have hinj : Function.Injective fun w : ↥E => codeOf (w : G5) := fun w w' h =>
    Subtype.ext (codeOf_injective (hEU w.2) (hEU w'.2) h)
  have hcard : S.card = Nat.card E := by
    rw [hS, Finset.card_image_of_injective _ hinj, Finset.card_univ, Nat.card_eq_fintype_card]
  have hS' : S ⊆ (sqCodes.filter (fun y => bmul (upB (codeOf u)) (upB y) =
      bmul (upB y) (upB (codeOf u)))).toFinset := by
    intro y hy
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 hy
    rw [List.mem_toFinset, List.mem_filter]
    exact ⟨codeOf_mem_sqCodes (hEU w.2) (h2 w w.2),
      decide_eq_true (bmul_comm_of_commute (hEU hu) (hEU w.2) (hc u hu w w.2))⟩
  have h1 := (Finset.card_le_card hS').trans (List.toFinset_card_le _)
  rw [hcard] at h1
  exact h1

theorem mem_of_card_eq_64 {E : Subgroup G5} (hEU : E ≤ Ugrp)
    (hc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (h2 : ∀ a ∈ E, a * a = 1) (h64 : Nat.card E = 64) :
    eT 0 4 (by decide) ∈ E ∧ eT 1 4 (by decide) ∈ E := by
  classical
  set S : Finset ℕ := Finset.univ.image fun w : ↥E => codeOf (w : G5) with hS
  have hinj : Function.Injective fun w : ↥E => codeOf (w : G5) := fun w w' h =>
    Subtype.ext (codeOf_injective (hEU w.2) (hEU w'.2) h)
  have hcard : S.card = 64 := by
    rw [hS, Finset.card_image_of_injective _ hinj, Finset.card_univ, ← Nat.card_eq_fintype_card,
      h64]
  have hq : ∀ u ∈ E, codeOf u ∈ q1Codes ∨ codeOf u ∈ q2Codes := fun u hu =>
    codes_sub _ (codeOf_mem_sqCodes (hEU hu) (h2 u hu))
      (h64 ▸ card_le_commCnt hEU hc h2 hu)
  have hall : (∀ u ∈ E, codeOf u ∈ q1Codes) ∨ (∀ u ∈ E, codeOf u ∈ q2Codes) := by
    by_contra hne
    push Not at hne
    obtain ⟨⟨u₁, hu₁, h₁⟩, ⟨u₂, hu₂, h₂⟩⟩ := hne
    have h₁' := (hq u₁ hu₁).resolve_left h₁
    have h₂' := (hq u₂ hu₂).resolve_right h₂
    exact not_comm_codes _ h₁' h₁ _ h₂' h₂
      (bmul_comm_of_commute (hEU hu₁) (hEU hu₂) (hc u₁ hu₁ u₂ hu₂))
  have hfull : ∀ c ∈ q1Codes, c ∈ q2Codes → c ∈ S := by
    intro c hc1 hc2
    rcases hall with h | h
    · have hsub : S ⊆ q1Codes.toFinset := by
        intro y hy
        obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 hy
        exact List.mem_toFinset.2 (h w w.2)
      have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcard, card_q1Codes])
      rw [heq]
      exact List.mem_toFinset.2 hc1
    · have hsub : S ⊆ q2Codes.toFinset := by
        intro y hy
        obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 hy
        exact List.mem_toFinset.2 (h w w.2)
      have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcard, card_q2Codes])
      rw [heq]
      exact List.mem_toFinset.2 hc2
  have hmem : ∀ (t : G5), t ∈ Ugrp → codeOf t ∈ q1Codes → codeOf t ∈ q2Codes → t ∈ E := by
    intro t ht h1 h2'
    obtain ⟨w, -, hw⟩ := Finset.mem_image.1 (hfull _ h1 h2')
    have : (w : G5) = t := codeOf_injective (hEU w.2) ht hw
    exact this ▸ w.2
  exact ⟨hmem _ eT04_mem_Ugrp (by rw [codeOf_eT04]; decide) (by rw [codeOf_eT04]; decide),
    hmem _ eT14_mem_Ugrp (by rw [codeOf_eT14]; decide) (by rw [codeOf_eT14]; decide)⟩

end CFSG.Quasithin.B42Ln
