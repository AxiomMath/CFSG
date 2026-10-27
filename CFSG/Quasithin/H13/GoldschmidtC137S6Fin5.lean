module

public import CFSG.Quasithin.H13.GoldschmidtC137S6Fin3

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Quasithin CFSG.Quasithin.B3

@[expose] def Z0l : List Tab := [[0, 1, 2, 3, 4, 5], [1, 0, 2, 3, 4, 5]]

@[expose] def Z2l : List Tab := [[0, 1, 2, 3, 4, 5], [0, 1, 3, 2, 4, 5]]

theorem subOK_Z0 : subOK 6 Z0l = true := by decide +kernel

theorem subOK_Z2 : subOK 6 Z2l = true := by decide +kernel

noncomputable abbrev Z0 : Subgroup (Gp 6) := subOf 6 Z0l

noncomputable abbrev Z2 : Subgroup (Gp 6) := subOf 6 Z2l

set_option maxRecDepth 100000 in
theorem T6_two_list : ∀ a ∈ T6l, ∀ b ∈ T6l, subOK 6 [a, b] = true → 32 ≤ Fval 6 Mod.ut0 [a, b] →
    (∀ t ∈ [a, b], t ∈ Z0l) ∨ (∀ t ∈ [a, b], t ∈ Z2l) ∨ (∀ t ∈ [a, b], t ∈ Z1l) := by
  decide +kernel

theorem card_Z0 : Nat.card Z0 = 2 := by
  rw [card_subOf subOK_Z0]
  rfl

theorem card_Z2 : Nat.card Z2 = 2 := by
  rw [card_subOf subOK_Z2]
  rfl

theorem card_Z1 : Nat.card Z1 = 2 := by
  rw [card_subOf subOK_Z1]
  rfl

theorem tab_swap01 : tab (Equiv.swap (0 : Fin 6) 1) = [1, 0, 2, 3, 4, 5] := by decide +kernel

theorem tab_swap23 : tab (Equiv.swap (2 : Fin 6) 3) = [0, 1, 3, 2, 4, 5] := by decide +kernel

theorem swap01_mem_Z0 : Equiv.swap (0 : Fin 6) 1 ∈ Z0 := by
  rw [mem_subOf subOK_Z0, tab_swap01]
  decide +kernel

theorem swap23_mem_Z2 : Equiv.swap (2 : Fin 6) 3 ∈ Z2 := by
  rw [mem_subOf subOK_Z2, tab_swap23]
  decide +kernel

theorem T6_offender_two {K : Subgroup (Gp 6)} (hK : K ≤ T6) (hK2 : Nat.card K = 2)
    (hF : 16 ≤ Nat.card (K.map (Mod.act 6 Mod.ut0)) *
      Nat.card (fixV (K.map (Mod.act 6 Mod.ut0)))) : K = Z0 ∨ K = Z2 ∨ K = Z1 := by
  obtain ⟨X, hXL, hX, hKX⟩ := exists_sublist_of_le (subOK_spec subOK_lists.1).2.2.2.2 (K := K)
    (fun x hx => (mem_T6).1 (hK hx))
  have hKe : K = subOf 6 X := subOf_eq hX hKX
  have hlen : X.length = 2 := by
    rw [← card_subOf hX, ← hKe, hK2]
  obtain ⟨a, b, hab⟩ := List.length_eq_two.1 hlen
  subst hab
  have ha : a ∈ T6l := hXL.subset (by simp)
  have hb : b ∈ T6l := hXL.subset (by simp)
  have hFv : 32 ≤ Fval 6 Mod.ut0 [a, b] := by
    have h2 := card_mul_fix_eq hX
    rw [← hKe] at h2
    omega
  have hmem : ∀ x : Gp 6, x ∈ K → tab x ∈ [a, b] := fun x hx => (hKX x).1 hx
  rcases T6_two_list a ha b hb hX hFv with h | h | h
  · left
    refine Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) (by rw [card_Z0, hK2])
    exact (mem_subOf subOK_Z0).2 (h _ (hmem x hx))
  · right
    left
    refine Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) (by rw [card_Z2, hK2])
    exact (mem_subOf subOK_Z2).2 (h _ (hmem x hx))
  · right
    right
    refine Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) (by rw [card_Z1, hK2])
    exact (mem_subOf subOK_Z1).2 (h _ (hmem x hx))

theorem Z0_le_R2 : Z0 ≤ R2 := fun σ hσ => by
  rw [mem_subOf subOK_Z0] at hσ
  rw [mem_R2]
  revert hσ
  generalize tab σ = t
  decide +revert +kernel

theorem Z2_le_R2 : Z2 ≤ R2 := fun σ hσ => by
  rw [mem_subOf subOK_Z2] at hσ
  rw [mem_R2]
  revert hσ
  generalize tab σ = t
  decide +revert +kernel

theorem Z1_le_R2 : Z1 ≤ R2 := fun σ hσ => by
  rw [mem_Z1] at hσ
  rw [mem_R2]
  revert hσ
  generalize tab σ = t
  decide +revert +kernel

@[expose] def R2words : List (List ℕ) := [[], [2], [1], [1, 2], [0], [0, 2], [0, 1], [0, 1, 2]]

theorem R2_le_sup : R2 ≤ Z0 ⊔ Z2 ⊔ Z1 := by
  have hG : ∀ g ∈ [tab (Equiv.swap (0 : Fin 6) 1), tab (Equiv.swap (2 : Fin 6) 3),
      tab (Equiv.swap (4 : Fin 6) 5)], ∃ x ∈ Z0 ⊔ Z2 ⊔ Z1, tab x = g := by
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl
    · exact ⟨_, le_sup_left (a := Z0 ⊔ Z2) (le_sup_left (a := Z0) (b := Z2) swap01_mem_Z0), rfl⟩
    · exact ⟨_, le_sup_left (a := Z0 ⊔ Z2) (le_sup_right (a := Z0) (b := Z2) swap23_mem_Z2), rfl⟩
    · exact ⟨_, le_sup_right (b := Z1) swap45_mem_Z1, rfl⟩
  intro σ hσ
  rw [mem_R2] at hσ
  have hw : R2l = R2words.map (evalG [tab (Equiv.swap (0 : Fin 6) 1),
      tab (Equiv.swap (2 : Fin 6) 3), tab (Equiv.swap (4 : Fin 6) 5)]) := by decide +kernel
  rw [hw, List.mem_map] at hσ
  obtain ⟨l, -, hl⟩ := hσ
  exact mem_of_word hG hl.symm

@[expose] def h01 : Gp 6 := Equiv.swap 0 2 * Equiv.swap 1 3

@[expose] def h12 : Gp 6 := Equiv.swap 2 4 * Equiv.swap 3 5

theorem h01_mem : h01 ∈ H2 := by
  rw [mem_H2]
  decide +kernel

theorem h12_mem : h12 ∈ H2 := by
  rw [mem_H2]
  decide +kernel

set_option maxRecDepth 100000 in
theorem cj_h01_Z0 : cj h01 Z0 = Z2 := by
  ext x
  rw [mem_cj, mem_subOf subOK_Z0, mem_subOf subOK_Z2]
  revert x
  decide +kernel

set_option maxRecDepth 100000 in
theorem cj_h01_Z2 : cj h01 Z2 = Z0 := by
  ext x
  rw [mem_cj, mem_subOf subOK_Z0, mem_subOf subOK_Z2]
  revert x
  decide +kernel

set_option maxRecDepth 100000 in
theorem cj_h12_Z2 : cj h12 Z2 = Z1 := by
  ext x
  rw [mem_cj, mem_Z1, mem_subOf subOK_Z2]
  revert x
  decide +kernel

set_option maxRecDepth 100000 in
theorem cj_h12_Z1 : cj h12 Z1 = Z2 := by
  ext x
  rw [mem_cj, mem_Z1, mem_subOf subOK_Z2]
  revert x
  decide +kernel

theorem exists_H2_conj_Z0 : (∃ h ∈ H2, cj h Z0 = Z2) ∧ (∃ h ∈ H2, cj h Z0 = Z1) :=
  ⟨⟨h01, h01_mem, cj_h01_Z0⟩, ⟨h12 * h01, H2.mul_mem h12_mem h01_mem, by
    rw [← cj_h12_Z2, ← cj_h01_Z0]
    ext x
    simp [mem_cj, mul_assoc]⟩⟩

theorem exists_H2_conj_Z2 : (∃ h ∈ H2, cj h Z2 = Z0) ∧ (∃ h ∈ H2, cj h Z2 = Z1) :=
  ⟨⟨h01, h01_mem, cj_h01_Z2⟩, ⟨h12, h12_mem, cj_h12_Z2⟩⟩

theorem exists_H2_conj_Z1 : (∃ h ∈ H2, cj h Z1 = Z2) ∧ (∃ h ∈ H2, cj h Z1 = Z0) :=
  ⟨⟨h12, h12_mem, cj_h12_Z1⟩, ⟨h01 * h12, H2.mul_mem h01_mem h12_mem, by
    rw [← cj_h01_Z2, ← cj_h12_Z1]
    ext x
    simp [mem_cj, mul_assoc]⟩⟩

end CFSG.Quasithin.H13.U3.GC137
