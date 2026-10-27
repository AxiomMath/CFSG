module

public import CFSG.Quasithin.H13.GoldschmidtC137S6Fin3

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Quasithin CFSG.Quasithin.B3

@[expose] def K9l : List Tab :=
  [[0,1,2,3,4,5],[0,1,2,4,5,3],[0,1,2,5,3,4],[1,2,0,3,4,5],[1,2,0,4,5,3],[1,2,0,5,3,4],
    [2,0,1,3,4,5],[2,0,1,4,5,3],[2,0,1,5,3,4]]

theorem subOK_K9 : subOK 6 K9l = true := by decide +kernel

noncomputable abbrev K9 : Subgroup (Gp 6) := subOf 6 K9l

set_option maxRecDepth 100000 in
theorem K9_sign : ∀ σ : Gp 6, tab σ ∈ K9l → Equiv.Perm.sign σ = 1 := by
  decide +kernel

theorem K9_le_A6 : K9 ≤ alternatingGroup (Fin 6) := fun σ hσ =>
  (Equiv.Perm.mem_alternatingGroup).2 (K9_sign σ ((mem_subOf subOK_K9).1 hσ))

theorem card_fixV_K9 : Nat.card (fixV (K9.map (Mod.act 6 Mod.ut0))) = 1 := by
  have h : Nat.card (fixV (K9.map (Mod.act 6 Mod.ut0))) * cN 6 Mod.ut0 = cntF 6 Mod.ut0 K9l :=
    card_fix_cnt Mod.ut0 K9 K9l (subOK_spec subOK_K9).1 (fun x => mem_subOf subOK_K9)
  rw [cN6] at h
  have h2 : cntF 6 Mod.ut0 K9l = 2 := by decide +kernel
  omega

theorem fixV_A6 : fixV ((alternatingGroup (Fin 6)).map (Mod.act 6 Mod.ut0)) = ⊥ := by
  have hle : fixV ((alternatingGroup (Fin 6)).map (Mod.act 6 Mod.ut0)) ≤
      fixV (K9.map (Mod.act 6 Mod.ut0)) := fun v hv x hx => by
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hx
    exact hv _ (Subgroup.mem_map_of_mem _ (K9_le_A6 hz))
  have hc : Nat.card (fixV ((alternatingGroup (Fin 6)).map (Mod.act 6 Mod.ut0))) ≤ 1 := by
    rw [← card_fixV_K9]
    exact Subgroup.card_le_of_le hle
  exact Subgroup.eq_bot_of_card_le _ hc

theorem rkIdx_A6 : rkIdx (fixV ((alternatingGroup (Fin 6)).map (Mod.act 6 Mod.ut0))) = 4 := by
  unfold rkIdx
  rw [fixV_A6, Subgroup.index_bot, card_V6, show (16 : ℕ) = 2 ^ 4 by norm_num,
    padicValNat.prime_pow]

@[expose] def cptP : Gp 6 := Equiv.swap 2 4 * Equiv.swap 2 5

theorem cptP_even : cptP ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

theorem cptP_conj : cptP⁻¹ * Equiv.swap (2 : Fin 6) 4 * cptP = Equiv.swap 4 5 := by
  decide +kernel

theorem R1_sup_eq_top : R1 ⊔ cj cptP Z1 = ⊤ := by
  have h24 : Equiv.swap (2 : Fin 6) 4 ∈ cj cptP Z1 := by
    rw [mem_cj, cptP_conj]
    exact swap45_mem_Z1
  have hG : ∀ g ∈ [tab (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 2 3),
      tab (Equiv.swap (0 : Fin 6) 2 * Equiv.swap 1 3), tab (Equiv.swap (4 : Fin 6) 5),
      tab (Equiv.swap (2 : Fin 6) 4)], ∃ x ∈ R1 ⊔ cj cptP Z1, tab x = g := by
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact ⟨_, le_sup_left (a := R1) ((mem_R1).2 (by decide +kernel)), rfl⟩
    · exact ⟨_, le_sup_left (a := R1) ((mem_R1).2 (by decide +kernel)), rfl⟩
    · exact ⟨_, le_sup_left (a := R1) swap45_mem_R1, rfl⟩
    · exact ⟨_, le_sup_right (b := cj cptP Z1) h24, rfl⟩
  apply eq_top_of_adjacent
  intro i
  fin_cases i
  · exact mem_of_word hG (l := [3, 0, 3, 0, 3, 0]) (by decide +kernel)
  · exact mem_of_word hG (l := [3, 1, 0, 3, 1, 0, 3]) (by decide +kernel)
  · exact mem_of_word hG (l := [3, 0, 3, 0, 3]) (by decide +kernel)
  · exact mem_of_word hG (l := [0, 3, 0]) (by decide +kernel)
  · exact mem_of_word hG (l := [2]) (by decide +kernel)

end CFSG.Quasithin.H13.U3.GC137
