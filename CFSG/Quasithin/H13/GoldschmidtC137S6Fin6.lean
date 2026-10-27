module

public import CFSG.Quasithin.H13.GoldschmidtC137S6Fin5

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Quasithin CFSG.Quasithin.B3

theorem rank_R2 : rk R2 = 3 ∧ rkIdx (fixV (R2.map (Mod.act 6 Mod.ut0))) = 2 := by
  have h := rank_data (n := 6) (by norm_num) Mod.ut0 subOK_lists.2.2.2.2 (r := 3) (s := 2)
    (by decide +kernel) (by decide +kernel)
  exact ⟨h.1, h.2.1⟩

theorem rank_Z0 : rk Z0 = 1 ∧ rkIdx (fixV (Z0.map (Mod.act 6 Mod.ut0))) = 1 := by
  have h := rank_data (n := 6) (by norm_num) Mod.ut0 subOK_Z0 (r := 1) (s := 1)
    (by decide +kernel) (by decide +kernel)
  exact ⟨h.1, h.2.1⟩

theorem rank_Z2 : rk Z2 = 1 ∧ rkIdx (fixV (Z2.map (Mod.act 6 Mod.ut0))) = 1 := by
  have h := rank_data (n := 6) (by norm_num) Mod.ut0 subOK_Z2 (r := 1) (s := 1)
    (by decide +kernel) (by decide +kernel)
  exact ⟨h.1, h.2.1⟩

@[expose] def c2L : Gp 6 := Equiv.swap 0 2 * Equiv.swap 0 1

@[expose] def c3L : Gp 6 := Equiv.swap 0 3 * Equiv.swap 1 4

theorem c2L_even : c2L ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

theorem c3L_even : c3L ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

theorem c2L_conj : c2L⁻¹ * Equiv.swap (1 : Fin 6) 2 * c2L = Equiv.swap 0 1 := by
  decide +kernel

theorem c3L_conj : c3L⁻¹ * Equiv.swap (3 : Fin 6) 4 * c3L = Equiv.swap 0 1 := by
  decide +kernel

theorem R2_sup_eq_top : R2 ⊔ cj c2L Z0 ⊔ cj c3L Z0 = ⊤ := by
  have h12 : Equiv.swap (1 : Fin 6) 2 ∈ cj c2L Z0 := by
    rw [mem_cj, c2L_conj]
    exact swap01_mem_Z0
  have h34 : Equiv.swap (3 : Fin 6) 4 ∈ cj c3L Z0 := by
    rw [mem_cj, c3L_conj]
    exact swap01_mem_Z0
  have hR2 : ∀ a b : Fin 6, tab (Equiv.swap a b) ∈ R2l → Equiv.swap a b ∈ R2 := fun a b h =>
    (mem_R2).2 h
  have hG : ∀ g ∈ [tab (Equiv.swap (0 : Fin 6) 1), tab (Equiv.swap (2 : Fin 6) 3),
      tab (Equiv.swap (4 : Fin 6) 5), tab (Equiv.swap (1 : Fin 6) 2),
      tab (Equiv.swap (3 : Fin 6) 4)], ∃ x ∈ R2 ⊔ cj c2L Z0 ⊔ cj c3L Z0, tab x = g := by
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, le_sup_left (a := R2 ⊔ cj c2L Z0) (le_sup_left (a := R2) (b := cj c2L Z0)
        (hR2 0 1 (by decide +kernel))), rfl⟩
    · exact ⟨_, le_sup_left (a := R2 ⊔ cj c2L Z0) (le_sup_left (a := R2) (b := cj c2L Z0)
        (hR2 2 3 (by decide +kernel))), rfl⟩
    · exact ⟨_, le_sup_left (a := R2 ⊔ cj c2L Z0) (le_sup_left (a := R2) (b := cj c2L Z0)
        (hR2 4 5 (by decide +kernel))), rfl⟩
    · exact ⟨_, le_sup_left (a := R2 ⊔ cj c2L Z0) (le_sup_right (a := R2) (b := cj c2L Z0) h12),
        rfl⟩
    · exact ⟨_, le_sup_right (b := cj c3L Z0) h34, rfl⟩
  apply eq_top_of_adjacent
  intro i
  fin_cases i
  · exact mem_of_word hG (l := [0]) (by decide +kernel)
  · exact mem_of_word hG (l := [3]) (by decide +kernel)
  · exact mem_of_word hG (l := [1]) (by decide +kernel)
  · exact mem_of_word hG (l := [4]) (by decide +kernel)
  · exact mem_of_word hG (l := [2]) (by decide +kernel)

end CFSG.Quasithin.H13.U3.GC137
