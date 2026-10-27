module

public import CFSG.Quasithin.Background.RonanE114HeLat

public section

namespace CFSG.Quasithin.RonanE114.HeOver

open CFSG.Quasithin.ModH CFSG.Quasithin.ModH.He1 CFSG.Quasithin.ModH.He2
open CFSG.QuasithinUnique.Ch1.SporLat.He

variable {J : Type} [Group J] [Finite J]

theorem key_Y1 : ∀ j : Fin 11, (j : ℕ) ∈ heIncl[1]! → 2 ∈ heIncl[(j : ℕ)]! →
    9 ∈ heIncl[(j : ℕ)]! → 3 * 1024 ≤ heIdx (j : ℕ) * 1024 → (j : ℕ) = 1 := by
  decide

theorem key_Y6 : ∀ j : Fin 11, (j : ℕ) ∈ heIncl[6]! → 2 ∈ heIncl[(j : ℕ)]! →
    5 ∈ heIncl[(j : ℕ)]! → 3 * 1024 ≤ heIdx (j : ℕ) * 1024 → (j : ℕ) = 6 := by
  decide

theorem key_Y9A : ∀ j : Fin 11, heIdx (j : ℕ) = 9 → 4 ∈ heIncl[(j : ℕ)]! →
    (j : ℕ) = 2 ∨ (j : ℕ) = 9 := by
  decide

theorem key_Y9B : ∀ j : Fin 11, heIdx (j : ℕ) = 9 → 3 ∈ heIncl[(j : ℕ)]! →
    (j : ℕ) = 2 ∨ (j : ℕ) = 5 := by
  decide

theorem he_Y2_inf_Y9 (hl : HeLat J) : hl.Y 2 ⊓ hl.Y 9 = hl.Y 1 := by
  refine le_antisymm ?_ (le_inf (Y_le hl (by norm_num) (by norm_num) (by decide))
    (Y_le hl (by norm_num) (by norm_num) (by decide)))
  have hS : hl.S ≤ hl.Y 2 ⊓ hl.Y 9 := le_inf (hl.S_le_Y 2) (hl.S_le_Y 9)
  rcases hl.complete _ hS with ⟨j, hj, hjeq⟩ | htop
  · have h1le : hl.Y 1 ≤ hl.Y 2 ⊓ hl.Y 9 := le_inf
      (Y_le hl (by norm_num) (by norm_num) (by decide))
      (Y_le hl (by norm_num) (by norm_num) (by decide))
    have h1j : hl.Y 1 ≤ hl.Y j := h1le.trans hjeq.le
    have hj1 : j ∈ heIncl[1]! := (hl.le_iff (by norm_num) hj).mp h1j
    have hi2 : 2 ∈ heIncl[j]! := (hl.le_iff hj (by norm_num)).mp (hjeq ▸ inf_le_left)
    have hi9 : 9 ∈ heIncl[j]! := (hl.le_iff hj (by norm_num)).mp (hjeq ▸ inf_le_right)
    have hcard : 3 * 1024 ≤ heIdx j * 1024 := by
      have h := Subgroup.card_le_of_le h1j
      rwa [card_Y_idx hl (by norm_num), card_Y_idx hl hj] at h
    have hj1' : j = 1 := key_Y1 ⟨j, hj⟩ hj1 hi2 hi9 hcard
    rw [hjeq, hj1']
  · exfalso
    have : hl.Y 2 = ⊤ := top_le_iff.mp (htop ▸ inf_le_left)
    have h1 := congrArg (fun K : Subgroup J => Nat.card ↥K) this
    rw [card_top hl, card_Y_idx hl (by norm_num)] at h1
    norm_num [heIdx] at h1

theorem he_Y2_inf_Y5 (hl : HeLat J) : hl.Y 2 ⊓ hl.Y 5 = hl.Y 6 := by
  refine le_antisymm ?_ (le_inf (Y_le hl (by norm_num) (by norm_num) (by decide))
    (Y_le hl (by norm_num) (by norm_num) (by decide)))
  have hS : hl.S ≤ hl.Y 2 ⊓ hl.Y 5 := le_inf (hl.S_le_Y 2) (hl.S_le_Y 5)
  rcases hl.complete _ hS with ⟨j, hj, hjeq⟩ | htop
  · have h6le : hl.Y 6 ≤ hl.Y 2 ⊓ hl.Y 5 := le_inf
      (Y_le hl (by norm_num) (by norm_num) (by decide))
      (Y_le hl (by norm_num) (by norm_num) (by decide))
    have h6j : hl.Y 6 ≤ hl.Y j := h6le.trans hjeq.le
    have hj6 : j ∈ heIncl[6]! := (hl.le_iff (by norm_num) hj).mp h6j
    have hi2 : 2 ∈ heIncl[j]! := (hl.le_iff hj (by norm_num)).mp (hjeq ▸ inf_le_left)
    have hi5 : 5 ∈ heIncl[j]! := (hl.le_iff hj (by norm_num)).mp (hjeq ▸ inf_le_right)
    have hcard : 3 * 1024 ≤ heIdx j * 1024 := by
      have h := Subgroup.card_le_of_le h6j
      rwa [card_Y_idx hl (by norm_num), card_Y_idx hl hj] at h
    have hj6' : j = 6 := key_Y6 ⟨j, hj⟩ hj6 hi2 hi5 hcard
    rw [hjeq, hj6']
  · exfalso
    have : hl.Y 2 = ⊤ := top_le_iff.mp (htop ▸ inf_le_left)
    have h1 := congrArg (fun K : Subgroup J => Nat.card ↥K) this
    rw [card_top hl, card_Y_idx hl (by norm_num)] at h1
    norm_num [heIdx] at h1

theorem map_Y9_of_fixes_Y3 (hl : HeLat J) {α : MulAut J}
    (hα : hl.S.map α.toMonoidHom = hl.S) (h3 : (hl.Y 3).map α.toMonoidHom = hl.Y 3) :
    (hl.Y 9).map α.toMonoidHom = hl.Y 9 := by
  have h4 : (hl.Y 4).map α.toMonoidHom = hl.Y 4 := by
    rcases aut_Y34 hl hα with ⟨-, h4⟩ | ⟨h3', -⟩
    · exact h4
    · exact absurd (h3'.symm.trans h3) (fun h => Y3_ne_Y4 hl h.symm)
  obtain ⟨j, hj, hjeq, hidx⟩ := map_member hl hα (a := 9) (by norm_num)
  have h9 : heIdx j = 9 := by rw [hidx]; rfl
  have hle9 : hl.Y 9 ≤ hl.Y 4 := Y_le hl (by norm_num) (by norm_num) (by decide)
  have hm : (hl.Y 9).map α.toMonoidHom ≤ (hl.Y 4).map α.toMonoidHom :=
    Subgroup.map_mono hle9
  rw [hjeq, h4] at hm
  have hi4 : 4 ∈ heIncl[j]! := (hl.le_iff hj (by norm_num)).mp hm
  rcases key_Y9A ⟨j, hj⟩ h9 hi4 with rfl | rfl
  · exfalso
    have h2 : (hl.Y 2).map α.toMonoidHom = hl.Y 2 := by
      rw [← he_Y3_inf_Y4 hl, Subgroup.map_inf_eq _ _ _ α.injective, h3, h4]
    have h1 : (hl.Y 1).map α.toMonoidHom = hl.Y 2 := by
      rw [← he_Y2_inf_Y9 hl, Subgroup.map_inf_eq _ _ _ α.injective, h2, hjeq, inf_idem]
    obtain ⟨j1, hj1, hj1eq, hi1⟩ := map_member hl hα (a := 1) (by norm_num)
    rw [h1] at hj1eq
    have hc : Nat.card ↥(hl.Y 2) = Nat.card ↥(hl.Y j1) :=
      congrArg (fun K : Subgroup J => Nat.card ↥K) hj1eq
    rw [card_Y_idx hl (by norm_num), card_Y_idx hl hj1, hi1] at hc
    norm_num [heIdx] at hc
  · exact hjeq

theorem map_Y9_of_swaps_Y3 (hl : HeLat J) {α : MulAut J}
    (hα : hl.S.map α.toMonoidHom = hl.S) (h3 : (hl.Y 3).map α.toMonoidHom = hl.Y 4)
    (h4 : (hl.Y 4).map α.toMonoidHom = hl.Y 3) :
    (hl.Y 9).map α.toMonoidHom = hl.Y 5 := by
  obtain ⟨j, hj, hjeq, hidx⟩ := map_member hl hα (a := 9) (by norm_num)
  have h9 : heIdx j = 9 := by rw [hidx]; rfl
  have hle9 : hl.Y 9 ≤ hl.Y 4 := Y_le hl (by norm_num) (by norm_num) (by decide)
  have hm : (hl.Y 9).map α.toMonoidHom ≤ (hl.Y 4).map α.toMonoidHom :=
    Subgroup.map_mono hle9
  rw [hjeq, h4] at hm
  have hi3 : 3 ∈ heIncl[j]! := (hl.le_iff hj (by norm_num)).mp hm
  rcases key_Y9B ⟨j, hj⟩ h9 hi3 with rfl | rfl
  · exfalso
    have h2 : (hl.Y 2).map α.toMonoidHom = hl.Y 2 := by
      rw [← he_Y3_inf_Y4 hl, Subgroup.map_inf_eq _ _ _ α.injective, h3, h4, inf_comm]
    have h1 : (hl.Y 1).map α.toMonoidHom = hl.Y 2 := by
      rw [← he_Y2_inf_Y9 hl, Subgroup.map_inf_eq _ _ _ α.injective, h2, hjeq, inf_idem]
    obtain ⟨j1, hj1, hj1eq, hi1⟩ := map_member hl hα (a := 1) (by norm_num)
    rw [h1] at hj1eq
    have hc : Nat.card ↥(hl.Y 2) = Nat.card ↥(hl.Y j1) :=
      congrArg (fun K : Subgroup J => Nat.card ↥K) hj1eq
    rw [card_Y_idx hl (by norm_num), card_Y_idx hl hj1, hi1] at hc
    norm_num [heIdx] at hc
  · exact hjeq

theorem map_Y1_of_fixes_Y3 (hl : HeLat J) {α : MulAut J}
    (hα : hl.S.map α.toMonoidHom = hl.S) (h3 : (hl.Y 3).map α.toMonoidHom = hl.Y 3) :
    (hl.Y 1).map α.toMonoidHom = hl.Y 1 := by
  have h4 : (hl.Y 4).map α.toMonoidHom = hl.Y 4 := by
    rcases aut_Y34 hl hα with ⟨-, h4⟩ | ⟨h3', -⟩
    · exact h4
    · exact absurd (h3'.symm.trans h3) (fun h => Y3_ne_Y4 hl h.symm)
  have h2 : (hl.Y 2).map α.toMonoidHom = hl.Y 2 := by
    rw [← he_Y3_inf_Y4 hl, Subgroup.map_inf_eq _ _ _ α.injective, h3, h4]
  rw [← he_Y2_inf_Y9 hl, Subgroup.map_inf_eq _ _ _ α.injective, h2,
    map_Y9_of_fixes_Y3 hl hα h3]

theorem map_Y1_of_swaps_Y3 (hl : HeLat J) {α : MulAut J}
    (hα : hl.S.map α.toMonoidHom = hl.S) (h3 : (hl.Y 3).map α.toMonoidHom = hl.Y 4)
    (h4 : (hl.Y 4).map α.toMonoidHom = hl.Y 3) :
    (hl.Y 1).map α.toMonoidHom = hl.Y 6 := by
  have h2 : (hl.Y 2).map α.toMonoidHom = hl.Y 2 := by
    rw [← he_Y3_inf_Y4 hl, Subgroup.map_inf_eq _ _ _ α.injective, h3, h4, inf_comm]
  rw [← he_Y2_inf_Y9 hl, Subgroup.map_inf_eq _ _ _ α.injective, h2,
    map_Y9_of_swaps_Y3 hl hα h3 h4, he_Y2_inf_Y5 hl]

end CFSG.Quasithin.RonanE114.HeOver

end
