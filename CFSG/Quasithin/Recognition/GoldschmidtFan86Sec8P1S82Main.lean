module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1S82Pts
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1S82Path
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1S82Move

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace D10Set

variable {L : ZLab Γ G} {α : V} (D : D10Set L α)

theorem fixed_iff (F : FanTree Γ G) (h7 : Fan7 F L) (h512 : Fan512 F L) {i j : Fin 5}
    (hij : i ≠ j) (k : Fin 5) {n : ℕ} (hn : n ≤ 4) :
    (L.z (D.alpha i) * L.z (D.alpha j)) • (D.P k).vert n = (D.P k).vert n ↔
      (k = midlab i j ∨ ((k = i ∨ k = j) ∧ n ≤ 2) ∨
        ((k = kstar i j ∨ k = kstar j i) ∧ n ≤ 3)) := by
  have h : Fan71c F L := h7.2.2.1
  obtain ⟨⟨hmi, hmj, hi1, hi2, hi3, hj1, hj2, hj3, hij'⟩, ⟨hmid, -⟩, hall⟩ :=
    fin5_midlab_facts i j hij
  rcases hall k with hk | hk | hk | hk | hk
  · rw [hk]
    simp only [true_or, iff_true]
    exact D.fixed_mid F h h512 (Ne.symm hmi) (Ne.symm hmj) hmid hn
  · rw [hk, D.fixed_iff_left F h hij hn]
    simp [hmi.symm, hi1.symm, hj1.symm, hij]
  · rw [hk, D.fixed_iff_right F h hij hn]
    simp [hmj.symm, hi2.symm, hj2.symm, hij.symm]
  · rw [hk, D.fixed_iff_other F h7 h512 hij (Ne.symm hmi) (Ne.symm hmj) hmid hi1.symm
      hi2.symm hi3.symm hn]
    simp [hi3, hi1, hi2, hij']
  · rw [hk, D.fixed_iff_other F h7 h512 hij (Ne.symm hmi) (Ne.symm hmj) hmid hj1.symm
      hj2.symm hj3.symm hn]
    simp [hj3, hj1, hj2, hij'.symm]

end D10Set

theorem fan_8_2b {F : FanTree Γ G} {L : ZLab Γ G} (h7 : Fan7 F L) (h512 : Fan512 F L) :
    Fan82b F L := by
  intro α D i j hij
  have h : Fan71c F L := h7.2.2.1
  obtain ⟨⟨-, -, -, -, -, -, -, -, hij'⟩, -, -⟩ := fin5_midlab_facts i j hij
  have hp1 : pathSet Γ (D.alpha i) (D.alpha j) =
      {v | (∃ n, n ≤ 2 ∧ v = (D.P i).vert n) ∨ ∃ n, n ≤ 2 ∧ v = (D.P j).vert n} :=
    D.pathSet_branches F h hij (a := 2) (b := 2) (by norm_num) (by norm_num)
  have hp2 : pathSet Γ (D.xi (kstar i j)) (D.xi (kstar j i)) =
      {v | (∃ n, n ≤ 3 ∧ v = (D.P (kstar i j)).vert n) ∨
        ∃ n, n ≤ 3 ∧ v = (D.P (kstar j i)).vert n} :=
    D.pathSet_branches F h hij' (a := 3) (b := 3) (by norm_num) (by norm_num)
  have hp3 : pathSet Γ α (D.delta (midlab i j)) =
      {v | ∃ n, n ≤ 4 ∧ v = (D.P (midlab i j)).vert n} :=
    D.pathSet_start F _ (a := 4) (by norm_num)
  ext v
  rw [Set.mem_union, Set.mem_union, hp1, hp2, hp3]
  constructor
  · rintro ⟨⟨k, n, hn, rfl⟩, hfix⟩
    rw [D.fixed_iff F h7 h512 hij k hn] at hfix
    rcases hfix with hk | ⟨hk, hn2⟩ | ⟨hk, hn3⟩
    · exact Or.inr ⟨n, hn, by rw [hk]⟩
    · rcases hk with rfl | rfl
      · exact Or.inl (Or.inl (Or.inl ⟨n, hn2, rfl⟩))
      · exact Or.inl (Or.inl (Or.inr ⟨n, hn2, rfl⟩))
    · rcases hk with rfl | rfl
      · exact Or.inl (Or.inr (Or.inl ⟨n, hn3, rfl⟩))
      · exact Or.inl (Or.inr (Or.inr ⟨n, hn3, rfl⟩))
  · rintro (((⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩) | (⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩)) | ⟨n, hn, rfl⟩)
    · exact ⟨⟨i, n, by omega, rfl⟩,
        (D.fixed_iff F h7 h512 hij i (by omega)).2 (Or.inr (Or.inl ⟨Or.inl rfl, hn⟩))⟩
    · exact ⟨⟨j, n, by omega, rfl⟩,
        (D.fixed_iff F h7 h512 hij j (by omega)).2 (Or.inr (Or.inl ⟨Or.inr rfl, hn⟩))⟩
    · exact ⟨⟨kstar i j, n, by omega, rfl⟩,
        (D.fixed_iff F h7 h512 hij (kstar i j) (by omega)).2
          (Or.inr (Or.inr ⟨Or.inl rfl, hn⟩))⟩
    · exact ⟨⟨kstar j i, n, by omega, rfl⟩,
        (D.fixed_iff F h7 h512 hij (kstar j i) (by omega)).2
          (Or.inr (Or.inr ⟨Or.inr rfl, hn⟩))⟩
    · exact ⟨⟨midlab i j, n, hn, rfl⟩,
        (D.fixed_iff F h7 h512 hij (midlab i j) hn).2 (Or.inl rfl)⟩

theorem fan_8_2c {F : FanTree Γ G} {L : ZLab Γ G} (h7 : Fan7 F L) (h512 : Fan512 F L) :
    Fan82c F L := by
  intro α D i j hij
  obtain ⟨⟨hmi, -, -, -, -, -, -, -, -⟩, ⟨hmid, -⟩, -⟩ := fin5_midlab_facts i j hij
  refine ⟨?_, D.not_mem_nbrStab_delta F h7.2.2.1 (Ne.symm hmi) hmid⟩
  exact fan_8_2c_ball h7 h512 D hij

theorem fan_8_2 {F : FanTree Γ G} {L : ZLab Γ G} (h7 : Fan7 F L) (h81 : Fan81 F L)
    (h512 : Fan512 F L) : Fan82 F L :=
  ⟨fan_8_2a h7 h81 h512, fan_8_2b h7 h512, fan_8_2c h7 h512⟩

end CFSG.Quasithin.Fan86
