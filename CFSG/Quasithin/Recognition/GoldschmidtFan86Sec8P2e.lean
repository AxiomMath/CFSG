module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P2e2
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Stmt2

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace D10Set

variable {L : ZLab Γ G} {α : V} (D : D10Set L α)

theorem u_fixed_iff (F : FanTree Γ G) (h7 : Fan7 F L) (h81 : Fan81 F L) (h82 : Fan82a F L)
    (h512 : Fan512 F L) {δ' : V} (hY : D.IsYPair δ') {i j : Fin 5} (hij : i ≠ j) (k : Fin 5)
    {n : ℕ} (hn : n ≤ 4) :
    (D.y δ' i * D.y δ' j) • (D.P k).vert n = (D.P k).vert n ↔
      n ≤ 1 ∨ (n = 2 ∧ (k = midlab i j ∨ k = kstar i j ∨ k = kstar j i)) := by
  have h71c : Fan71c F L := h7.2.2.1
  obtain ⟨⟨hmi, hmj, hi1, hi2, -, hj1, hj2, -, -⟩, -, hall⟩ := fin5_midlab_facts i j hij
  interval_cases n
  · have e : (D.P k).vert 0 = α := D.start k
    rw [e]
    exact ⟨fun _ => Or.inl (by norm_num), fun _ => D.u_fixes_start F h71c h81 hY i j⟩
  · have e : (D.P k).vert 1 = D.beta k := rfl
    rw [e]
    refine ⟨fun _ => Or.inl (by norm_num), fun _ => ?_⟩
    rw [mul_smul, D.y_fixes_beta F h71c h81 hY j k, D.y_fixes_beta F h71c h81 hY i k]
  · have e : (D.P k).vert 2 = D.alpha k := rfl
    rw [e]
    rcases hall k with hk | hk | hk | hk | hk
    · exact ⟨fun _ => Or.inr ⟨rfl, Or.inl hk⟩, fun _ =>
        D.u_alpha_fixed F h71c h81 hY (by rw [hk]; exact hmi) (by rw [hk]; exact hmj)⟩
    · rw [hk]
      refine ⟨fun hfix => absurd hfix (D.u_alpha_moved_left F h71c h81 hY hij), fun hr => ?_⟩
      rcases hr with h1 | ⟨-, h2 | h2 | h2⟩
      · omega
      · exact absurd h2.symm hmi
      · exact absurd h2.symm hi1
      · exact absurd h2.symm hj1
    · rw [hk]
      refine ⟨fun hfix => absurd hfix (D.u_alpha_moved_right F h71c h81 hY hij), fun hr => ?_⟩
      rcases hr with h1 | ⟨-, h2 | h2 | h2⟩
      · omega
      · exact absurd h2.symm hmj
      · exact absurd h2.symm hi2
      · exact absurd h2.symm hj2
    · exact ⟨fun _ => Or.inr ⟨rfl, Or.inr (Or.inl hk)⟩, fun _ =>
        D.u_alpha_fixed F h71c h81 hY (by rw [hk]; exact hi1) (by rw [hk]; exact hi2)⟩
    · exact ⟨fun _ => Or.inr ⟨rfl, Or.inr (Or.inr hk)⟩, fun _ =>
        D.u_alpha_fixed F h71c h81 hY (by rw [hk]; exact hj1) (by rw [hk]; exact hj2)⟩
  · have e : (D.P k).vert 3 = D.xi k := rfl
    rw [e]
    refine ⟨fun hfix => absurd hfix (D.u_xi_moved F h7 h81 h82 h512 hY hij k), fun hr => ?_⟩
    rcases hr with h1 | ⟨h2, -⟩ <;> omega
  · have e : (D.P k).vert 4 = D.delta k := rfl
    rw [e]
    refine ⟨fun hfix => absurd hfix (D.u_delta_moved F h7 h81 h82 h512 hY hij k), fun hr => ?_⟩
    rcases hr with h1 | ⟨h2, -⟩ <;> omega

end D10Set

theorem fan_8_3e {F : FanTree Γ G} {L : ZLab Γ G} (h7 : Fan7 F L) (h81 : Fan81 F L)
    (h82 : Fan82a F L) (h512 : Fan512 F L) : Fan83e F L := by
  intro α D δ' hY i j hij
  have h : Fan71c F L := h7.2.2.1
  obtain ⟨⟨-, -, -, -, -, -, -, -, hij'⟩, -, -⟩ := fin5_midlab_facts i j hij
  have hp1 : pathSet Γ (D.alpha (kstar i j)) (D.alpha (kstar j i)) =
      {v | (∃ n, n ≤ 2 ∧ v = (D.P (kstar i j)).vert n) ∨
        ∃ n, n ≤ 2 ∧ v = (D.P (kstar j i)).vert n} :=
    D.pathSet_branches F h hij' (a := 2) (b := 2) (by norm_num) (by norm_num)
  have hp2 : pathSet Γ α (D.alpha (midlab i j)) =
      {v | ∃ n, n ≤ 2 ∧ v = (D.P (midlab i j)).vert n} :=
    D.pathSet_start F _ (a := 2) (by norm_num)
  have hfix := fun (k : Fin 5) {n : ℕ} (hn : n ≤ 4) => D.u_fixed_iff F h7 h81 h82 h512 hY hij k hn
  ext v
  rw [Set.mem_union, Set.mem_union, hp1, hp2]
  constructor
  · rintro ⟨⟨k, n, hn, rfl⟩, hv⟩
    rcases (hfix k hn).1 hv with hn1 | ⟨rfl, rfl | rfl | rfl⟩
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hn1 with rfl | rfl
      · exact Or.inr ⟨0, by norm_num, (D.start k).trans (D.start _).symm⟩
      · exact Or.inl (Or.inl (D.adj_start_beta k))
    · exact Or.inr ⟨2, le_rfl, rfl⟩
    · exact Or.inl (Or.inr (Or.inl ⟨2, le_rfl, rfl⟩))
    · exact Or.inl (Or.inr (Or.inr ⟨2, le_rfl, rfl⟩))
  · rintro ((hv | ⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩) | ⟨n, hn, rfl⟩)
    · obtain ⟨k, rfl⟩ := D.exists_beta_eq F h hv
      exact ⟨⟨k, 1, by norm_num, rfl⟩, (hfix k (n := 1) (by norm_num)).2 (Or.inl le_rfl)⟩
    · refine ⟨⟨kstar i j, n, by omega, rfl⟩, (hfix _ (by omega)).2 ?_⟩
      by_cases h1 : n ≤ 1
      · exact Or.inl h1
      · exact Or.inr ⟨by omega, Or.inr (Or.inl rfl)⟩
    · refine ⟨⟨kstar j i, n, by omega, rfl⟩, (hfix _ (by omega)).2 ?_⟩
      by_cases h1 : n ≤ 1
      · exact Or.inl h1
      · exact Or.inr ⟨by omega, Or.inr (Or.inr rfl)⟩
    · refine ⟨⟨midlab i j, n, by omega, rfl⟩, (hfix _ (by omega)).2 ?_⟩
      by_cases h1 : n ≤ 1
      · exact Or.inl h1
      · exact Or.inr ⟨by omega, Or.inl rfl⟩

end CFSG.Quasithin.Fan86
