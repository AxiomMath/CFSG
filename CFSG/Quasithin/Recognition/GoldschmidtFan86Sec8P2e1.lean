module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P2V2

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem fixes_parent (F : FanTree Γ G) {g : G} {α p c : V} (hg : g • α = α) (hpc : Γ.Adj p c)
    (hd : Γ.dist α p + 1 = Γ.dist α c) (hc : g • c = c) : g • p = p := by
  have h1 : Γ.Adj (g • p) c := by
    have := (F.adj_smul g p c).2 hpc
    rwa [hc] at this
  have h2 : Γ.dist α (g • p) + 1 = Γ.dist α c := by
    have := dist_smul F g α p
    rw [hg] at this
    omega
  exact IsTree.eq_of_dist_succ F.isTree (r := α) h1 hpc h2 hd

namespace D10Set

variable {L : ZLab Γ G} {α : V} (D : D10Set L α)

theorem y_alpha_eq (F : FanTree Γ G) (h : Fan71c F L) (h81 : Fan81 F L) {δ' : V}
    (hY : D.IsYPair δ') {i j k : Fin 5} (hki : k ≠ i) (hkj : k ≠ j) :
    D.y δ' i • D.alpha k = D.y δ' j • D.alpha k := by
  have hadj : ∀ a : Fin 5, Γ.Adj (D.beta k) (D.y δ' a • D.alpha k) := fun a => by
    have := (F.adj_smul (D.y δ' a) (D.beta k) (D.alpha k)).2 (D.adj_beta_alpha k)
    rwa [D.y_fixes_beta F h h81 hY a k] at this
  have hα : ∀ a : Fin 5, D.y δ' a • D.alpha k ≠ α := fun a e => D.alpha_ne_start k (by
    apply MulAction.injective (D.y δ' a)
    show D.y δ' a • D.alpha k = D.y δ' a • α
    rw [e, D.y_fixes_alpha_start F h h81 hY a])
  have hne : ∀ a : Fin 5, a ≠ k → D.y δ' a • D.alpha k ≠ D.alpha k := fun a hak =>
    D.y_moves_alpha F h h81 hY (Ne.symm hak)
  obtain ⟨t, hts, hat, hjt⟩ := exists_third_neighbor (D.valence_beta F k)
    (D.adj_start_beta k).symm (D.adj_beta_alpha k) (D.alpha_ne_start k).symm
  have hthird : ∀ a : Fin 5, a ≠ k → D.y δ' a • D.alpha k = t := by
    intro a hak
    have hmem : D.y δ' a • D.alpha k ∈ Γ.neighborSet (D.beta k) := hadj a
    rw [hts] at hmem
    rcases hmem with h1 | h1 | h1
    · exact absurd h1 (hα a)
    · exact absurd h1 (hne a hak)
    · exact h1
  rw [hthird i (Ne.symm hki), hthird j (Ne.symm hkj)]

theorem u_alpha_fixed (F : FanTree Γ G) (h : Fan71c F L) (h81 : Fan81 F L) {δ' : V}
    (hY : D.IsYPair δ') {i j k : Fin 5} (hki : k ≠ i) (hkj : k ≠ j) :
    (D.y δ' i * D.y δ' j) • D.alpha k = D.alpha k := by
  rw [mul_smul, ← D.y_alpha_eq F h h81 hY hki hkj, D.y_smul_smul F h hY]

theorem u_alpha_moved_left (F : FanTree Γ G) (h : Fan71c F L) (h81 : Fan81 F L) {δ' : V}
    (hY : D.IsYPair δ') {i j : Fin 5} (hij : i ≠ j) :
    (D.y δ' i * D.y δ' j) • D.alpha i ≠ D.alpha i := by
  intro hfix
  rw [mul_smul] at hfix
  have hy : D.y δ' i • D.y δ' j • D.alpha i = D.y δ' j • D.alpha i := by
    have := D.y_fixes_ball_beta F h h81 hY i (D.y δ' j • D.alpha i) (by
      have h1 := dist_smul F (D.y δ' j) (D.beta i) (D.alpha i)
      rw [D.y_fixes_beta F h h81 hY j i, D.dist_beta_alpha] at h1
      rw [h1]
      norm_num)
    exact this
  rw [hy] at hfix
  exact D.y_moves_alpha F h h81 hY hij hfix

theorem u_alpha_moved_right (F : FanTree Γ G) (h : Fan71c F L) (h81 : Fan81 F L) {δ' : V}
    (hY : D.IsYPair δ') {i j : Fin 5} (hij : i ≠ j) :
    (D.y δ' i * D.y δ' j) • D.alpha j ≠ D.alpha j := by
  intro hfix
  rw [mul_smul] at hfix
  have hy : D.y δ' j • D.alpha j = D.alpha j :=
    (D.y_fixed_iff F h h81 hY j (by rw [D.dist_start_alpha F j]; norm_num)).2
      (Or.inl (by rw [SimpleGraph.dist_self]; norm_num))
  rw [hy] at hfix
  exact D.y_moves_alpha F h h81 hY hij.symm hfix

theorem u_fixes_start (F : FanTree Γ G) (h : Fan71c F L) (h81 : Fan81 F L) {δ' : V}
    (hY : D.IsYPair δ') (i j : Fin 5) : (D.y δ' i * D.y δ' j) • α = α := by
  rw [mul_smul, D.y_fixes_alpha_start F h h81 hY j, D.y_fixes_alpha_start F h h81 hY i]

end D10Set

end CFSG.Quasithin.Fan86
