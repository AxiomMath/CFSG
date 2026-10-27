module

public import CFSG.Quasithin.MS93.S4A44Nabla

public section

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

section Reduction

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B)

@[expose] def Disj442 (α α' : Vtx X) : Prop :=
  ¬ conjCl (stab X α) (ZM X (geo X α α' 2)) ≤ Qv X (geo X α' α 2) ∨
    ∃ g ∈ stab X α, ¬ conjCl (stab X (g • geo X α α' 2)) (ZM X α) ≤ Qv X (geo X α' α 4)

theorem isStraightUpTo_moveB (h : Hyp20 X) (hb : 4 ≤ critDist X) {α α' : Vtx X}
    (hc : IsCritical X α α') {m : ℕ} (hs : IsStraightUpTo X α α' m) {g : X.Universal}
    (hg : g ∈ stab X α) {k : X.Universal} (hk : k ∈ stab X (g • geo X α α' 2))
    (hkQ : ¬ ZM X (k • α) ≤ Qv X (geo X α' α 4)) :
    IsCritical X (k • α) (geo X α' α 4) ∧ IsStraightUpTo X (k • α) (geo X α' α 4) (m + 2) := by
  have hd : X.treeGraph.dist α α' = critDist X := hc.2.1
  have hd' : X.treeGraph.dist α' α = critDist X := by rw [tdist_comm]; exact hd
  obtain ⟨n, hn⟩ := ms21_v X h
  have hgα : g • α = α := (mem_stab X).mp hg
  have hkl : k • (g • geo X α α' 2) = g • geo X α α' 2 := (mem_stab X).mp hk
  have hal : X.treeGraph.dist α (g • geo X α α' 2) = 2 := by
    have := dist_smul X g α (geo X α α' 2)
    rwa [hgα, dist_geo X (by omega)] at this
  have hkal : X.treeGraph.dist (k • α) (g • geo X α α' 2) = 2 := by
    have := dist_smul X k α (g • geo X α α' 2)
    rwa [hkl, hal] at this
  have hα4 : X.treeGraph.dist α (geo X α' α 4) = critDist X - 4 := by
    rw [tdist_comm, dist_geo_right X (by omega), hd']
  have hM : IsMVtx X (k • α) := (isMVtx_smul X k α).mpr hc.1
  have hge : critDist X ≤ X.treeGraph.dist (k • α) (geo X α' α 4) := by
    by_contra hlt
    exact hkQ (zm_le_qv_of_dist_lt X hM (by omega))
  have t1 := dist_triangle X (k • α) (g • geo X α α' 2) α
  have t2 := dist_triangle X (k • α) α (geo X α' α 4)
  rw [tdist_comm X (g • geo X α α' 2) α, hal, hkal] at t1
  rw [hα4] at t2
  have hkα4 : X.treeGraph.dist (k • α) α = 4 := by omega
  have hdist : X.treeGraph.dist (k • α) (geo X α' α 4) = critDist X := by omega
  have hadd : X.treeGraph.dist (k • α) (geo X α' α 4) =
      X.treeGraph.dist (k • α) α + X.treeGraph.dist α (geo X α' α 4) := by omega
  have hadd' : X.treeGraph.dist (k • α) α =
      X.treeGraph.dist (k • α) (g • geo X α α' 2) + X.treeGraph.dist (g • geo X α α' 2) α := by
    rw [tdist_comm X (g • geo X α α' 2) α]
    omega
  have hsym : geo X α' α 4 = geo X α α' (critDist X - 4) := by
    have := geo_symm X (u := α) (w := α') (i := critDist X - 4) (by omega)
    rwa [hd, show critDist X - (critDist X - 4) = 4 by omega] at this
  have hgeo : ∀ j, j + 4 ≤ critDist X →
      geo X (k • α) (geo X α' α 4) (j + 4) = geo X α α' j := by
    intro j hj
    rw [show j + 4 = X.treeGraph.dist (k • α) α + j by omega,
      geo_of_dist_eq_add X hadd (k := j) (by omega), hsym,
      geo_geo X (i := j) (j := critDist X - 4) (by omega) (by omega)]
  have hgeo2 : geo X (k • α) (geo X α' α 4) 2 = g • geo X α α' 2 := by
    rw [geo_eq_of_dist_eq_add X hadd (k := 2) (by omega)]
    have := geo_of_dist_eq_add X hadd' (k := 0) (by omega)
    rwa [hkal, add_zero, geo_zero] at this
  refine ⟨⟨hM, hdist, hkQ⟩, fun i hi0 him hib => ?_⟩
  rw [hdist] at hib
  rcases (show i = 1 ∨ i = 2 ∨ 3 ≤ i by omega) with rfl | rfl | hi3
  ·
    refine ⟨k, ?_, ?_⟩
    · rw [show 2 * 1 = 2 from rfl, hgeo2]
      exact hk
    · rw [show 2 * 1 + 2 = 0 + 4 from rfl, hgeo 0 (by omega), geo_zero,
        show 2 * 1 - 2 = 0 from rfl, geo_zero]
  ·
    refine ⟨g, ?_, ?_⟩
    · rw [show 2 * 2 = 0 + 4 from rfl, hgeo 0 (by omega), geo_zero]
      exact hg
    · rw [show 2 * 2 + 2 = 2 + 4 from rfl, hgeo 2 (by omega), show 2 * 2 - 2 = 2 from rfl,
        hgeo2]
  ·
    obtain ⟨g', hg', hge'⟩ := hs (i - 2) (by omega) (by omega) (by rw [hd]; omega)
    refine ⟨g', ?_, ?_⟩
    · rw [show 2 * i = 2 * (i - 2) + 4 by omega, hgeo (2 * (i - 2)) (by omega)]
      exact hg'
    · rw [show 2 * i + 2 = 2 * (i - 2) + 2 + 4 by omega, hgeo (2 * (i - 2) + 2) (by omega),
        show 2 * i - 2 = 2 * (i - 2) - 2 + 4 by omega, hgeo (2 * (i - 2) - 2) (by omega)]
      exact hge'

theorem exists_isStraight_of_disj (h : Hyp20 X) (hb : 4 < critDist X)
    (hD : ∀ α α' : Vtx X, IsCritical X α α' → Disj442 X α α') :
    ∃ α α' : Vtx X, IsCritical X α α' ∧ IsStraight X α α' := by
  classical
  let P : ℕ → Prop := fun m => ∃ α α' : Vtx X, IsCritical X α α' ∧ IsStraightUpTo X α α' m
  have hP0 : P 0 := by
    obtain ⟨α, α', hc⟩ := exists_isCritical X h
    exact ⟨α, α', hc, fun i hi him _ => by omega⟩
  obtain ⟨α, α', hc, hs⟩ : P (Nat.findGreatest P (critDist X)) :=
    Nat.findGreatest_spec (Nat.zero_le _) hP0
  have hmax : ∀ j, Nat.findGreatest P (critDist X) < j → j ≤ critDist X → ¬ P j :=
    fun j hj hjb => Nat.findGreatest_is_greatest hj hjb
  have hd : X.treeGraph.dist α α' = critDist X := hc.2.1
  by_cases hfin : critDist X ≤ 2 * Nat.findGreatest P (critDist X)
  · exact ⟨α, α', hc, hs.isStraight X (by rw [hd]; exact hfin)⟩
  exfalso
  rcases hD α α' hc with hA | ⟨g, hg, hB⟩
  ·
    obtain ⟨g, hg, hgQ⟩ : ∃ g ∈ stab X α,
        ¬ ZM X (g • geo X α α' 2) ≤ Qv X (geo X α' α 2) := by
      by_contra hall
      push Not at hall
      exact hA (iSup₂_le fun g hg => by rw [← zm_smul]; exact hall g hg)
    have hν : IsMVtx X (g • geo X α α' 2) :=
      (isMVtx_smul X g _).mpr (isMVtx_geo_two X h (by omega) hc)
    have hdν : X.treeGraph.dist α (g • geo X α α' 2) = 2 := by
      have := dist_smul X g α (geo X α α' 2)
      rwa [(mem_stab X).mp hg, dist_geo X (by omega)] at this
    obtain ⟨hc', -, -⟩ := isCritical_move X (by omega) hc hν hdν hgQ
    exact hmax _ (Nat.lt_succ_self _) (by omega)
      ⟨_, _, hc', isStraightUpTo_move X h (by omega) hc hs hg hgQ⟩
  ·
    obtain ⟨k, hk, hkQ⟩ : ∃ k ∈ stab X (g • geo X α α' 2),
        ¬ ZM X (k • α) ≤ Qv X (geo X α' α 4) := by
      by_contra hall
      push Not at hall
      exact hB (iSup₂_le fun k hk => by rw [← zm_smul]; exact hall k hk)
    obtain ⟨hc', hs'⟩ := isStraightUpTo_moveB X h (by omega) hc hs hg hk hkQ
    exact hmax _ (by omega) (by omega) ⟨_, _, hc', hs'⟩

end Reduction

@[expose] def S442Disj : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L)
    (F : Type) (_ : Field F) (_ : Fintype F) (φ : ↥M →* ↥(StatedSL 3 F)), Hyp40 h φ →
    4 < critDist (puAmalgam h.le) →
    ∀ α α' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) α α' →
      Disj442 (puAmalgam h.le) α α'

theorem s442_of_disj (hD : S442Disj) : S442 := by
  intro G _ _ M T L h F _ _ φ hH hb
  exact exists_isStraight_of_disj _ h.hyp20 hb (hD G M T L h F inferInstance inferInstance φ hH hb)

end CFSG.Quasithin.MS93.S4A
