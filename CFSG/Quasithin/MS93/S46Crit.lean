module

public import CFSG.Quasithin.MS93.S46Base

public section

namespace CFSG.Quasithin.MS93.S46

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] {X : GoldAmalgam A C B}

section Path

variable {α α' : Vtx X}

theorem dist_eq_four (hb : critDist X = 4) (hc : IsCritical X α α') :
    X.treeGraph.dist α α' = 4 := hc.2.1.trans hb

theorem dist_geo_crit (hb : critDist X = 4) (hc : IsCritical X α α') {i : ℕ} (hi : i ≤ 4) :
    X.treeGraph.dist α (geo X α α' i) = i :=
  dist_geo X (by rw [dist_eq_four hb hc]; exact hi)

theorem dist_geo_crit_right (hb : critDist X = 4) (hc : IsCritical X α α') {i : ℕ} (hi : i ≤ 4) :
    X.treeGraph.dist (geo X α α' i) α' = 4 - i := by
  rw [dist_geo_right X (by rw [dist_eq_four hb hc]; exact hi), dist_eq_four hb hc]

theorem adj_geo_crit (hb : critDist X = 4) (hc : IsCritical X α α') {i : ℕ} (hi : i < 4) :
    X.treeGraph.Adj (geo X α α' i) (geo X α α' (i + 1)) :=
  adj_geo X (by rw [dist_eq_four hb hc]; exact hi)

theorem geo_rev (hb : critDist X = 4) (hc : IsCritical X α α') {i : ℕ} (hi : i ≤ 4) :
    geo X α' α i = geo X α α' (4 - i) := by
  have h := geo_symm X (u := α) (w := α') (i := 4 - i) (by rw [dist_eq_four hb hc]; omega)
  rw [dist_eq_four hb hc, show 4 - (4 - i) = i by omega] at h
  exact h

theorem geo_rev_one (hb : critDist X = 4) (hc : IsCritical X α α') :
    geo X α' α 1 = geo X α α' 3 := geo_rev hb hc (by omega)

theorem geo_rev_two (hb : critDist X = 4) (hc : IsCritical X α α') :
    geo X α' α 2 = geo X α α' 2 := geo_rev hb hc (by omega)

theorem geo_four (hb : critDist X = 4) (hc : IsCritical X α α') : geo X α α' 4 = α' :=
  geo_of_le X (by rw [dist_eq_four hb hc])

theorem isMVtx_geo_crit (hb : critDist X = 4) (hc : IsCritical X α α') {i : ℕ} (hi : i ≤ 4) :
    IsMVtx X (geo X α α' i) ↔ Even i := by
  rw [isMVtx_geo X (by rw [dist_eq_four hb hc]; exact hi)]
  exact ⟨fun h => h.mp hc.1, fun h => ⟨fun _ => h, fun _ => hc.1⟩⟩

theorem isMVtx_geo_two' (hb : critDist X = 4) (hc : IsCritical X α α') :
    IsMVtx X (geo X α α' 2) :=
  (isMVtx_geo_crit hb hc (by omega)).mpr even_two

theorem not_isMVtx_geo_one (hb : critDist X = 4) (hc : IsCritical X α α') :
    ¬ IsMVtx X (geo X α α' 1) := by
  rw [isMVtx_geo_crit hb hc (by omega)]
  exact Nat.not_even_one

theorem not_isMVtx_geo_three (hb : critDist X = 4) (hc : IsCritical X α α') :
    ¬ IsMVtx X (geo X α α' 3) := by
  rw [isMVtx_geo_crit hb hc (by omega)]
  decide

end Path

section Contain

variable {α α' : Vtx X}

theorem zm_le_qv_geo (hb : critDist X = 4) (hc : IsCritical X α α') {i : ℕ} (hi : i ≤ 3) :
    ZM X α ≤ Qv X (geo X α α' i) :=
  zm_le_qv_of_dist_le_three hb hc.1 (by rw [dist_geo_crit hb hc (by omega)]; exact hi)

theorem zm_right_le_qv_geo (h : Hyp20 X) (hb : critDist X = 4) (hc : IsCritical X α α') {i : ℕ}
    (hi : 1 ≤ i) (hi4 : i ≤ 4) : ZM X α' ≤ Qv X (geo X α α' i) := by
  refine zm_le_qv_of_dist_le_three hb (hc.isMVtx_right X h) ?_
  rw [tdist_comm, dist_geo_crit_right hb hc hi4]
  omega

end Contain

end CFSG.Quasithin.MS93.S46
