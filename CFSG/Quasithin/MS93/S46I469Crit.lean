module

public import CFSG.Quasithin.MS93.S46I461

public section

namespace CFSG.Quasithin.MS93.S46

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.Fan86.Univ

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] {X : GoldAmalgam A C B}

theorem commute_of_dist_le_three (h : Hyp20 X) (hb4 : critDist X = 4) {γ ρ : Vtx X}
    (hγ : IsMVtx X γ) (hd : X.treeGraph.dist γ ρ ≤ 3) {x y : X.Universal} (hx : x ∈ ZM X γ)
    (hy : y ∈ Zv X ρ) : x * y = y * x := by
  have hxQ : x ∈ Qv X ρ := zm_le_qv_of_dist_le_three hb4 hγ hd hx
  by_cases hρ : IsMVtx X ρ
  · rw [zv_of_isMVtx X hρ] at hy
    exact (Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv X h hρ hy) x hxQ)
  · rw [zv_of_not_isMVtx X hρ] at hy
    exact (Subgroup.mem_centralizer_iff.mp (zh_le_centralizer X ρ hy) x hxQ)

theorem not_vv_le_qv_of_not_commute (h : Hyp20 X) (hb4 : critDist X = 4)
    (h43 : ∀ δ δ' : Vtx X, IsCritical X δ δ' → ¬ Vv X δ ≤ Qv X (geo X δ' δ 2))
    {α γ : Vtx X} (hγ : IsMVtx X γ) (hd : X.treeGraph.dist α γ = 2) {x w : X.Universal}
    (hx : x ∈ ZM X γ) (hw : w ∈ Vv X α) (hxw : x * w ≠ w * x) : ¬ Vv X γ ≤ Qv X α := by
  obtain ⟨ρ, hρ, y, hy, hxy⟩ : ∃ ρ : Vtx X, X.treeGraph.dist α ρ ≤ 2 ∧
      ∃ y ∈ Zv X ρ, x * y ≠ y * x := by
    by_contra! hall
    apply hxw
    have hle : Vv X α ≤ Subgroup.centralizer ({x} : Set X.Universal) := by
      refine iSup₂_le fun ρ hρ y hy => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff.mp hz]
      exact hall ρ hρ y hy
    exact Subgroup.mem_centralizer_iff.mp (hle hw) x (Set.mem_singleton x)
  have hγρ : 4 ≤ X.treeGraph.dist γ ρ := by
    by_contra hlt
    exact hxy (commute_of_dist_le_three h hb4 hγ (by omega) hx hy)
  have htri := dist_triangle X γ α ρ
  rw [tdist_comm X γ α, hd] at htri
  have h4 : X.treeGraph.dist γ ρ = 4 := by omega
  have hαρ : X.treeGraph.dist α ρ = 2 := by omega
  have hρM : IsMVtx X ρ := by
    have := (even_dist_iff X γ ρ).mp (by rw [h4]; decide)
    exact this.mp hγ
  have hZ : ¬ ZM X γ ≤ Qv X ρ := fun hle => by
    rw [zv_of_isMVtx X hρM] at hy
    exact hxy (Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv X h hρM hy) x (hle hx))
  have hc : IsCritical X γ ρ := ⟨hγ, by rw [h4, hb4], hZ⟩
  have hgeo : geo X ρ γ 2 = α := by
    rw [geo_rev_two hb4 hc]
    exact (eq_geo_of_dist X (by rw [tdist_comm]; exact hd) (by rw [tdist_comm X γ α, hd, hαρ,
      h4])).symm
  have := h43 γ ρ hc
  rwa [hgeo] at this

theorem exists_isCritical_of_not_vv_le_qv (h : Hyp20 X) (hC : CentHyp X)
    (hb4 : critDist X = 4) {α γ : Vtx X} (hγ : IsMVtx X γ) (hd : X.treeGraph.dist α γ = 2)
    (hVQ : ¬ Vv X γ ≤ Qv X α) :
    ∃ α' : Vtx X, IsCritical X α α' ∧ geo X α α' 2 = γ := by
  by_contra hno
  apply hVQ
  have hgen : critGen X α γ = ⊥ :=
    le_bot_iff.mp (iSup₂_le fun δ hδ => (hno ⟨δ, hδ⟩).elim)
  have := vv_le_critGen_sup h hC hb4 hγ hd
  rwa [hgen, bot_sup_eq] at this

theorem eq_geo_one_of_adj (hb4 : critDist X = 4) {α α' β : Vtx X} (hc : IsCritical X α α')
    (hαβ : X.treeGraph.Adj α β) (hβγ : X.treeGraph.Adj β (geo X α α' 2)) :
    geo X α α' 1 = β := by
  have h1 : X.treeGraph.Adj α (geo X α α' 1) := by
    have := adj_geo_crit hb4 hc (i := 0) (by omega)
    rwa [geo_zero] at this
  have h2 : X.treeGraph.Adj (geo X α α' 1) (geo X α α' 2) := adj_geo_crit hb4 hc (i := 1) (by omega)
  have hd : X.treeGraph.dist α (geo X α α' 2) = 2 := dist_geo_crit hb4 hc (by omega)
  have e1 := eq_geo_one X hαβ (by rw [dist_eq_one_of_adj X hβγ, hd])
  have e2 := eq_geo_one X h1 (by rw [dist_eq_one_of_adj X h2, hd])
  rw [e1, ← e2]

end CFSG.Quasithin.MS93.S46
