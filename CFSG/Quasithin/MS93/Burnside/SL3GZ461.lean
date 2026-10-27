module

public import CFSG.Quasithin.MS93.S34F461
public import CFSG.Quasithin.MS93.S38G2Step
public import CFSG.Quasithin.MS93.Burnside.SL3GRed

public section

namespace CFSG.Quasithin.MS93.S4L

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S34F
open scoped commutatorElement

section General

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B)

noncomputable abbrev burnsideSL3G_vb (α : Vtx X) : Subgroup X.Universal :=
  Vi X α (critDist X - 2)

variable {X}

theorem burnsideSL3G_vi_le_qv_self (h : Hyp20 X) {α : Vtx X} (hα : IsMVtx X α) {k : ℕ}
    (hk : k < critDist X) : Vi X α k ≤ Qv X α := by
  refine iSup₂_le fun ρ hρ => ?_
  have hρ' : X.treeGraph.dist α ρ ≤ k := hρ
  by_cases hρM : IsMVtx X ρ
  · rw [zv_of_isMVtx X hρM]
    exact zm_le_qv_of_dist_lt X hρM (by rw [tdist_comm]; omega)
  · rw [zv_of_not_isMVtx X hρM]
    have hne : ρ ≠ α := fun e => hρM (e ▸ hα)
    have hpos : 0 < X.treeGraph.dist ρ α := by
      rcases Nat.eq_zero_or_pos (X.treeGraph.dist ρ α) with h0 | h0
      · exact absurd ((dist_eq_zero_iff X).mp h0) hne
      · exact h0
    have hadj : X.treeGraph.Adj ρ (geo X ρ α 1) := adj_geo_one X hpos
    have hρ'M : IsMVtx X (geo X ρ α 1) := by
      have := isMVtx_iff_of_adj X hadj
      tauto
    have hd : X.treeGraph.dist (geo X ρ α 1) α < critDist X := by
      rw [dist_geo_right X (by omega), tdist_comm]
      omega
    exact (zh_le_zm X hadj.symm).trans (zm_le_qv_of_dist_lt X hρ'M hd)

theorem burnsideSL3G_centerOf_vi_le_qv (h : Hyp20 X) (hC : CentHyp X) {α : Vtx X}
    (hα : IsMVtx X α) {k : ℕ} (hk : k < critDist X) :
    ∀ (m : ℕ) (ρ : Vtx X), X.treeGraph.dist α ρ = m → m ≤ k →
      centerOf (Vi X α k) ≤ Qv X ρ := by
  intro m
  induction m with
  | zero =>
    intro ρ hρ _
    obtain rfl := (dist_eq_zero_iff X).mp hρ
    exact inf_le_left.trans (burnsideSL3G_vi_le_qv_self h hα hk)
  | succ m ih =>
    intro ρ hρ hmk
    have hpos : 0 < X.treeGraph.dist ρ α := by rw [tdist_comm, hρ]; omega
    have hadj : X.treeGraph.Adj ρ (geo X ρ α 1) := adj_geo_one X hpos
    have hdσ : X.treeGraph.dist α (geo X ρ α 1) = m := by
      rw [tdist_comm, dist_geo_right X (by omega), tdist_comm, hρ]
      omega
    have hσ := ih _ hdσ (by omega)
    by_cases hρM : IsMVtx X ρ
    · have hZ : ZM X ρ ≤ Vi X α k := by
        have := S38G.zv_le_vi' (X := X) (δ := α) (ρ := ρ) (i := k) (by omega)
        rwa [zv_of_isMVtx X hρM] at this
      have hle : centerOf (Vi X α k) ≤
          Qv X (geo X ρ α 1) ⊓ Subgroup.centralizer (ZM X ρ : Set X.Universal) :=
        le_inf hσ (inf_le_right.trans (Subgroup.centralizer_le hZ))
      rwa [hC ρ _ hρM hadj] at hle
    · have hσM : IsMVtx X (geo X ρ α 1) := by
        have := isMVtx_iff_of_adj X hadj
        tauto
      exact hσ.trans (qv_le_qv X h hσM hadj.symm)

theorem burnsideSL3G_centerOf_vb_le_qv_end (h : Hyp20 X) (hC : CentHyp X)
    (hb : 2 < critDist X) {α α' : Vtx X} (hc : IsCritical X α α') :
    centerOf (burnsideSL3G_vb X α) ≤ Qv X (geo X α' α 1) := by
  have hb0 : 0 < critDist X := by omega
  have hc' := ms22_iii X h hb0 hC hc
  have hd : X.treeGraph.dist α' α = critDist X := hc'.2.1
  have hγM : IsMVtx X (geo X α' α 2) := by
    rw [isMVtx_geo X (by omega)]
    exact ⟨fun _ => even_two, fun _ => hc'.1⟩
  have hdγ : X.treeGraph.dist α (geo X α' α 2) = critDist X - 2 := by
    rw [tdist_comm, dist_geo_right X (by omega), hd]
  have hN := burnsideSL3G_centerOf_vi_le_qv h hC hc.1 (k := critDist X - 2) (by omega) _ _ hdγ
    le_rfl
  have hadj : X.treeGraph.Adj (geo X α' α 2) (geo X α' α 1) :=
    (adj_geo X (i := 1) (by omega)).symm
  exact hN.trans (qv_le_qv X h hγM hadj)

theorem burnsideSL3G_vi_le_wStar {β δ : Vtx X} (hβδ : X.treeGraph.Adj β δ) (hδ : IsMVtx X δ)
    {k : ℕ} (hk : k + 1 < critDist X) : Vi X δ k ≤ burnsideSL3G_wStar X β := by
  refine iSup₂_le fun ρ hρ => ?_
  have hρ' : X.treeGraph.dist δ ρ ≤ k := hρ
  have htri := dist_triangle X β δ ρ
  rw [dist_eq_one_of_adj X hβδ] at htri
  by_cases hρM : IsMVtx X ρ
  · rw [zv_of_isMVtx X hρM]
    exact burnsideSL3G_zm_le_wStar hρM (by omega)
  · rw [zv_of_not_isMVtx X hρM]
    have hne : ρ ≠ δ := fun e => hρM (e ▸ hδ)
    have hpos : 0 < X.treeGraph.dist ρ δ := by
      rcases Nat.eq_zero_or_pos (X.treeGraph.dist ρ δ) with h0 | h0
      · exact absurd ((dist_eq_zero_iff X).mp h0) hne
      · exact h0
    have hadj : X.treeGraph.Adj ρ (geo X ρ δ 1) := adj_geo_one X hpos
    have hρ'M : IsMVtx X (geo X ρ δ 1) := by
      have := isMVtx_iff_of_adj X hadj
      tauto
    have hd1 : X.treeGraph.dist (geo X ρ δ 1) δ = X.treeGraph.dist ρ δ - 1 :=
      dist_geo_right X (by omega)
    have htri2 := dist_triangle X β δ (geo X ρ δ 1)
    rw [dist_eq_one_of_adj X hβδ, tdist_comm X δ, hd1, tdist_comm X ρ δ] at htri2
    exact (zh_le_zm X hadj.symm).trans (burnsideSL3G_zm_le_wStar hρ'M (by omega))

end General

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

section Center

variable (h : PUHyp M T L)
include h

theorem burnsideSL3G_stab_le_normalizer_centerOf_vi (α : Vtx (puAmalgam h.le)) (k : ℕ) :
    stab _ α ≤ Subgroup.normalizer (centerOf (Vi (puAmalgam h.le) α k) : Set _) := by
  refine le_normalizer_of_map_conj_le fun g hg => ?_
  rw [← PU.centerOf_map (MulAut.conj g).injective,
    map_conj_eq_of_mem_normalizer (S38G.stab_le_normalizer_vi α k hg)]

theorem burnsideSL3G_zm_le_centerOf_vi {α : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) {k : ℕ}
    (hk : k < critDist (puAmalgam h.le)) : ZM (puAmalgam h.le) α ≤ centerOf (Vi _ α k) := by
  have hZ : ZM (puAmalgam h.le) α ≤ Vi _ α k := by
    have := S38G.zv_le_vi' (X := puAmalgam h.le) (δ := α) (ρ := α) (i := k) (by simp)
    rwa [zv_of_isMVtx _ hα] at this
  exact le_inf hZ ((zm_le_centralizer_qv _ h.hyp20 hα).trans
    (Subgroup.centralizer_le (burnsideSL3G_vi_le_qv_self h.hyp20 hα hk)))

theorem burnsideSL3G_commutator_centerOf_zm_le (hb : 2 < critDist (puAmalgam h.le))
    {α α' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α α') :
    ⁅centerOf (burnsideSL3G_vb (puAmalgam h.le) α), ZM _ α'⁆ ≤
      Uloc h.le L α' ⊓ Subgroup.centralizer (ZM (puAmalgam h.le) α : Set _) := by
  have hb0 : 0 < critDist (puAmalgam h.le) := by omega
  have hc' := ms22_iii _ h.hyp20 hb0 h.centHyp hc
  have hα'ε := adj_geo_one_of_isCritical _ hb0 hc'
  have hNε := burnsideSL3G_centerOf_vb_le_qv_end h.hyp20 h.centHyp hb hc
  have hNs : centerOf (burnsideSL3G_vb (puAmalgam h.le) α) ≤ stab _ α' :=
    hNε.trans (qv_le_stab_of_adj _ hα'ε.symm)
  refine le_inf ?_ ?_
  · rw [Subgroup.commutator_comm, commutator_zm_eq_commutator_uloc_of_le_qv h hc'.1 hα'ε hNε]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      (hNs.trans (stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) α'))
  · have h1 : ⁅centerOf (burnsideSL3G_vb (puAmalgam h.le) α), ZM _ α'⁆ ≤
        centerOf (burnsideSL3G_vb (puAmalgam h.le) α) :=
      Subgroup.le_normalizer_iff_commutator_le_left.mp
        ((zm_le_stab_of_isCritical _ h.hyp20 hb0 hc).trans
          (burnsideSL3G_stab_le_normalizer_centerOf_vi h α _))
    exact h1.trans (inf_le_right.trans (Subgroup.centralizer_le
      ((burnsideSL3G_zm_le_centerOf_vi h hc.1 (by omega)).trans inf_le_left)))

theorem burnsideSL3G_centerOf_ltil_le_of_commutator_le (hb : 2 < critDist (puAmalgam h.le))
    {α α' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α α')
    (hN : ⁅centerOf (burnsideSL3G_vb (puAmalgam h.le) α), ZM _ α'⁆ ≤ ZM _ α) :
    ⁅centerOf (burnsideSL3G_vb (puAmalgam h.le) α), Ltil h.le L α⁆ ≤ ZM _ α := by
  have hb0 : 0 < critDist (puAmalgam h.le) := by omega
  have hβ := adj_geo_one_of_isCritical _ hb0 hc
  have hc' := ms22_iii _ h.hyp20 hb0 h.centHyp hc
  exact commutator_ltil_le_of_commutator_le_gen h hc.1 hβ
    (burnsideSL3G_stab_le_normalizer_centerOf_vi h α _) (stab_le_normalizer_zm _ α) hN
    (zm_le_qv_geo_one _ h.hyp20 hb0 hc) hc'.2.2

end Center

section Flat

variable (h : PUHyp M T L) (hU : IsSL3U M T L)
include hU

theorem burnsideSL3G_centerOf_vb_le_flat (hb : 2 < critDist (puAmalgam h.le))
    {α α' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α α') :
    centerOf (burnsideSL3G_vb (puAmalgam h.le) α) ≤ Qv _ (geo _ α' α 1) ⊓ flat h α' := by
  have hNε := burnsideSL3G_centerOf_vb_le_qv_end h.hyp20 h.centHyp hb hc
  have hNR : centerOf (burnsideSL3G_vb (puAmalgam h.le) α) ≤
      Subgroup.centralizer (critR (puAmalgam h.le) α α' : Set _) :=
    inf_le_right.trans (Subgroup.centralizer_le
      (((critR_eq_commutator_uloc_right h h.centHyp hc).2.trans inf_le_right).trans
        ((burnsideSL3G_zm_le_centerOf_vi h hc.1 (by omega)).trans inf_le_left)))
  exact le_inf hNε ((le_inf hNε hNR).trans (qv_inf_centralizer_critR_le_flat h hU hc))

theorem burnsideSL3G_centerOf_ltil_le_of_ne (hb : 2 < critDist (puAmalgam h.le))
    {α α' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α α')
    (hne : (Qv (puAmalgam h.le) α').relIndex (ZM (puAmalgam h.le) α) ≠
      Nat.card ↥(critR (puAmalgam h.le) α α')) :
    ⁅centerOf (burnsideSL3G_vb (puAmalgam h.le) α), Ltil h.le L α⁆ ≤ ZM _ α := by
  refine burnsideSL3G_centerOf_ltil_le_of_commutator_le h hb hc ?_
  refine (burnsideSL3G_commutator_centerOf_zm_le h hb hc).trans ?_
  rw [uloc_inf_centralizer_eq_critR_flat h hU h.centHyp hc hne]
  exact ((critR_eq_commutator_uloc_right h h.centHyp hc).2).trans inf_le_right

end Flat

theorem burnsideSL3G_uloc_inf_centralizer_le_centerOf (h : PUHyp M T L)
    (hb : 4 < critDist (puAmalgam h.le)) {β α δ : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hαβ : (puAmalgam h.le).treeGraph.Adj α β) (hβδ : (puAmalgam h.le).treeGraph.Adj β δ)
    (hδ : IsMVtx _ δ) :
    Uloc h.le L α ⊓ Subgroup.centralizer
        (burnsideSL3G_wStar (puAmalgam h.le) β : Set (puAmalgam h.le).Universal) ≤
      centerOf (burnsideSL3G_vb (puAmalgam h.le) δ) := by
  have hd : (puAmalgam h.le).treeGraph.dist δ α ≤ critDist (puAmalgam h.le) - 2 := by
    have htri := dist_triangle (puAmalgam h.le) δ β α
    rw [tdist_comm _ δ β, dist_eq_one_of_adj _ hβδ, dist_eq_one_of_adj _ hαβ.symm] at htri
    omega
  have hZV : ZM (puAmalgam h.le) α ≤ burnsideSL3G_vb (puAmalgam h.le) δ := by
    have := S38G.zv_le_vi' (X := puAmalgam h.le) (δ := δ) (ρ := α)
      (i := critDist (puAmalgam h.le) - 2) hd
    rwa [zv_of_isMVtx _ hα] at this
  have hVW : burnsideSL3G_vb (puAmalgam h.le) δ ≤ burnsideSL3G_wStar (puAmalgam h.le) β :=
    burnsideSL3G_vi_le_wStar hβδ hδ (by omega)
  exact le_inf (inf_le_left.trans ((S34F.uloc_le_zm' h hα).trans hZV))
    (inf_le_right.trans (Subgroup.centralizer_le hVW))

end CFSG.Quasithin.MS93.S4L
