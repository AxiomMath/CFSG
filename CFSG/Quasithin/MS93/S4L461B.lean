module

public import CFSG.Quasithin.MS93.S4L461A
public import CFSG.Quasithin.MS93.S34F39
public import CFSG.Quasithin.MS93.S34GE

public section

namespace CFSG.Quasithin.MS93.S4L

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

section Offender

variable (h : PUHyp M T L) (hU : IsSL3U M T L) (hC : CentHyp (puAmalgam h.le))
include h hU hC

theorem commutator_critGen_le_flat (hb4 : critDist (puAmalgam h.le) = 4)
    {α γ : Vtx (puAmalgam h.le)} (hγ : IsMVtx _ γ)
    (hd : (puAmalgam h.le).treeGraph.dist α γ = 2)
    (hN : ¬ centerOf (Vv (puAmalgam h.le) α) ≤ Bloc h.le L α) :
    ⁅Vv (puAmalgam h.le) α ⊓ Qv _ γ, critGen _ α γ⁆ ≤ centerOf (Vv _ α) := by
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  set β := geo (puAmalgam h.le) α γ 1
  have hαβ : (puAmalgam h.le).treeGraph.Adj α β := adj_geo_one _ (by omega)
  have hβγ : (puAmalgam h.le).treeGraph.Adj β γ := by
    have := adj_geo (puAmalgam h.le) (u := α) (w := γ) (i := 1) (by omega)
    rwa [geo_of_le _ (by omega : (puAmalgam h.le).treeGraph.dist α γ ≤ 1 + 1)] at this
  have hWs : critGen (puAmalgam h.le) α γ ≤ stab _ α :=
    (critGen_le_vv hb4 α γ).trans ((vv_le_qv h hb hγ).trans
      ((qv_le_qv _ h.hyp20 hγ hβγ.symm).trans (qv_le_stab_of_adj _ hαβ.symm)))
  rw [Subgroup.commutator_comm, critGen, iSup_subtype']
  refine commutator_iSup_le_of (fun δ => ?_) ?_
  · obtain ⟨δ, hc, hgeo⟩ := δ
    rw [Subgroup.commutator_comm]
    have := S34F.commutator_vv_inf_qv_le_centerOf_flat h hU hC hb4 hc hN
    rwa [hgeo] at this
  · rw [← iSup_subtype' (f := fun δ (_ : δ ∈ {δ : Vtx (puAmalgam h.le) |
      IsCritical (puAmalgam h.le) α δ ∧ geo (puAmalgam h.le) α δ 2 = γ}) =>
        ZM (puAmalgam h.le) δ), ← critGen]
    exact hWs.trans (S34F.stab_le_normalizer_centerOf h α)

theorem exists_offender_centerOf_flat (h43 : S34G.S43b4Flat)
    (hb4 : critDist (puAmalgam h.le) = 4) {α α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) α α')
    (hNα : ¬ centerOf (Vv (puAmalgam h.le) α) ≤ Bloc h.le L α)
    (hNγ : ¬ centerOf (Vv (puAmalgam h.le) (geo _ α α' 2)) ≤ Bloc h.le L (geo _ α α' 2)) :
    (∃ As, As ≤ S34F.flat h α ∧ IsOffenderOn (puAmalgam h.le) α (centerOf (Vv _ α)) As) ∨
      (∃ As, As ≤ S34F.flat h (geo _ α α' 2) ∧ IsOffenderOn (puAmalgam h.le) (geo _ α α' 2)
        (centerOf (Vv _ (geo _ α α' 2))) As) := by
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  have hb0 : 0 < critDist (puAmalgam h.le) := by omega
  have h20 := h.hyp20
  set γ := geo (puAmalgam h.le) α α' 2 with hγdef
  set β := geo (puAmalgam h.le) α α' 1 with hβdef
  have hγ : IsMVtx _ γ := isMVtx_geo_two' hb4 hc
  have hd : (puAmalgam h.le).treeGraph.dist α γ = 2 := dist_geo_crit hb4 hc (by omega)
  have hd' : (puAmalgam h.le).treeGraph.dist γ α = 2 := by rw [tdist_comm]; exact hd
  have hαβ : (puAmalgam h.le).treeGraph.Adj α β := adj_geo_one_of_isCritical _ hb0 hc
  have hβγ : (puAmalgam h.le).treeGraph.Adj β γ := adj_geo_crit hb4 hc (i := 1) (by omega)
  have hVαγ : ¬ Vv (puAmalgam h.le) α ≤ Qv _ γ := fun hle =>
    h43 G M T L h hU hC hb4 α α' ⟨hc, by rw [geo_rev_two hb4 hc]; exact hle⟩
  have hW₂ : ¬ critGen (puAmalgam h.le) γ α ≤ Qv _ γ := fun hle =>
    hVαγ ((vv_le_critGen_sup h20 hC hb4 hc.1 hd').trans (sup_le hle le_rfl))
  obtain ⟨μ, hcμ, hgeoμ⟩ : ∃ μ, IsCritical (puAmalgam h.le) γ μ ∧
      geo (puAmalgam h.le) γ μ 2 = α := by
    by_contra hno
    apply hW₂
    refine iSup₂_le fun δ hδ => (hno ⟨δ, hδ⟩).elim
  have hVγα : ¬ Vv (puAmalgam h.le) γ ≤ Qv _ α := fun hle =>
    h43 G M T L h hU hC hb4 γ μ ⟨hcμ, by rw [geo_rev_two hb4 hcμ, hgeoμ]; exact hle⟩
  have hW₁ : ¬ critGen (puAmalgam h.le) α γ ≤ Qv _ α := fun hle =>
    hVγα ((vv_le_critGen_sup h20 hC hb4 hγ hd).trans (sup_le hle le_rfl))
  have h39γ := S34F.s39_flat h hU hC hb4 hγ
  have h39α := S34F.s39_flat h hU hC hb4 hc.1
  have hsqγ : ∀ a ∈ Vv (puAmalgam h.le) γ, a ^ 2 ∈ Qv _ α := fun a ha =>
    centerOf_vv_le_qv h20 hC hb hγ hc.1 hd' (h39γ (sq_mem_commutator_vv h hb0 ha))
  have hcomγ : ∀ a ∈ Vv (puAmalgam h.le) γ, ∀ b ∈ Vv (puAmalgam h.le) γ, ⁅a, b⁆ ∈ Qv _ α :=
    fun a ha b hb' => centerOf_vv_le_qv h20 hC hb hγ hc.1 hd'
      (h39γ (Subgroup.commutator_mem_commutator ha hb'))
  have hsqα : ∀ a ∈ Vv (puAmalgam h.le) α, a ^ 2 ∈ Qv _ γ := fun a ha =>
    centerOf_vv_le_qv h20 hC hb hc.1 hγ hd (h39α (sq_mem_commutator_vv h hb0 ha))
  have hcomα : ∀ a ∈ Vv (puAmalgam h.le) α, ∀ b ∈ Vv (puAmalgam h.le) α, ⁅a, b⁆ ∈ Qv _ γ :=
    fun a ha b hb' => centerOf_vv_le_qv h20 hC hb hc.1 hγ hd
      (h39α (Subgroup.commutator_mem_commutator ha hb'))
  have hfinα := finite_stab h hc.1
  have hfinγ := finite_stab h hγ
  have hβs : Qv (puAmalgam h.le) β ≤ stab _ α := qv_le_stab_of_adj _ hαβ.symm
  have hβs' : Qv (puAmalgam h.le) β ≤ stab _ γ := qv_le_stab_of_adj _ hβγ
  have hVγβ : Vv (puAmalgam h.le) γ ≤ Qv _ β :=
    (vv_le_qv h hb hγ).trans (qv_le_qv _ h20 hγ hβγ.symm)
  have hVαβ : Vv (puAmalgam h.le) α ≤ Qv _ β :=
    (vv_le_qv h hb hc.1).trans (qv_le_qv _ h20 hc.1 hαβ)
  have hb1 : (Qv (puAmalgam h.le) α).relIndex (Vv _ γ) ≤
      (Qv (puAmalgam h.le) α).relIndex (critGen _ α γ) :=
    relIndex_le_of_le_sup (S := stab _ α) (hVγβ.trans hβs)
      (((critGen_le_vv hb4 α γ).trans hVγβ).trans hβs) (qv_le_stab _ α)
      (stab_le_normalizer_qv _ α) (vv_le_critGen_sup h20 hC hb4 hγ hd)
  have ha1 : (Qv (puAmalgam h.le) γ).relIndex (Vv _ α) ≤
      (Qv (puAmalgam h.le) γ).relIndex (critGen _ γ α) :=
    relIndex_le_of_le_sup (S := stab _ γ) (hVαβ.trans hβs')
      (((critGen_le_vv hb4 γ α).trans hVαβ).trans hβs') (qv_le_stab _ γ)
      (stab_le_normalizer_qv _ γ) (vv_le_critGen_sup h20 hC hb4 hc.1 hd')
  by_cases hab : (Qv (puAmalgam h.le) γ).relIndex (Vv _ α) ≤
      (Qv (puAmalgam h.le) α).relIndex (Vv _ γ)
  · left
    refine ⟨critGen _ α γ, critGen_le_flat h hU hC α γ,
      ⟨β, hαβ, (critGen_le_vv hb4 α γ).trans hVγβ⟩, hW₁,
      fun a ha => hsqγ a (critGen_le_vv hb4 α γ ha),
      fun a ha b hb' => hcomγ a (critGen_le_vv hb4 α γ ha) b (critGen_le_vv hb4 α γ hb'),
      Vv _ α ⊓ Qv _ γ, le_inf inf_le_left (centerOf_vv_le_qv h20 hC hb hc.1 hγ hd),
      inf_le_left, commutator_critGen_le_flat h hU hC hb4 hγ hd hNα, ?_⟩
    rw [Subgroup.inf_relIndex_left]
    exact hab.trans hb1
  · right
    refine ⟨critGen _ γ α, critGen_le_flat h hU hC γ α,
      ⟨β, hβγ.symm, (critGen_le_vv hb4 γ α).trans hVαβ⟩, hW₂,
      fun a ha => hsqα a (critGen_le_vv hb4 γ α ha),
      fun a ha b hb' => hcomα a (critGen_le_vv hb4 γ α ha) b (critGen_le_vv hb4 γ α hb'),
      Vv _ γ ⊓ Qv _ α, le_inf inf_le_left (centerOf_vv_le_qv h20 hC hb hγ hc.1 hd'),
      inf_le_left, commutator_critGen_le_flat h hU hC hb4 hc.1 hd' hNγ, ?_⟩
    rw [Subgroup.inf_relIndex_left]
    exact (le_of_lt (not_le.mp hab)).trans ha1

end Offender

end CFSG.Quasithin.MS93.S4L
