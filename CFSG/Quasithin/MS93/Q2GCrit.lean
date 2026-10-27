module

public import CFSG.Quasithin.MS93.S38EInst

public section

namespace CFSG.Quasithin.MS93.Q2G

open CFSG.Quasithin CFSG.Quasithin.Fan86.Univ CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.S38E
  SimpleGraph
open scoped commutatorElement

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] {X : GoldAmalgam A C B}

@[expose] def CritUniq (X : GoldAmalgam A C B) : Prop :=
  ∀ γ γ' δ' : Vtx X, IsCritical X γ γ' → IsCritical X γ δ' → geo X γ δ' 1 = geo X γ γ' 1 →
    XM X γ' ⊔ Qv X γ = XM X δ' ⊔ Qv X γ

section Crit

variable (h : Hyp20 X) (hb : 0 < critDist X) (hC : CentHyp X)
include h hb hC

theorem commutator_xm_eq_of_critUniq (hU : CritUniq X) {α α' δ' : Vtx X}
    (hc : IsCritical X α α') (hd : IsCritical X α δ') (hgeo : geo X α δ' 1 = geo X α α' 1) :
    ⁅XM X α, XM X α'⁆ = ⁅XM X α, XM X δ'⁆ := by
  have hn : ∀ {δ : Vtx X}, IsCritical X α δ →
      XM X δ ≤ Subgroup.normalizer (XM X α : Set X.Universal) := fun hδ =>
    (xm_le_qv_geo_one X h hb hC hδ).trans ((qv_le_stab_of_adj X
      (adj_geo_one_of_isCritical X hb hδ).symm).trans (stab_le_normalizer_xm X α))
  rw [← commutator_sup_eq_of_le_centralizer (hn hc) (qv_le_centralizer_xm X α),
    ← commutator_sup_eq_of_le_centralizer (hn hd) (qv_le_centralizer_xm X α),
    hU α α' δ' hc hd hgeo]

theorem normalizer_commutator_xm_of_critUniq (hU : CritUniq X) {α α' : Vtx X}
    (hc : IsCritical X α α') :
    Qv X (geo X α α' 1) ≤ Subgroup.normalizer ((⁅XM X α, XM X α'⁆ : Subgroup X.Universal) :
      Set X.Universal) := by
  intro t ht
  have hαβ : X.treeGraph.Adj α (geo X α α' 1) := adj_geo_one_of_isCritical X hb hc
  have htα : t • α = α := (mem_stab X).mp (qv_le_stab_of_adj X hαβ.symm ht)
  have htβ : t • geo X α α' 1 = geo X α α' 1 := (mem_stab X).mp (qv_le_stab X _ ht)
  have hct : IsCritical X α (t • α') := by
    have := (isCritical_smul X t α α').mpr hc
    rwa [htα] at this
  have hgeo : geo X α (t • α') 1 = geo X α α' 1 := by
    conv_lhs => rw [← htα]
    rw [geo_smul, htβ]
  refine mem_normalizer_of_map_conj_eq ?_
  rw [Subgroup.map_commutator, ← xm_smul, ← xm_smul, htα]
  exact (commutator_xm_eq_of_critUniq h hb hC hU hc hct hgeo).symm

theorem ms23_of_critUniq (ha : 2 < critDist X)
    (hG : ∀ γ ρ : Vtx X, IsMVtx X γ → X.treeGraph.Adj γ ρ → Gen23At X γ ρ)
    (hU : CritUniq X) (hZ : ∀ γ γ' : Vtx X, IsCritical X γ γ' → ∃ Z, Zc23At X γ γ' Z)
    (hN : ∀ ε ε' : Vtx X, IsCritical X ε ε' →
      ¬ stab X ε ≤ Subgroup.normalizer ((⁅XM X ε, XM X ε'⁆ : Subgroup X.Universal) :
        Set X.Universal)) :
    critDist X = 4 ∧ StarNorm X := by
  have key : ∀ ε ε' : Vtx X, IsCritical X ε ε' → critDist X = 4 ∧
      stab X (geo X ε ε' 2) ≤ Subgroup.normalizer ((⁅XM X ε, XM X ε'⁆ : Subgroup X.Universal) :
        Set X.Universal) := by
    intro ε ε' hc
    have hεβ := adj_geo_one_of_isCritical X hb hc
    have := ms23 X h hc.1 hεβ ha (hG _ _ hc.1 hεβ) (fun α' hc' _ => hZ ε α' hc')
      (normalizer_commutator_xm_of_critUniq h hb hC hU hc) (hN ε ε' hc)
      (fun δ' hd hgeo => (commutator_xm_eq_of_critUniq h hb hC hU hc hd hgeo).le)
    exact ⟨this.1, this.2 ε' hc rfl⟩
  obtain ⟨α, α', hc⟩ := exists_isCritical X h
  exact ⟨(key α α' hc).1, fun ε ε' hc => (key ε ε' hc).2⟩

end Crit

theorem vv_le_xm_sup_of_critUniq (h : Hyp20 X) (hb : critDist X = 4) (hC : CentHyp X)
    (hU : CritUniq X) {μ β α μ' : Vtx X} (hμ : IsMVtx X μ) (hμβ : X.treeGraph.Adj μ β)
    (hβα : X.treeGraph.Adj β α) (hne : α ≠ μ) (hcμ : IsCritical X μ μ')
    (hgμ : geo X μ μ' 1 = β) : Vv X α ≤ XM X μ' ⊔ Qv X μ := by
  have hb0 : 0 < critDist X := by omega
  have hdαμ : X.treeGraph.dist α μ = 2 := dist_eq_two_of_adj_adj X hβα.symm hμβ.symm hne
  have hα : IsMVtx X α := by
    have h1 := isMVtx_iff_of_adj X hμβ
    have h2 := isMVtx_iff_of_adj X hβα
    tauto
  refine iSup₂_le fun ρ hρ => ?_
  obtain ⟨γ, hγ, hdγ, hle⟩ := exists_zv_le_zm X hα hρ
  refine hle.trans ?_
  by_cases hγμ : ZM X γ ≤ Qv X μ
  · exact hγμ.trans le_sup_right
  have hd4 : X.treeGraph.dist γ μ = 4 := by
    have h1 : 4 ≤ X.treeGraph.dist γ μ := by
      by_contra hlt
      exact hγμ (zm_le_qv_of_dist_lt X hγ (by omega))
    have h2 := dist_triangle X γ α μ
    rw [tdist_comm X γ α] at h2
    omega
  have hc : IsCritical X γ μ := ⟨hγ, by rw [hd4, hb], hγμ⟩
  have hc' := ms22_iii X h hb0 hC hc
  have hgeo : geo X μ γ 1 = β := by
    symm
    refine eq_geo_one X hμβ ?_
    have h1 := dist_triangle X β α γ
    rw [dist_eq_one_of_adj X hβα] at h1
    have h2 := dist_triangle X μ β γ
    have h3 : X.treeGraph.dist μ γ = 4 := by rw [tdist_comm]; exact hd4
    rw [dist_eq_one_of_adj X hμβ, h3] at h2
    rw [h3]
    omega
  rw [← hU μ γ μ' hc' hcμ (hgμ.trans hgeo.symm)]
  exact (zm_le_xm X h hb0 hγ).trans le_sup_left

theorem endSetup_of_critUniq (h : Hyp20 X) (hb : critDist X = 4) (hC : CentHyp X)
    (hN : StarNorm X) {Lt : Vtx X → Subgroup X.Universal} (hL : StarCent X Lt)
    (hU : CritUniq X)
    (h8 : ∀ ε ε' : Vtx X, IsCritical X ε ε' → ¬ Vv X ε ≤ Qv X (geo X ε' ε 2))
    {α α' : Vtx X} (hc : IsCritical X α α')
    (hff : ⁅Vv X α ⊓ Qv X (geo X α α' 2), XM X α'⁆ ≤
      Subgroup.centralizer (Vv X α : Set X.Universal))
    (hfin : Finite ↥(stab X α)) (hLt_le : Lt α ≤ stab X α)
    (hnLt : stab X α ≤ Subgroup.normalizer (Lt α : Set X.Universal))
    (hperf : ⁅Lt α, Lt α⁆ = Lt α) (hLt : stab X α = Lt α ⊔ Qv X (geo X α α' 1))
    (hfaith : ∀ x ∈ XM X α', x ∉ Qv X α →
      Lt α ≤ Subgroup.closure {y | ∃ k ∈ stab X α, k * x * k⁻¹ = y}) :
    EndSetup (Vv X α) (stab X α) (Lt α) (Qv X (geo X α α' 1)) (Qv X α) (XM X α')
      ((Qv X α).relIndex (XM X α')) := by
  have hb0 : 0 < critDist X := by omega
  have hd : X.treeGraph.dist α α' = 4 := hc.2.1.trans hb
  set β := geo X α α' 1 with hβ
  set μ := geo X α α' 2 with hμdef
  have hαβ : X.treeGraph.Adj α β := adj_geo_one_of_isCritical X hb0 hc
  have hβμ : X.treeGraph.Adj β μ := adj_geo X (i := 1) (by omega)
  have hμ : IsMVtx X μ := isMVtx_geo_two X h hb0 hc
  have hαμ : X.treeGraph.dist α μ = 2 := dist_geo X (by omega)
  have hne : α ≠ μ := fun he => by rw [← he] at hαμ; simp at hαμ
  have hVQ : Vv X α ≤ Qv X α := vv_le_qv X (by omega) hc.1
  have hcomm : ⁅Vv X α, Vv X α⁆ ≤ Subgroup.centralizer (Vv X α : Set X.Universal) :=
    commutator_vv_le_centralizer X h hb hC hN hc.1
  have hltC : Lt α ≤ Subgroup.centralizer ((⁅Vv X α, Vv X α⁆ : Subgroup X.Universal) :
      Set X.Universal) :=
    Subgroup.le_centralizer_iff.mp
      ((commutator_vv_le_nA X h hb hN hc.1).trans (nA_le_centralizer_lt X hL α))
  have hXβ : XM X α' ≤ Qv X β := xm_le_qv_geo_one X h hb0 hC hc
  refine
    { finite := hfin
      v_le := hVQ.trans (qv_le_stab X α)
      nV := stab_le_normalizer_of_smul X (F := fun ρ => Vi X ρ 2) (fun g ρ => vi_smul X g ρ 2) α
      invol := ?_
      cls2 := hcomm
      lt_le := hLt_le
      nLt := hnLt
      perf := hperf
      tb_le := qv_le_stab_of_adj X hαβ.symm
      sup := hLt
      ltC := hltC
      key := ?_
      e_le := hXβ.trans (qv_le_stab_of_adj X hαβ.symm)
      e_ab := isElemAbelian_xm X α'
      ff := ?_
      e_eq := rfl
      qa_le := qv_le_stab X α
      nQa := stab_le_normalizer_qv X α
      qa2 := (isPGroup_qv X h ((isMVtx_iff_of_adj X hαβ).mp hc.1)).to_le
        (qv_le_qv X h hc.1 hαβ)
      faith := hfaith }
  ·
    refine le_antisymm (iSup₂_le fun ρ hρ => ?_)
      (Subgroup.closure_le _ |>.mpr fun v hv => hv.1)
    intro z hz
    refine Subgroup.subset_closure ⟨?_, ?_⟩
    · exact le_iSup₂_of_le (f := fun ρ (_ : ρ ∈ {ρ : Vtx X | X.treeGraph.dist α ρ ≤ 2}) =>
        Zv X ρ) ρ hρ le_rfl hz
    · by_cases hρM : IsMVtx X ρ
      · rw [zv_of_isMVtx X hρM] at hz
        exact (isElemAbelian_xm X ρ).2 z (zm_le_xm X h hb0 hρM hz)
      · rw [zv_of_not_isMVtx X hρM] at hz
        exact (isElemAbelian_xm X ρ).2 z hz
  ·
    intro hle
    have hbot := commutator_vv_eq_bot_of_le X h hb hC hN hc.1 hαβ hLt hltC hle
    refine commutator_vv_ne_bot X h hb hC hc ?_ hbot
    have h1 := h8 α α' hc
    have e : geo X α' α 2 = μ := by
      have := geo_symm X (u := α) (w := α') (i := 2) (by omega)
      rwa [hd] at this
    rwa [e] at h1
  ·
    obtain ⟨g, hg, hgα⟩ := exists_mem_stab_smul X hαβ.symm hβμ
    have hgβ : g • β = β := (mem_stab X).mp hg
    have hcg : IsCritical X μ (g • α') := by
      rw [← hgα]
      exact (isCritical_smul X g α α').mpr hc
    have hgeog : geo X μ (g • α') 1 = β := by
      rw [← hgα, geo_smul, ← hβ, hgβ]
    have hVF := vv_le_xm_sup_of_critUniq h hb hC hU hμ hβμ.symm hαβ.symm hne hcg hgeog
    rw [xm_smul] at hVF
    have hfinX : Finite ↥(XM X α') :=
      Finite.of_injective _ (Subgroup.inclusion_injective
        (hXβ.trans (qv_le_stab_of_adj X hαβ.symm)))
    have hfinF : Finite ↥((XM X α').map (MulAut.conj g).toMonoidHom) :=
      Finite.of_equiv _ (Subgroup.equivMapOfInjective _ _ (MulAut.conj g).injective).toEquiv
    have hFβ : (XM X α').map (MulAut.conj g).toMonoidHom ≤ Qv X β := by
      have := xm_le_qv_geo_one X h hb0 hC hcg
      rwa [hgeog, xm_smul] at this
    have hFn : (XM X α').map (MulAut.conj g).toMonoidHom ≤
        Subgroup.normalizer (Qv X μ : Set X.Universal) :=
      hFβ.trans ((qv_le_stab_of_adj X hβμ).trans (stab_le_normalizer_qv X μ))
    refine ⟨Vv X α ⊓ Qv X μ, inf_le_left, ?_, hff⟩
    rw [inf_comm, Subgroup.inf_relIndex_right]
    have h1 : (Qv X μ).relIndex ((XM X α').map (MulAut.conj g).toMonoidHom ⊔ Qv X μ) =
        (Qv X α).relIndex (XM X α') := by
      rw [relIndex_sup_of_le_normalizer hFn, ← hgα, qv_smul,
        Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
    rw [← h1]
    refine Subgroup.relIndex_le_of_le_right hVF ?_
    rw [h1]
    unfold Subgroup.relIndex
    exact Subgroup.index_ne_zero_of_finite

end CFSG.Quasithin.MS93.Q2G
