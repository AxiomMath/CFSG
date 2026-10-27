module

public import CFSG.Quasithin.MS93.S38EFF
public import CFSG.Quasithin.MS93.S38EIrr

public section

namespace CFSG.Quasithin.MS93.S38E

open CFSG.Quasithin CFSG.Quasithin.Fan86.Univ CFSG.Quasithin.MS93 SimpleGraph
open scoped commutatorElement

section General

variable {Γ : Type*} [Group Γ]

theorem relIndex_sup_of_le_normalizer {H K : Subgroup Γ}
    (hH : H ≤ Subgroup.normalizer (K : Set Γ)) : K.relIndex (H ⊔ K) = K.relIndex H := by
  set P := Subgroup.normalizer (K : Set Γ)
  have hK : K ≤ P := Subgroup.le_normalizer
  have : (K.subgroupOf P).Normal := Subgroup.normal_in_normalizer
  rw [← Subgroup.relIndex_subgroupOf (sup_le hH hK), ← Subgroup.relIndex_subgroupOf hH,
    Subgroup.subgroupOf_sup hH hK, Subgroup.relIndex_sup_right]

end General

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] {X : GoldAmalgam A C B}

theorem endSetup_of (h : Hyp20 X) (hb : critDist X = 4) (hC : CentHyp X) (hN : StarNorm X)
    {Lt : Vtx X → Subgroup X.Universal} (hL : StarCent X Lt)
    (hO : ∀ γ ρ : Vtx X, IsMVtx X γ → X.treeGraph.Adj γ ρ → OffDataAt X γ ρ)
    (hOC : ∀ γ ρ : Vtx X, IsMVtx X γ → X.treeGraph.Adj γ ρ → OffCentAt X γ ρ)
    (h8 : ∀ ε ε' : Vtx X, IsCritical X ε ε' → ¬ Vv X ε ≤ Qv X (geo X ε' ε 2))
    {α α' : Vtx X} (hc : IsCritical X α α')
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
  have hβM : ¬ IsMVtx X β := (isMVtx_iff_of_adj X hαβ).mp hc.1
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
  have hc' := ms22_iii X h hb0 hC hc
  have hα'γ : X.treeGraph.Adj α' (geo X α' α 1) := adj_geo_one_of_isCritical X hb0 hc'
  have hoff := (isOffAt_xm h hb0 hC hc (hO _ _ hc.1 hαβ) (hO _ _ hc'.1 hα'γ)).1
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
      qa2 := (isPGroup_qv X h hβM).to_le (qv_le_qv X h hc.1 hαβ)
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
    have hF : IsOffAt X μ β ((XM X α').map (MulAut.conj g).toMonoidHom) := by
      have := isOffAt_smul X hoff g
      rwa [hgα, hgβ] at this
    have hVF := vv_le_offender_sup X h hb hC hO hμ hβμ.symm hαβ.symm hne hF
    have hfinX : Finite ↥(XM X α') :=
      Finite.of_injective _ (Subgroup.inclusion_injective
        (hXβ.trans (qv_le_stab_of_adj X hαβ.symm)))
    have hfinF : Finite ↥((XM X α').map (MulAut.conj g).toMonoidHom) :=
      Finite.of_equiv _ (Subgroup.equivMapOfInjective _ _ (MulAut.conj g).injective).toEquiv
    have hFn : (XM X α').map (MulAut.conj g).toMonoidHom ≤
        Subgroup.normalizer (Qv X μ : Set X.Universal) :=
      hF.1.trans ((qv_le_stab_of_adj X hβμ).trans (stab_le_normalizer_qv X μ))
    refine ⟨Vv X α ⊓ Qv X μ, inf_le_left, ?_, ?_⟩
    · rw [inf_comm, Subgroup.inf_relIndex_right]
      have h1 : (Qv X μ).relIndex ((XM X α').map (MulAut.conj g).toMonoidHom ⊔ Qv X μ) =
          (Qv X α).relIndex (XM X α') := by
        rw [relIndex_sup_of_le_normalizer hFn, ← hgα, qv_smul,
          Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
      rw [← h1]
      refine Subgroup.relIndex_le_of_le_right hVF ?_
      rw [h1]
      unfold Subgroup.relIndex
      exact Subgroup.index_ne_zero_of_finite
    · refine (commutator_vv_inf_qv_le X h hb hC hc (hO _ _ hc.1 hαβ) (hO _ _ hc'.1 hα'γ)
        (hOC _ _ hc'.1 hα'γ)).trans ((commutator_xm_le_left X h hb0 hC hc).trans ?_)
      exact (xm_le_centralizer X α).trans (Subgroup.centralizer_le hVQ)

end CFSG.Quasithin.MS93.S38E
