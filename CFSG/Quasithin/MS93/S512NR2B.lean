module

public import CFSG.Quasithin.MS93.S512NR2A
public import CFSG.Quasithin.MS93.S512NV

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

namespace S512N

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

namespace Cfg

variable {h : PUHyp M T L} {δ μ₁ μ₂ : Vtx (puAmalgam h.le)} (hc : Cfg h k δ μ₁ μ₂)
include hc

theorem nclStab_le_stab_δ :
    S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ μ₁) ≤ stab _ δ :=
  hc.nclStab_le_qv.trans (qv_le_stab_of_dist_le_two _ h.hyp20 (isMVtx_baseA _) hc.dist_δ.le)

theorem nclStab_le_stab_μ₁ :
    S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ μ₁) ≤ stab _ μ₁ :=
  hc.nclStab_le_qv.trans (qv_le_stab_of_dist_le_two _ h.hyp20 (isMVtx_baseA _) hc.dist_μ₁.le)

theorem zh_le_centralizer {γ ρ : Vtx (puAmalgam h.le)}
    (hγ : (puAmalgam h.le).treeGraph.Adj (baseA _) γ) (hρ : IsMVtx _ ρ)
    (hdρ : (puAmalgam h.le).treeGraph.dist (baseA _) ρ = 2) :
    ZH _ γ ≤ Subgroup.centralizer (ZM _ ρ : Set (puAmalgam h.le).Universal) :=
  (zh_le_zm _ hγ).trans
    ((zm_le_qv_of_dist_lt _ (isMVtx_baseA _) (by rw [hdρ, hc.b4]; norm_num)).trans
      (Subgroup.le_centralizer_iff.1 (zm_le_centralizer_qv _ h.hyp20 hρ)))

theorem critR_le_centralizer_β (hd : S5.IsSp4Data M T L k F a) :
    ⁅ZM _ μ₁, ZM _ δ⁆ ≤
      Subgroup.centralizer (Qv _ (baseB (puAmalgam h.le)) : Set (puAmalgam h.le).Universal) :=
  critR_le_centralizer h hd hc.isMVtx_δ hc.adj.symm (le_nclStab _ _ _) hc.nclStab_le_stab_δ
    hc.isPGroup_nclStab (fun hle => hc.crit₁.2.2 ((le_nclStab _ _ _).trans hle))
    (hc.relIndex_centralizer_le hc.isMVtx_δ hc.dist_δ hc.nclStab_eq hc.relIndex_bSub_δ)
    (qv_le_stab_of_adj _ hc.adj) (isPGroup_qv _ h.hyp20 (not_isMVtx_baseB _))
    ((qv_le_stab_of_adj _ (adj_baseA_baseB (puAmalgam h.le)).symm).trans
      (S310.stab_le_normalizer_nclStab _ _ _))
    (hc.zh_le_centralizer (adj_baseA_baseB _) hc.isMVtx_μ₁ hc.dist_μ₁)

theorem critR_le_centralizer_smul (hd : S5.IsSp4Data M T L k F a)
    {y : (puAmalgam h.le).Universal} (hy : y ∈ stab _ (baseA (puAmalgam h.le)))
    (hμ : μ₁ = y⁻¹ • δ) :
    ⁅ZM _ μ₁, ZM _ δ⁆ ≤ Subgroup.centralizer
      (Qv _ (y⁻¹ • baseB (puAmalgam h.le)) : Set (puAmalgam h.le).Universal) := by
  have hyα : y⁻¹ • baseA (puAmalgam h.le) = baseA _ := (mem_stab _).1 (inv_mem hy)
  have hadjμ : (puAmalgam h.le).treeGraph.Adj μ₁ (y⁻¹ • baseB (puAmalgam h.le)) := by
    rw [hμ, adj_smul]
    exact hc.adj.symm
  have hadjα : (puAmalgam h.le).treeGraph.Adj (baseA (puAmalgam h.le))
      (y⁻¹ • baseB (puAmalgam h.le)) := by
    rw [← hyα, adj_smul]
    exact adj_baseA_baseB _
  have hγ : ¬ IsMVtx _ (y⁻¹ • baseB (puAmalgam h.le)) := by
    rw [isMVtx_smul]
    exact not_isMVtx_baseB _
  rw [Subgroup.commutator_comm]
  exact critR_le_centralizer h hd hc.isMVtx_μ₁ hadjμ hc.zm_δ_le hc.nclStab_le_stab_μ₁
    hc.isPGroup_nclStab (fun hle => hc.crit₁'.2.2 (hc.zm_δ_le.trans hle))
    (hc.relIndex_centralizer_le hc.isMVtx_μ₁ hc.dist_μ₁ rfl hc.idxB)
    (qv_le_stab_of_adj _ hadjμ.symm) (isPGroup_qv _ h.hyp20 hγ)
    ((qv_le_stab_of_adj _ hadjα.symm).trans (S310.stab_le_normalizer_nclStab _ _ _))
    (hc.zh_le_centralizer hadjα hc.isMVtx_δ hc.dist_δ)

theorem critR_le_zm_δ : ⁅ZM _ μ₁, ZM _ δ⁆ ≤ ZM _ δ :=
  Subgroup.le_normalizer_iff_commutator_le_right.1
    ((zm_le_stab_of_isCritical _ h.hyp20 h.critDist_pos hc.crit₁').trans
      (stab_le_normalizer_zm _ _))

theorem sq_eq_one_of_mem_critR {r : (puAmalgam h.le).Universal}
    (hr : r ∈ ⁅ZM _ μ₁, ZM _ δ⁆) : r ^ 2 = 1 :=
  (isElemAbelian_zm _ h.hyp20 h.critDist_pos hc.isMVtx_δ).2 r (hc.critR_le_zm_δ hr)

theorem critR_le_zh (hd : S5.IsSp4Data M T L k F a) :
    ⁅ZM _ μ₁, ZM _ δ⁆ ≤ ZH _ (baseB (puAmalgam h.le)) := by
  intro r hr
  have hrQ : r ∈ Qv _ (baseB (puAmalgam h.le)) :=
    qv_le_qv _ h.hyp20 hc.isMVtx_δ hc.adj.symm
      (zm_le_qv_self _ hc.isMVtx_δ h.critDist_pos (hc.critR_le_zm_δ hr))
  exact Subgroup.subset_closure ⟨⟨hrQ, hc.critR_le_centralizer_β hd hr⟩,
    hc.sq_eq_one_of_mem_critR hr⟩

theorem critR_le_xm (hd : S5.IsSp4Data M T L k F a) :
    ⁅ZM _ μ₁, ZM _ δ⁆ ≤ XM _ (baseA (puAmalgam h.le)) := by
  intro r hr
  have hrQ : r ∈ Qv _ (baseA (puAmalgam h.le)) := hc.zm_δ_le_qv (hc.critR_le_zm_δ hr)
  have hQβ : Qv _ (baseA (puAmalgam h.le)) ≤ Qv _ (baseB (puAmalgam h.le)) :=
    qv_le_qv _ h.hyp20 (isMVtx_baseA _) (adj_baseA_baseB _)
  have hrC : r ∈ Subgroup.centralizer (Qv _ (baseA (puAmalgam h.le)) :
      Set (puAmalgam h.le).Universal) :=
    Subgroup.centralizer_le hQβ (hc.critR_le_centralizer_β hd hr)
  exact Subgroup.subset_closure ⟨⟨hrQ, hrC⟩, hc.sq_eq_one_of_mem_critR hr⟩

theorem critR_le_dSub_of_le_stabCenter
    (hZ : ⁅ZM _ μ₁, ZM _ δ⁆ ≤ stabCenter _ (baseA (puAmalgam h.le))) :
    ⁅ZM _ μ₁, ZM _ δ⁆ ≤ S5.dSub h.le L (baseA _) := by
  intro r hr
  refine Subgroup.mem_inf.2 ⟨hc.zm_δ_le_qv (hc.critR_le_zm_δ hr), ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  obtain ⟨w, hw, hwr⟩ := hZ hr
  rw [← hwr]
  exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hw ⟨l, puTrans_le_stab h.le L _ hl⟩)

end Cfg

end S512N

end CFSG.Quasithin.MS93
