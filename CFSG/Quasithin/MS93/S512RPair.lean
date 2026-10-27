module

public import CFSG.Quasithin.MS93.S512RCore
public import CFSG.Quasithin.MS93.S511SBase

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

namespace S512R

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem stab_le_normalizer_inf_stabCenter (h : PUHyp M T L)
    (K : Subgroup (puAmalgam h.le).Universal) (δ : Vtx (puAmalgam h.le)) :
    stab _ δ ≤ Subgroup.normalizer ((K ⊓ stabCenter _ δ : Subgroup _) :
      Set (puAmalgam h.le).Universal) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro w
  constructor
  · intro hw
    have e : x * w * x⁻¹ = w := by
      rw [S510.commute_of_mem_stabCenter hw.2 hx, mul_inv_cancel_right]
    rw [e]
    exact hw
  · intro hw
    have hc := S510.commute_of_mem_stabCenter hw.2 hx
    have e : x * w * x⁻¹ = w := by
      have h1 : x * (x * w * x⁻¹) = x * w := by
        rw [hc]
        group
      exact mul_left_cancel h1
    rw [← e]
    exact hw

theorem map_conj_eq_of_le_stabCenter (h : PUHyp M T L) {δ : Vtx (puAmalgam h.le)}
    {K : Subgroup (puAmalgam h.le).Universal} (hK : K ≤ stabCenter _ δ)
    {g : (puAmalgam h.le).Universal} (hg : g ∈ stab _ δ) :
    K.map (MulAut.conj g).toMonoidHom = K := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have e : (MulAut.conj g).toMonoidHom y = y := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [S510.commute_of_mem_stabCenter (hK hy) hg, mul_inv_cancel_right]
    rw [e]
    exact hy
  · intro hx
    refine ⟨x, hx, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [S510.commute_of_mem_stabCenter (hK hx) hg, mul_inv_cancel_right]

theorem commutator_vv_qv_le_dSub_smul (h : PUHyp M T L)
    (hv : ⁅Vv _ (baseA (puAmalgam h.le)), Qv _ (baseA (puAmalgam h.le))⁆ ≤
      S5.dSub h.le L (baseA _)) (g : (puAmalgam h.le).Universal) :
    ⁅Vv _ (g • baseA (puAmalgam h.le)), Qv _ (g • baseA (puAmalgam h.le))⁆ ≤
      S5.dSub h.le L (g • baseA (puAmalgam h.le)) := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  rw [Vv, vi_smul, qv_smul, S5B.dSub_smul h.le hLn, ← Subgroup.map_commutator]
  exact Subgroup.map_mono hv

theorem exists_mul_of_mem_stab_adj (h : PUHyp M T L) {δ : Vtx (puAmalgam h.le)}
    (hβδ : (puAmalgam h.le).treeGraph.Adj (baseB _) δ) {x : (puAmalgam h.le).Universal}
    (hx : x ∈ stab _ δ) :
    ∃ l ∈ puTrans h.le L δ, ∃ t ∈ Qv _ (baseB (puAmalgam h.le)), x = l * t := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨g, hg, rfl⟩ := exists_mem_stab_smul _ (adj_baseA_baseB (puAmalgam h.le)).symm hβδ
  have hx' : g⁻¹ * x * g ∈ stab _ (baseA (puAmalgam h.le)) := (mem_stab_smul _).1 hx
  obtain ⟨l, hl, t, ht, he⟩ := S310.exists_mul_of_mem_stab h (adj_baseA_baseB _) hx'
  refine ⟨g * l * g⁻¹, ?_, g * t * g⁻¹, ?_, ?_⟩
  · rw [puTrans_smul h.le hLn]
    exact ⟨l, hl, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
  · exact (Subgroup.mem_normalizer_iff.1 (stab_le_normalizer_qv _ _ hg) t).1 ht
  · calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      _ = g * (l * t) * g⁻¹ := by rw [he]
      _ = g * l * g⁻¹ * (g * t * g⁻¹) := by group

theorem commutator_uSub_qv_le_stabCenter (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    (hb : 2 < critDist (puAmalgam h.le)) {l : Submodule F (MSP.V4 F)} (hl : MSP.IsLine l)
    (hTl : Qv _ (baseB (puAmalgam h.le)) ≤ S5.vPre h.le a (MSP.qLine l))
    (hv : ⁅Vv _ (baseA (puAmalgam h.le)), Qv _ (baseA (puAmalgam h.le))⁆ ≤
      S5.dSub h.le L (baseA _))
    {δ ε : Vtx (puAmalgam h.le)} (hβδ : (puAmalgam h.le).treeGraph.Adj (baseB _) δ)
    (hβε : (puAmalgam h.le).treeGraph.Adj (baseB _) ε) :
    ⁅S5.uSub h.le L ε, Qv _ δ⁆ ≤ stabCenter _ δ := by
  have hyp := h.hyp20
  have hδM : IsMVtx _ δ := (isMVtx_iff_of_adj _ hβδ.symm).2 (not_isMVtx_baseB _)
  have hεM : IsMVtx _ ε := (isMVtx_iff_of_adj _ hβε.symm).2 (not_isMVtx_baseB _)
  have hVD : ⁅Vv _ δ, Qv _ δ⁆ ≤ S5.dSub h.le L δ := by
    obtain ⟨g, -, rfl⟩ := exists_mem_stab_smul _ (adj_baseA_baseB (puAmalgam h.le)).symm hβδ
    exact commutator_vv_qv_le_dSub_smul h hv g
  have hdist : (puAmalgam h.le).treeGraph.dist δ ε ≤ 2 := by
    have := dist_triangle _ δ (baseB (puAmalgam h.le)) ε
    rw [dist_eq_one_of_adj _ hβδ.symm, dist_eq_one_of_adj _ hβε] at this
    omega
  have hUV : S5.uSub h.le L ε ≤ Vv _ δ :=
    (S5B.uSub_le_zm h.le ε).trans (S5B.zm_le_vv_of_dist hεM hdist)
  have h1 : ⁅S5.uSub h.le L ε, Qv _ δ⁆ ≤
      Subgroup.centralizer (puTrans h.le L δ : Set (puAmalgam h.le).Universal) :=
    ((Subgroup.commutator_mono hUV le_rfl).trans hVD).trans inf_le_right
  have hQδβ : Qv _ δ ≤ Qv _ (baseB (puAmalgam h.le)) := qv_le_qv _ hyp hδM hβδ.symm
  have h2 : ⁅S5.uSub h.le L ε, Qv _ δ⁆ ≤
      Subgroup.centralizer (Qv _ (baseB (puAmalgam h.le)) : Set (puAmalgam h.le).Universal) :=
    (Subgroup.commutator_mono le_rfl hQδβ).trans (Subgroup.le_centralizer_iff.1
      (qv_le_centralizer_commutator_of_le_qLine h hd hl hTl hεM hβε.symm))
  have hUst : S5.uSub h.le L ε ≤ stab _ δ :=
    ((S5B.uSub_le_zm h.le ε).trans (zm_le_qv_of_dist_lt _ hεM
      (by rw [dist_eq_one_of_adj _ hβε.symm]; omega))).trans (qv_le_stab_of_adj _ hβδ)
  have h3 : ⁅S5.uSub h.le L ε, Qv _ δ⁆ ≤ stab _ δ := commutator_le_of_le hUst (qv_le_stab _ _)
  intro x hx
  rw [S510.mem_stabCenter_iff]
  refine ⟨h3 hx, fun g hg => ?_⟩
  obtain ⟨l', hl', t, ht, rfl⟩ := exists_mul_of_mem_stab_adj h hβδ hg
  have hxl : l' * x = x * l' := Subgroup.mem_centralizer_iff.1 (h1 hx) l' hl'
  have hxt : t * x = x * t := Subgroup.mem_centralizer_iff.1 (h2 hx) t ht
  calc l' * t * x = l' * (t * x) := by group
    _ = l' * (x * t) := by rw [hxt]
    _ = (l' * x) * t := by group
    _ = (x * l') * t := by rw [hxl]
    _ = x * (l' * t) := by group

theorem commutator_zm_qv_le_stabCenter (h32 : S32) (h53 : S53) (h : PUHyp M T L)
    (hmin : PUMin M T L) (hd : S5.IsSp4Data M T L k F a) (hb : 2 < critDist (puAmalgam h.le))
    {l : Submodule F (MSP.V4 F)} (hl : MSP.IsLine l)
    (hTl : Qv _ (baseB (puAmalgam h.le)) ≤ S5.vPre h.le a (MSP.qLine l))
    (hv : ⁅Vv _ (baseA (puAmalgam h.le)), Qv _ (baseA (puAmalgam h.le))⁆ ≤
      S5.dSub h.le L (baseA _))
    {δ ε : Vtx (puAmalgam h.le)} (hβδ : (puAmalgam h.le).treeGraph.Adj (baseB _) δ)
    (hβε : (puAmalgam h.le).treeGraph.Adj (baseB _) ε) :
    ⁅ZM _ ε, Qv _ δ⁆ ≤ stabCenter _ δ := by
  have hyp := h.hyp20
  have hδM : IsMVtx _ δ := (isMVtx_iff_of_adj _ hβδ.symm).2 (not_isMVtx_baseB _)
  have hεM : IsMVtx _ ε := (isMVtx_iff_of_adj _ hβε.symm).2 (not_isMVtx_baseB _)
  have hZ := S511S.zm_le_sup' h32 h53 h hmin hb hd hεM
  have hn : stab _ δ ≤ Subgroup.normalizer (stabCenter _ δ : Set (puAmalgam h.le).Universal) := by
    have := stab_le_normalizer_inf_stabCenter h ⊤ δ
    rwa [top_inf_eq] at this
  have hβst : Qv _ (baseB (puAmalgam h.le)) ≤ stab _ δ := qv_le_stab_of_adj _ hβδ
  have hUst : S5.uSub h.le L ε ≤ stab _ δ :=
    ((S5B.uSub_le_zm h.le ε).trans (zm_le_qv_of_dist_lt _ hεM
      (by rw [dist_eq_one_of_adj _ hβε.symm]; omega))).trans hβst
  have hXst : XM _ ε ⊓ stabCenter _ ε ≤ stab _ δ :=
    inf_le_left.trans ((xm_le_qv _ ε).trans ((qv_le_qv _ hyp hεM hβε.symm).trans hβst))
  have hQδε : Qv _ δ ≤ stab _ ε :=
    (qv_le_qv _ hyp hδM hβδ.symm).trans (qv_le_stab_of_adj _ hβε)
  refine (Subgroup.commutator_mono hZ le_rfl).trans (S310.commutator_sup_left_le
    (hUst.trans hn) (hXst.trans hn)
    (commutator_uSub_qv_le_stabCenter h hd hb hl hTl hv hβδ hβε) ?_)
  rw [Subgroup.commutator_le]
  intro x hx t ht
  have hxt := S510.commute_of_mem_stabCenter hx.2 (hQδε ht)
  rw [commutatorElement_def, ← hxt, mul_inv_cancel_right, mul_inv_cancel]
  exact one_mem _

theorem commutator_nclStab_qv_le (h32 : S32) (h53 : S53) (h : PUHyp M T L)
    (hmin : PUMin M T L) (hd : S5.IsSp4Data M T L k F a) (hb : 2 < critDist (puAmalgam h.le))
    {l : Submodule F (MSP.V4 F)} (hl : MSP.IsLine l)
    (hTl : Qv _ (baseB (puAmalgam h.le)) ≤ S5.vPre h.le a (MSP.qLine l))
    (hv : ⁅Vv _ (baseA (puAmalgam h.le)), Qv _ (baseA (puAmalgam h.le))⁆ ≤
      S5.dSub h.le L (baseA _))
    {δ ε : Vtx (puAmalgam h.le)} (hβδ : (puAmalgam h.le).treeGraph.Adj (baseB _) δ)
    (hβε : (puAmalgam h.le).treeGraph.Adj (baseB _) ε) :
    ⁅S5.nclStab _ δ (ZM _ ε), Qv _ δ⁆ ≤ ZM _ ε ⊓ stabCenter _ δ := by
  have hyp := h.hyp20
  have hδM : IsMVtx _ δ := (isMVtx_iff_of_adj _ hβδ.symm).2 (not_isMVtx_baseB _)
  have hεM : IsMVtx _ ε := (isMVtx_iff_of_adj _ hβε.symm).2 (not_isMVtx_baseB _)
  have hβst : Qv _ (baseB (puAmalgam h.le)) ≤ stab _ δ := qv_le_stab_of_adj _ hβδ
  have hZst : ZM _ ε ≤ stab _ δ :=
    (zm_le_qv_of_dist_lt _ hεM (by rw [dist_eq_one_of_adj _ hβε.symm]; omega)).trans hβst
  have hQδε : Qv _ δ ≤ stab _ ε :=
    (qv_le_qv _ hyp hδM hβδ.symm).trans (qv_le_stab_of_adj _ hβε)
  have key : ⁅ZM _ ε, Qv _ δ⁆ ≤ ZM _ ε ⊓ stabCenter _ δ :=
    le_inf (Subgroup.le_normalizer_iff_commutator_le_left.1
      (hQδε.trans (stab_le_normalizer_zm _ _)))
      (commutator_zm_qv_le_stabCenter h32 h53 h hmin hd hb hl hTl hv hβδ hβε)
  refine S512N.commutator_iSup_le (fun g => ?_) (fun g => ?_)
  · rintro _ ⟨z, hz, rfl⟩
    exact stab_le_normalizer_inf_stabCenter h _ δ
      (mul_mem (mul_mem g.2 (hZst hz)) (inv_mem g.2))
  · have hQg := map_conj_eq_of_mem_normalizer (stab_le_normalizer_qv _ δ g.2)
    rw [← hQg, ← Subgroup.map_commutator,
      map_conj_eq_of_le_stabCenter h (key.trans inf_le_right) g.2]
    exact key

theorem commutator_inf_qv_nclStab_le (h32 : S32) (h53 : S53) (h : PUHyp M T L)
    (hmin : PUMin M T L) (hd : S5.IsSp4Data M T L k F a) (hb : 2 < critDist (puAmalgam h.le))
    {l : Submodule F (MSP.V4 F)} (hl : MSP.IsLine l)
    (hTl : Qv _ (baseB (puAmalgam h.le)) ≤ S5.vPre h.le a (MSP.qLine l))
    (hv : ⁅Vv _ (baseA (puAmalgam h.le)), Qv _ (baseA (puAmalgam h.le))⁆ ≤
      S5.dSub h.le L (baseA _))
    {δ ε : Vtx (puAmalgam h.le)} (hβδ : (puAmalgam h.le).treeGraph.Adj (baseB _) δ)
    (hβε : (puAmalgam h.le).treeGraph.Adj (baseB _) ε) (X : Subgroup (puAmalgam h.le).Universal) :
    ⁅X ⊓ Qv _ δ, S5.nclStab _ δ (ZM _ ε)⁆ ≤ ZM _ ε := by
  rw [Subgroup.commutator_comm]
  exact ((Subgroup.commutator_mono le_rfl inf_le_right).trans
    (commutator_nclStab_qv_le h32 h53 h hmin hd hb hl hTl hv hβδ hβε)).trans inf_le_left

theorem qv_le_vPre_qLine_core (h54 : S54) (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb4 : critDist (puAmalgam h.le) = 4) (hd : S5.IsSp4Data M T L k F a)
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    {μ : Vtx (puAmalgam h.le)} {y : (puAmalgam h.le).Universal}
    (hy : y ∈ stab _ (baseA (puAmalgam h.le))) (hμy : μ = y • geo _ (baseA (puAmalgam h.le)) α' 2)
    (hcμ : IsCritical _ μ (geo _ (baseA (puAmalgam h.le)) α' 2))
    (hbad : 2 ^ k < (Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2)).relIndex (ZM _ μ))
    (hRc : ⁅ZM (puAmalgam h.le) μ, ZM (puAmalgam h.le) (geo _ (baseA (puAmalgam h.le)) α' 2)⁆ ≤
      stabCenter _ (baseA (puAmalgam h.le))) :
    ∃ l : Submodule F (MSP.V4 F), MSP.IsLine l ∧
      Qv _ (baseB (puAmalgam h.le)) ≤ S5.vPre h.le a (MSP.qLine l) := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  set γ := geo _ (baseA (puAmalgam h.le)) α' 2 with hγdef
  have hγM : IsMVtx _ γ := isMVtx_geo_two _ hyp hb0 hc
  have hdαγ : (puAmalgam h.le).treeGraph.dist (baseA _) γ = 2 :=
    dist_geo _ (by have := hc.2.1; omega)
  obtain ⟨hμM, -, -, hd4, hμρ, hρα, -, -, -, -, -, -⟩ := S512T.pair_facts h hb4 hcμ
  have hdαμ : (puAmalgam h.le).treeGraph.dist (baseA _) μ = 2 := by
    have := dist_smul _ y (baseA (puAmalgam h.le)) γ
    rw [(mem_stab _).1 hy, ← hμy] at this
    rw [this, hdαγ]
  have hmid : geo _ μ γ 2 = baseA (puAmalgam h.le) := by
    symm
    refine eq_geo_of_dist _ (by rw [tdist_comm]; exact hdαμ) ?_
    rw [tdist_comm, hdαμ, hdαγ, hd4]
  rw [hmid] at hρα
  obtain ⟨hEε, hNs, -, -⟩ := S512T.zm_facts h hb4 hcμ
  obtain ⟨hrel, hEQ⟩ := S512T.bad_indices h hb4 hd hcμ hbad
  have hRZ : ⁅S5.uSub h.le L μ, ZM _ γ⁆ ≤ ZM _ γ :=
    (S512T.commutator_uSub_zm_le h hb4 hcμ).trans inf_le_left
  have hquad : ⁅S5.uSub h.le L μ, ZM _ γ⁆ ≤
      Subgroup.centralizer (ZM _ γ : Set (puAmalgam h.le).Universal) := by
    have hab := (isElemAbelian_zm _ hyp hb0 hγM).1
    refine hRZ.trans fun z hz => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have := hab.is_comm.comm ⟨w, hw⟩ ⟨z, hz⟩
    simpa using congrArg Subtype.val this
  have bad := S512T.bad_vertex h54 h hmin hb hd hμM hμρ hEε hrel hquad hEQ hNs le_rfl hquad
  have hQR : Qv _ (geo _ μ γ 1) ≤ Subgroup.centralizer
      ((⁅S5.uSub h.le L μ, ZM _ γ⁆ : Subgroup _) : Set (puAmalgam h.le).Universal) := by
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact (S510.commute_of_mem_stabCenter
      (hRc (Subgroup.commutator_mono (S5B.uSub_le_zm h.le μ) le_rfl hr))
      (qv_le_stab_of_adj _ hρα ht)).symm
  obtain ⟨-, hJT, l', hl', -, hJl'⟩ := bad.2.2.1 hQR
  exact ⟨l', hl', hJT ▸ hJl'⟩

end S512R

end CFSG.Quasithin.MS93
