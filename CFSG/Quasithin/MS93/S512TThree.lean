module

public import CFSG.Quasithin.MS93.S512TChain
public import CFSG.Quasithin.MS93.S510Loc

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

namespace S512T

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem zm_le_bSub (h : PUHyp M T L) {α : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) :
    ZM _ α ≤ S5.bSub h.le L α := by
  intro z hz
  refine Subgroup.subset_closure ⟨?_, fun y hy => ?_⟩
  · exact le_iSup₂_of_le (f := fun ρ (_ : ρ ∈ {ρ : Vtx (puAmalgam h.le) |
      (puAmalgam h.le).treeGraph.dist α ρ ≤ 2}) => Zv (puAmalgam h.le) ρ) α (by simp)
      (zv_of_isMVtx _ hα).ge hz
  · have hyz : y * z⁻¹ * y⁻¹ ∈ ZM _ α :=
      (Subgroup.mem_normalizer_iff.1 (stab_le_normalizer_zm _ _ (puTrans_le_stab h.le L α hy))
        _).1 (inv_mem hz)
    have e : ⁅z, y⁆ = z * (y * z⁻¹ * y⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact mul_mem hz hyz

theorem relIndex_bSub_zm_eq (h : PUHyp M T L) (hb4 : critDist (puAmalgam h.le) = 4)
    {μ γ α : Vtx (puAmalgam h.le)} (hc : IsCritical _ μ γ) (hmid : geo _ μ γ 2 = α) :
    (S5.bSub h.le L α).relIndex (ZM _ μ) = (S5.bSub h.le L α).relIndex (S5.uSub h.le L μ) := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  obtain ⟨hμ, -, hα, -, hμρ, hρα, -⟩ := pair_facts h hb4 hc
  subst hmid
  have hZ := S5B.zm_eq_zh_sup_uSub h hμ hμρ
  have hKB : ZH _ (geo _ μ γ 1) ≤ S5.bSub h.le L (geo _ μ γ 2) :=
    (zh_le_zm _ hρα.symm).trans (zm_le_bSub h hα)
  have hab := (isElemAbelian_zm _ hyp hb0 hμ).1
  have hcomm : ∀ x ∈ ZM (puAmalgam h.le) μ, ∀ y ∈ ZM (puAmalgam h.le) μ, x * y = y * x := by
    intro x hx y hy
    have := hab.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
    simpa using congrArg Subtype.val this
  rw [hZ, sup_comm, relIndex_sup_of_le_of_comm (A := ZM _ μ) hcomm (S5B.uSub_le_zm h.le μ)
    (zh_le_zm _ hμρ) hKB]

theorem relIndex_qv_uSub_eq (h : PUHyp M T L) (hb4 : critDist (puAmalgam h.le) = 4)
    {μ γ : Vtx (puAmalgam h.le)} (hc : IsCritical _ μ γ) :
    (Qv _ γ).relIndex (S5.uSub h.le L μ) = (Qv _ γ).relIndex (ZM _ μ) := by
  rw [relIndex_qv_zm_eq h hb4 hc, ← Subgroup.inf_relIndex_right (Qv _ γ), inf_comm,
    uSub_inf_qv_eq h hb4 hc, inf_comm, Subgroup.inf_relIndex_right]

theorem jOff_le_normalizer_y (h54 : S54) (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb4 : critDist (puAmalgam h.le) = 4) (hd : S5.IsSp4Data M T L k F a)
    {μ γ α ρ : Vtx (puAmalgam h.le)} (hc : IsCritical _ μ γ) (hmid : geo _ μ γ 2 = α)
    (hαρ : (puAmalgam h.le).treeGraph.Adj α ρ) (hρμ : (puAmalgam h.le).treeGraph.Adj ρ μ)
    (hq : (Qv _ γ).relIndex (ZM _ μ) = 2 ^ k) :
    S5.jOff h.le L (2 ^ k) μ ρ ≤ Subgroup.normalizer
      (((S5.uSub h.le L μ ⊓ Qv _ γ) ⊔ XM _ α : Subgroup _) : Set _) := by
  have hρ : ρ = geo _ μ γ 1 := eq_geo_one_of_adj h hb4 hc hmid hαρ hρμ
  obtain ⟨hZρ, -, -, -⟩ := zm_facts h hb4 hc
  rw [← hρ] at hZρ
  have hrel : (Subgroup.centralizer (ZM _ γ : Set (puAmalgam h.le).Universal)).relIndex
      (S5.uSub h.le L μ) = 2 ^ k := by
    rw [← relIndex_qv_zm_eq h hb4 hc]
    exact hq
  have hJ := S510.jOff_le_normalizer_of_relIndex h hmin (by omega) hd h54 hc.1 hρμ.symm hZρ hrel
  rw [← uSub_inf_qv_eq h hb4 hc] at hJ
  refine (le_inf hJ ?_).trans (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  exact (S5B.jOff_le_qv h.le L _ μ ρ).trans ((qv_le_stab_of_adj _ hαρ.symm).trans
    (stab_le_normalizer_xm _ α))

theorem jOff_eq_qv_of_point (h : PUHyp M T L) {q : ℕ}
    (hJT : S5.jOff h.le L q (baseA _) (baseB _) = Qv _ (baseB (puAmalgam h.le)))
    {γ ε : Vtx (puAmalgam h.le)} (hγ : IsMVtx _ γ) (hγε : (puAmalgam h.le).treeGraph.Adj γ ε) :
    S5.jOff h.le L q γ ε = Qv _ ε := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨g, rfl, rfl⟩ := exists_smul_base_edge _ hγ hγε
  rw [S5B.jOff_smul h.le hLn, hJT, qv_smul]

theorem xm_eq_uSub_sup_of_xq (h : PUHyp M T L) (hXU : Xq M = Uq M T L ⊔ Zq M L) :
    XM _ (baseA (puAmalgam h.le)) = S5.uSub h.le L (baseA _) ⊔ XM _ (baseA (puAmalgam h.le)) ⊓
      Subgroup.centralizer (puTrans h.le L (baseA _) : Set (puAmalgam h.le).Universal) := by
  rw [S5B.uSub_baseA h, S5B.puTrans_L_baseA h, S5B.xm_baseA_eq h,
    ← imM_inf_centralizer h.le _ h.L_le,
    ← S5B.imM_sup_of_le h.le (Uq_le h.L_le) (inf_le_left.trans (Xq_le M))]
  conv_lhs => rw [hXU]

theorem three_of_le_normalizer (h32 : S32) (h58 : S5B.S58) (h : PUHyp M T L)
    (hmin : PUMin M T L) (hb4 : critDist (puAmalgam h.le) = 4) (hd : S5.IsSp4Data M T L k F a)
    {α' ν μ₁ μ₂ : Vtx (puAmalgam h.le)} (hch : S5B.IsChain512 h (2 ^ k) a α' ν μ₁ μ₂)
    (hq : (Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2)).relIndex (ZM _ μ₁) = 2 ^ k)
    (hn : puTrans h.le L (baseA _) ≤ Subgroup.normalizer
      (((S5.uSub h.le L μ₁ ⊓ Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2)) ⊔
        XM _ (baseA (puAmalgam h.le)) : Subgroup _) : Set _)) :
    (S5.bSub h.le L (baseA _)).relIndex (ZM _ μ₁) = 2 ^ k := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  obtain ⟨hc, hαβ, hcμ, ⟨y, hy, hμy⟩, hdμ, hmid, -⟩ := chain_geo h hb4 hch
  have hμM : IsMVtx _ μ₁ := hcμ.1
  have hYZ : S5.uSub h.le L μ₁ ⊓ Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2) ≤ ZM _ μ₁ :=
    inf_le_left.trans (S5B.uSub_le_zm h.le μ₁)
  have hYB : S5.uSub h.le L μ₁ ⊓ Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2) ≤
      S5.bSub h.le L (baseA _) :=
    S5B.le_bSub_of_xm h (by omega) (h32 G M T L h).2.1 (isMVtx_baseA _) hdμ
      (hYZ.trans (zm_le_xm _ hyp hb0 hμM)) (hYZ.trans (S5B.zm_le_vv_of_dist hμM hdμ.le)) hn
  rw [relIndex_bSub_zm_eq h hb4 hcμ hmid]
  apply le_antisymm
  · rw [← relIndex_qv_uSub_eq h hb4 hcμ] at hq
    rw [← hq, ← Subgroup.inf_relIndex_right (S5.bSub h.le L (baseA _)),
      ← Subgroup.inf_relIndex_right (Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2))]
    refine Subgroup.relIndex_le_of_le_left (fun x hx => ⟨hYB ⟨hx.2, hx.1⟩, hx.2⟩) ?_
    rw [Subgroup.inf_relIndex_right, hq]
    positivity
  · have h1 := (h58 G M T L h hmin (by omega) k F _ _ a hd α' hc hαβ).2.2
    rw [hμy, S5B.relIndex_bSub_uSub_smul h hy]
    exact h1

theorem exists_le_sup_of_alt1 (h : PUHyp M T L) {q : ℕ} {α' δ μ : Vtx (puAmalgam h.le)}
    {g x : (puAmalgam h.le).Universal} (hg : g ∈ stab _ (baseA (puAmalgam h.le)))
    (hx : x ∈ puTrans h.le L (baseA _)) (hβδ : (puAmalgam h.le).treeGraph.Adj (baseB _) δ)
    (hμeq : μ = g⁻¹ • δ ∨ μ = x⁻¹ • g⁻¹ • δ)
    (halt : puTrans h.le L (baseA _) ≤
      (S5.jOff h.le L q (g⁻¹ • δ) (g⁻¹ • baseB (puAmalgam h.le)) ⊔ S5.zHat _ (baseA _) α') ⊓
        (S5.rconj x (S5.jOff h.le L q (g⁻¹ • δ) (g⁻¹ • baseB (puAmalgam h.le))) ⊔
          S5.zHat _ (baseA _) α')) :
    ∃ ρ, (puAmalgam h.le).treeGraph.Adj (baseA _) ρ ∧ (puAmalgam h.le).treeGraph.Adj ρ μ ∧
      puTrans h.le L (baseA _) ≤ S5.jOff h.le L q μ ρ ⊔ S5.zHat _ (baseA _) α' := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have hgα : g⁻¹ • baseA (puAmalgam h.le) = baseA _ := (mem_stab _).1 (inv_mem hg)
  have hxα : x⁻¹ • baseA (puAmalgam h.le) = baseA _ :=
    (mem_stab _).1 (inv_mem (puTrans_le_stab h.le L _ hx))
  have hadj1 : (puAmalgam h.le).treeGraph.Adj (baseA _) (g⁻¹ • baseB (puAmalgam h.le)) := by
    have := (adj_smul _ g⁻¹ _ _).2 (adj_baseA_baseB (puAmalgam h.le))
    rwa [hgα] at this
  have hadj2 : (puAmalgam h.le).treeGraph.Adj (g⁻¹ • baseB (puAmalgam h.le)) (g⁻¹ • δ) :=
    (adj_smul _ g⁻¹ _ _).2 hβδ
  rcases hμeq with rfl | rfl
  · exact ⟨_, hadj1, hadj2, halt.trans inf_le_left⟩
  · have hJx : S5.jOff h.le L q (x⁻¹ • g⁻¹ • δ) (x⁻¹ • g⁻¹ • baseB (puAmalgam h.le)) =
        S5.rconj x (S5.jOff h.le L q (g⁻¹ • δ) (g⁻¹ • baseB (puAmalgam h.le))) := by
      rw [S5B.jOff_smul h.le hLn, S5.rconj]
    have hadj1' : (puAmalgam h.le).treeGraph.Adj (baseA _)
        (x⁻¹ • g⁻¹ • baseB (puAmalgam h.le)) := by
      have := (adj_smul _ x⁻¹ _ _).2 hadj1
      rwa [hxα] at this
    refine ⟨_, hadj1', (adj_smul _ x⁻¹ _ _).2 hadj2, ?_⟩
    rw [hJx]
    exact halt.trans inf_le_right

omit [Fintype F] in
theorem le_sup_of_alt1 (h : PUHyp M T L) (hb4 : critDist (puAmalgam h.le) = 4) {q : ℕ}
    {α' ν μ₁ μ₂ : Vtx (puAmalgam h.le)} (hch : S5B.IsChain512 h q a α' ν μ₁ μ₂)
    {g x : (puAmalgam h.le).Universal} (hg : g ∈ stab _ (baseA (puAmalgam h.le)))
    (hx : x ∈ puTrans h.le L (baseA _))
    (hμeq : μ₁ = g⁻¹ • geo _ (baseA (puAmalgam h.le)) α' 2 ∨
      μ₁ = x⁻¹ • g⁻¹ • geo _ (baseA (puAmalgam h.le)) α' 2)
    (halt : puTrans h.le L (baseA _) ≤
      (S5.jOff h.le L q (g⁻¹ • geo _ (baseA (puAmalgam h.le)) α' 2)
          (g⁻¹ • baseB (puAmalgam h.le)) ⊔ S5.zHat _ (baseA _) α') ⊓
        (S5.rconj x (S5.jOff h.le L q (g⁻¹ • geo _ (baseA (puAmalgam h.le)) α' 2)
          (g⁻¹ • baseB (puAmalgam h.le))) ⊔ S5.zHat _ (baseA _) α')) :
    puTrans h.le L (baseA _) ≤
      S5.jOff h.le L q μ₁ (geo _ μ₁ (geo _ (baseA (puAmalgam h.le)) α' 2) 1) ⊔
        S5.zHat _ (baseA _) α' := by
  obtain ⟨-, -, hcμ, -, -, hmid, hβγ⟩ := chain_geo h hb4 hch
  obtain ⟨ρ, hαρ, hρμ, hL⟩ := exists_le_sup_of_alt1 h hg hx hβγ hμeq halt
  rwa [eq_geo_one_of_adj h hb4 hcμ hmid hαρ hρμ] at hL

theorem le_normalizer_of_le_sup_of (h54 : S54)
    (h : PUHyp M T L) (hmin : PUMin M T L) (hb4 : critDist (puAmalgam h.le) = 4)
    (hd : S5.IsSp4Data M T L k F a) {α' ν μ₁ μ₂ : Vtx (puAmalgam h.le)}
    (hch : S5B.IsChain512 h (2 ^ k) a α' ν μ₁ μ₂)
    (hZ : S5.zHat _ (baseA (puAmalgam h.le)) α' ≤ Subgroup.normalizer
      (((S5.uSub h.le L μ₁ ⊓ Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2)) ⊔
        XM _ (baseA (puAmalgam h.le)) : Subgroup _) : Set _))
    (hq : (Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2)).relIndex (ZM _ μ₁) = 2 ^ k)
    (hL : puTrans h.le L (baseA _) ≤
      S5.jOff h.le L (2 ^ k) μ₁ (geo _ μ₁ (geo _ (baseA (puAmalgam h.le)) α' 2) 1) ⊔
        S5.zHat _ (baseA _) α') :
    puTrans h.le L (baseA _) ≤ Subgroup.normalizer
      (((S5.uSub h.le L μ₁ ⊓ Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2)) ⊔
        XM _ (baseA (puAmalgam h.le)) : Subgroup _) : Set _) := by
  obtain ⟨-, -, hcμ, -, -, hmid, -⟩ := chain_geo h hb4 hch
  obtain ⟨-, -, -, -, hμρ, hρα, -⟩ := pair_facts h hb4 hcμ
  rw [hmid] at hρα
  exact hL.trans (sup_le (jOff_le_normalizer_y h54 h hmin hb4 hd hcμ hmid hρα.symm hμρ.symm hq)
    hZ)

theorem stab_le_normalizer_of_qv_of
    (h : PUHyp M T L) (hb4 : critDist (puAmalgam h.le) = 4)
    (hd : S5.IsSp4Data M T L k F a) {α' ν μ₁ μ₂ : Vtx (puAmalgam h.le)}
    (hch : S5B.IsChain512 h (2 ^ k) a α' ν μ₁ μ₂)
    (hZ : S5.zHat _ (baseA (puAmalgam h.le)) α' ≤ Subgroup.normalizer
      (((S5.uSub h.le L μ₁ ⊓ Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2)) ⊔
        XM _ (baseA (puAmalgam h.le)) : Subgroup _) : Set _))
    (hq1 : (Qv _ α').relIndex (ZM _ (baseA (puAmalgam h.le))) = 2 ^ k)
    (h56 : ∀ l, ¬ S5.Case56 h (2 ^ k) a (geo _ (baseA (puAmalgam h.le)) α' 2) l)
    (hTY : Qv _ (geo _ μ₁ (geo _ (baseA (puAmalgam h.le)) α' 2) 1) ≤ Subgroup.normalizer
      ((S5.uSub h.le L μ₁ ⊓ Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2) : Subgroup _) :
        Set (puAmalgam h.le).Universal)) :
    stab _ (baseA (puAmalgam h.le)) ≤ Subgroup.normalizer
      (((S5.uSub h.le L μ₁ ⊓ Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2)) ⊔
        XM _ (baseA (puAmalgam h.le)) : Subgroup _) : Set _) := by
  obtain ⟨hc, -, hcμ, -, -, hmid, hβγ⟩ := chain_geo h hb4 hch
  obtain ⟨ρ, hαρ, hρμ, -, hst, -⟩ := S510.lam55_facts h hc hβγ h56 hch.2.2.2.2.1
  have hρe := eq_geo_one_of_adj h hb4 hcμ hmid hαρ hρμ
  subst hρe
  rw [← hst]
  refine sup_le ?_ ?_
  · exact (le_inf hTY ((qv_le_stab_of_adj _ hαρ.symm).trans (stab_le_normalizer_xm _ _))).trans
      (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  · rw [← zHat_eq h hd hc hq1]
    exact hZ

theorem stab_le_normalizer_of_point_of (h54 : S54)
    (h : PUHyp M T L) (hmin : PUMin M T L) (hb4 : critDist (puAmalgam h.le) = 4)
    (hd : S5.IsSp4Data M T L k F a) {α' ν μ₁ μ₂ : Vtx (puAmalgam h.le)}
    (hch : S5B.IsChain512 h (2 ^ k) a α' ν μ₁ μ₂)
    (hZ : S5.zHat _ (baseA (puAmalgam h.le)) α' ≤ Subgroup.normalizer
      (((S5.uSub h.le L μ₁ ⊓ Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2)) ⊔
        XM _ (baseA (puAmalgam h.le)) : Subgroup _) : Set _))
    (hq1 : (Qv _ α').relIndex (ZM _ (baseA (puAmalgam h.le))) = 2 ^ k)
    (hq : (Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2)).relIndex (ZM _ μ₁) = 2 ^ k)
    (h56 : ∀ l, ¬ S5.Case56 h (2 ^ k) a (geo _ (baseA (puAmalgam h.le)) α' 2) l)
    (hJT : S5.jOff h.le L (2 ^ k) (baseA _) (baseB _) = Qv _ (baseB (puAmalgam h.le))) :
    stab _ (baseA (puAmalgam h.le)) ≤ Subgroup.normalizer
      (((S5.uSub h.le L μ₁ ⊓ Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2)) ⊔
        XM _ (baseA (puAmalgam h.le)) : Subgroup _) : Set _) := by
  obtain ⟨-, -, hcμ, -, -, -, -⟩ := chain_geo h hb4 hch
  obtain ⟨-, -, -, -, hμρ, -⟩ := pair_facts h hb4 hcμ
  obtain ⟨hZρ, -, -, -⟩ := zm_facts h hb4 hcμ
  refine stab_le_normalizer_of_qv_of h hb4 hd hch hZ hq1 h56 ?_
  rw [← jOff_eq_qv_of_point h hJT hcμ.1 hμρ, uSub_inf_qv_eq h hb4 hcμ]
  refine S510.jOff_le_normalizer_of_relIndex h hmin (by omega) hd h54 hcμ.1 hμρ hZρ ?_
  rw [← relIndex_qv_zm_eq h hb4 hcμ]
  exact hq

theorem le_normalizer_of_concl56_g_of (h54 : S54)
    (h : PUHyp M T L) (hmin : PUMin M T L) (hb4 : critDist (puAmalgam h.le) = 4)
    (hd : S5.IsSp4Data M T L k F a) {α' ν μ₁ μ₂ : Vtx (puAmalgam h.le)}
    (hch : S5B.IsChain512 h (2 ^ k) a α' ν μ₁ μ₂)
    (hZ : S5.zHat _ (baseA (puAmalgam h.le)) α' ≤ Subgroup.normalizer
      (((S5.uSub h.le L μ₁ ⊓ Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2)) ⊔
        XM _ (baseA (puAmalgam h.le)) : Subgroup _) : Set _))
    (hq1 : (Qv _ α').relIndex (ZM _ (baseA (puAmalgam h.le))) = 2 ^ k)
    (hq : (Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2)).relIndex (ZM _ μ₁) = 2 ^ k)
    {l : Submodule F (MSP.V4 F)}
    (hl : S5.Case56 h (2 ^ k) a (geo _ (baseA (puAmalgam h.le)) α' 2) l)
    {g x : (puAmalgam h.le).Universal} (hg : g ∈ stab _ (baseA (puAmalgam h.le)))
    (hc56 : S5.Concl56 h (2 ^ k) a α' l g x)
    (hμ : μ₁ = g⁻¹ • geo _ (baseA (puAmalgam h.le)) α' 2)
    (hZx : ZM _ (x • α') ≤ Subgroup.normalizer
      (((S5.uSub h.le L μ₁ ⊓ Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2)) ⊔
        XM _ (baseA (puAmalgam h.le)) : Subgroup _) : Set (puAmalgam h.le).Universal)) :
    puTrans h.le L (baseA _) ≤ Subgroup.normalizer
      (((S5.uSub h.le L μ₁ ⊓ Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2)) ⊔
        XM _ (baseA (puAmalgam h.le)) : Subgroup _) : Set (puAmalgam h.le).Universal) := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨hc, -, hcμ, -, -, hmid, hβγ⟩ := chain_geo h hb4 hch
  rw [zHat_eq h hd hc hq1] at hZ
  obtain ⟨-, -, hL, -⟩ := hc56
  rw [zHat_eq h hd hc hq1] at hL
  have hgα : g⁻¹ • baseA (puAmalgam h.le) = baseA _ := (mem_stab _).1 (inv_mem hg)
  have hadj1 : (puAmalgam h.le).treeGraph.Adj (baseA _) (g⁻¹ • baseB (puAmalgam h.le)) := by
    have := (adj_smul _ g⁻¹ _ _).2 (adj_baseA_baseB (puAmalgam h.le))
    rwa [hgα] at this
  have hadj2 : (puAmalgam h.le).treeGraph.Adj (g⁻¹ • baseB (puAmalgam h.le)) μ₁ := by
    rw [hμ]
    exact (adj_smul _ g⁻¹ _ _).2 hβγ
  have hJg : S5.rconj g (S5.jOff h.le L (2 ^ k) (baseA _) (baseB _)) =
      S5.jOff h.le L (2 ^ k) μ₁ (g⁻¹ • baseB (puAmalgam h.le)) := by
    rw [hμ, S5B.jOff_smul h.le hLn, hl.1, S5.rconj]
  have hZg : S5.rconj x⁻¹ (ZM _ α') = ZM _ (x • α') := by
    rw [S5.rconj, inv_inv, zm_smul]
  rw [hJg, hZg] at hL
  refine hL.trans (sup_le (sup_le ?_ hZ) hZx)
  exact jOff_le_normalizer_y h54 h hmin hb4 hd hcμ hmid hadj1 hadj2 hq

theorem le_normalizer_of_concl56_x_of (h54 : S54)
    (h : PUHyp M T L) (hmin : PUMin M T L) (hb4 : critDist (puAmalgam h.le) = 4)
    (hd : S5.IsSp4Data M T L k F a) {α' ν μ₁ μ₂ : Vtx (puAmalgam h.le)}
    (hch : S5B.IsChain512 h (2 ^ k) a α' ν μ₁ μ₂)
    (hZ : S5.zHat _ (baseA (puAmalgam h.le)) α' ≤ Subgroup.normalizer
      (((S5.uSub h.le L μ₁ ⊓ Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2)) ⊔
        XM _ (baseA (puAmalgam h.le)) : Subgroup _) : Set _))
    (hq1 : (Qv _ α').relIndex (ZM _ (baseA (puAmalgam h.le))) = 2 ^ k)
    (hq : (Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2)).relIndex (ZM _ μ₁) = 2 ^ k)
    {l : Submodule F (MSP.V4 F)}
    (hl : S5.Case56 h (2 ^ k) a (geo _ (baseA (puAmalgam h.le)) α' 2) l)
    {g x : (puAmalgam h.le).Universal} (hg : g ∈ stab _ (baseA (puAmalgam h.le)))
    (hx : x ∈ puTrans h.le L (baseA _)) (hc56 : S5.Concl56 h (2 ^ k) a α' l g x)
    (hμ : μ₁ = x⁻¹ • g⁻¹ • geo _ (baseA (puAmalgam h.le)) α' 2)
    (hZx : ZM _ (x⁻¹ • α') ≤ Subgroup.normalizer
      (((S5.uSub h.le L μ₁ ⊓ Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2)) ⊔
        XM _ (baseA (puAmalgam h.le)) : Subgroup _) : Set (puAmalgam h.le).Universal)) :
    puTrans h.le L (baseA _) ≤ Subgroup.normalizer
      (((S5.uSub h.le L μ₁ ⊓ Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2)) ⊔
        XM _ (baseA (puAmalgam h.le)) : Subgroup _) : Set (puAmalgam h.le).Universal) := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨hc, -, hcμ, -, -, hmid, hβγ⟩ := chain_geo h hb4 hch
  rw [zHat_eq h hd hc hq1] at hZ
  obtain ⟨-, -, hL, -⟩ := hc56
  rw [zHat_eq h hd hc hq1] at hL
  have hgα : g⁻¹ • baseA (puAmalgam h.le) = baseA _ := (mem_stab _).1 (inv_mem hg)
  have hxα : x⁻¹ • baseA (puAmalgam h.le) = baseA _ :=
    (mem_stab _).1 (inv_mem (puTrans_le_stab h.le L _ hx))
  have hadj1 : (puAmalgam h.le).treeGraph.Adj (baseA _)
      (x⁻¹ • g⁻¹ • baseB (puAmalgam h.le)) := by
    have := (adj_smul _ (x⁻¹ * g⁻¹) _ _).2 (adj_baseA_baseB (puAmalgam h.le))
    rwa [mul_smul, hgα, hxα, mul_smul] at this
  have hadj2 : (puAmalgam h.le).treeGraph.Adj (x⁻¹ • g⁻¹ • baseB (puAmalgam h.le)) μ₁ := by
    rw [hμ]
    exact (adj_smul _ x⁻¹ _ _).2 ((adj_smul _ g⁻¹ _ _).2 hβγ)
  have hL' := (S5.rconj_le_rconj_iff (g := x)).2 hL
  rw [S5.rconj_eq_self_of_mem hx, S5.rconj_sup, S5.rconj_sup, S5.rconj_rconj_inv] at hL'
  have hJg : S5.rconj x (S5.rconj g (S5.jOff h.le L (2 ^ k) (baseA _) (baseB _))) =
      S5.jOff h.le L (2 ^ k) μ₁ (x⁻¹ • g⁻¹ • baseB (puAmalgam h.le)) := by
    rw [hμ, S5B.jOff_smul h.le hLn, S5B.jOff_smul h.le hLn, hl.1, S5.rconj, S5.rconj]
  have hZg : S5.rconj x (ZM _ α') = ZM _ (x⁻¹ • α') := by
    rw [S5.rconj, zm_smul]
  rw [hJg, hZg] at hL'
  refine hL'.trans (sup_le (sup_le ?_ hZx) hZ)
  exact jOff_le_normalizer_y h54 h hmin hb4 hd hcμ hmid hadj1 hadj2 hq

end S512T

end CFSG.Quasithin.MS93
