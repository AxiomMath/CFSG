module

public import CFSG.Quasithin.MS93.S5B512

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

namespace S5B

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem uSub_le_bSub_of_forall_normalizes_sel (h32 : S32) (h55 : S55)
    (h : PUHyp M T L) (hmin : PUMin M T L) (hb : 2 < critDist (puAmalgam h.le))
    (hd : S5.IsSp4Data M T L k F a)
    {S : Submodule F (MSP.V4 F) → (puAmalgam h.le).Universal → (puAmalgam h.le).Universal → Prop}
    (h56S : Prod56 h k a S) {α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    (hαβ : geo _ (baseA (puAmalgam h.le)) α' 1 = baseB _) {δ : Vtx (puAmalgam h.le)}
    (hβδ : (puAmalgam h.le).treeGraph.Adj (baseB _) δ) (hδα : δ ≠ baseA _)
    (hn : ∀ μ ∈ lamSel h (2 ^ k) a S α' δ, S5.zHat _ (baseA (puAmalgam h.le)) α' ≤
      Subgroup.normalizer ((ZM _ μ ⊔ XM _ (baseA (puAmalgam h.le)) : Subgroup _) : Set _)) :
    S5.uSub h.le L δ ≤ S5.bSub h.le L (baseA _) := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have h32' := (h32 G M T L h).2.1
  have hα : IsMVtx _ (baseA (puAmalgam h.le)) := isMVtx_baseA _
  have hBy : ∀ y ∈ stab _ (baseA (puAmalgam h.le)),
      S5.uSub h.le L (y⁻¹ • δ) ≤ S5.bSub h.le L (baseA _) →
        S5.uSub h.le L δ ≤ S5.bSub h.le L (baseA _) := by
    intro y hy hle
    rw [← Subgroup.relIndex_eq_one, ← relIndex_bSub_uSub_smul h (inv_mem hy) δ]
    exact Subgroup.relIndex_eq_one.2 hle
  by_cases hcase : ∃ l, S5.Case56 h (2 ^ k) a δ l
  ·
    obtain ⟨l, hJδ, hline, hTl, hJl⟩ := hcase
    obtain ⟨g, hg, x, hx, hconc, hS⟩ := h56S α' hc hαβ l hline hTl hJl
    have hmem₁ : g⁻¹ • δ ∈ lamSel h (2 ^ k) a S α' δ :=
      ⟨g, x, hg, hx, Or.inr ⟨l, ⟨hJδ, hline, hTl, hJl⟩, hconc, hS⟩, Or.inl rfl⟩
    have hmem₂ : x⁻¹ • g⁻¹ • δ ∈ lamSel h (2 ^ k) a S α' δ :=
      ⟨g, x, hg, hx, Or.inr ⟨l, ⟨hJδ, hline, hTl, hJl⟩, hconc, hS⟩, Or.inr rfl⟩
    have hn₁ := hn _ hmem₁
    have hn₂ := hn _ hmem₂
    obtain ⟨-, -, hc6, -⟩ := hconc
    have hxst : x ∈ stab _ (baseA (puAmalgam h.le)) := puTrans_le_stab h.le L _ hx
    obtain ⟨hαβ₁, hβ₁α₁, hα₁, hdα₁⟩ := s57_vert h hβδ hδα hg
    have hxX : (XM _ (baseA (puAmalgam h.le))).map (MulAut.conj x).toMonoidHom =
        XM _ (baseA (puAmalgam h.le)) := by
      rw [← xm_smul, (mem_stab _).1 hxst]
    have h1 : S5.rconj g (S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _)) ≤
        Qv _ (g⁻¹ • baseB (puAmalgam h.le)) := by
      rw [rconj_eq_map, qv_smul]
      exact Subgroup.map_mono (jOff_le_qv h.le L _ _ _)
    have hJn : S5.rconj g (S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _)) ≤
        Subgroup.normalizer ((ZM _ (g⁻¹ • δ) ⊔ XM _ (baseA (puAmalgam h.le)) :
          Subgroup _) : Set _) :=
      le_normalizer_sup (h1.trans ((qv_le_stab_of_adj _ hβ₁α₁).trans
        (stab_le_normalizer_zm _ _))) (h1.trans ((qv_le_stab_of_isMVtx _ hyp
          (isMVtx_baseA _) hαβ₁).trans (stab_le_normalizer_xm _ _)))
    have hZn₂ : S5.rconj x⁻¹ (S5.zHat _ (baseA (puAmalgam h.le)) α') ≤
        Subgroup.normalizer ((ZM _ (g⁻¹ • δ) ⊔ XM _ (baseA (puAmalgam h.le)) :
          Subgroup _) : Set _) := by
      have hW : ZM _ (g⁻¹ • δ) ⊔ XM _ (baseA (puAmalgam h.le)) =
          (ZM _ (x⁻¹ • g⁻¹ • δ) ⊔ XM _ (baseA (puAmalgam h.le))).map
            (MulAut.conj x).toMonoidHom := by
        rw [Subgroup.map_sup, ← zm_smul, smul_inv_smul, hxX]
      rw [rconj_eq_map, inv_inv, hW, normalizer_map_conj, map_conj_le_map_conj_iff]
      exact hn₂
    have hall := hc6.trans (sup_le (sup_le hJn hn₁) hZn₂)
    have hZB := le_bSub_of_xm h hb h32' (isMVtx_baseA _) hdα₁ (zm_le_xm _ hyp hb0 hα₁)
      (zm_le_vv_of_dist hα₁ hdα₁.le) hall
    exact hBy g hg ((uSub_le_zm h.le _).trans hZB)
  ·
    push Not at hcase
    have hne : S5.jOff h.le L (2 ^ k) δ (baseB _) ≠
        S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) ∨
        ∀ l : Submodule F (MSP.V4 F), MSP.IsLine l →
          Qv _ (baseB (puAmalgam h.le)) ≤ S5.vPre h.le a (MSP.stab l) →
          ¬ S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) ≤
            S5.vPre h.le a (MSP.qLine l) := by
      by_cases hJ : S5.jOff h.le L (2 ^ k) δ (baseB _) =
          S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _)
      · exact Or.inr fun l hl hTl hJl => hcase l ⟨hJ, hl, hTl, hJl⟩
      · exact Or.inl hJ
    obtain ⟨g, hg, x, hx, hconc⟩ := h55 G M T L h hmin hb k F _ _ a hd α' hc hαβ δ hβδ hne
    have hmem₁ : g⁻¹ • δ ∈ lamSel h (2 ^ k) a S α' δ :=
      ⟨g, x, hg, hx, Or.inl ⟨hcase, hconc⟩, Or.inl rfl⟩
    obtain ⟨hαβ₁, hβ₁α₁, hα₁, hdα₁⟩ := s57_vert h hβδ hδα hg
    have hT₁ : Qv _ (g⁻¹ • baseB (puAmalgam h.le)) ≤ stab _ (baseA (puAmalgam h.le)) :=
      qv_le_stab_of_isMVtx _ hyp hα hαβ₁
    have hT₁α₁ : Qv _ (g⁻¹ • baseB (puAmalgam h.le)) ≤ stab _ (g⁻¹ • δ) :=
      qv_le_stab_of_adj _ hβ₁α₁
    have hTn : Qv _ (g⁻¹ • baseB (puAmalgam h.le)) ≤ Subgroup.normalizer
        ((ZM _ (g⁻¹ • δ) ⊔ XM _ (baseA (puAmalgam h.le)) : Subgroup _) : Set _) :=
      le_normalizer_sup (hT₁α₁.trans (stab_le_normalizer_zm _ _))
        (hT₁.trans (stab_le_normalizer_xm _ _))
    have hall : stab _ (baseA (puAmalgam h.le)) ≤ Subgroup.normalizer
        ((ZM _ (g⁻¹ • δ) ⊔ XM _ (baseA (puAmalgam h.le)) : Subgroup _) : Set _) := by
      rw [← hconc.1.1]
      exact sup_le hTn (hn _ hmem₁)
    have hZB := le_bSub_of_xm h hb h32' hα hdα₁ (zm_le_xm _ hyp hb0 hα₁)
      (zm_le_vv_of_dist hα₁ hdα₁.le) ((puTrans_le_stab h.le L _).trans hall)
    exact hBy g hg ((uSub_le_zm h.le _).trans hZB)

theorem s512chain_sel (h32 : S32) (h55 : S55) (h58 : S58) (h : PUHyp M T L)
    (hmin : PUMin M T L) (hb4 : critDist (puAmalgam h.le) = 4) (hd : S5.IsSp4Data M T L k F a)
    {S : Submodule F (MSP.V4 F) → (puAmalgam h.le).Universal → (puAmalgam h.le).Universal → Prop}
    (h56S : Prod56 h k a S) {α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    (hαβ : geo _ (baseA (puAmalgam h.le)) α' 1 = baseB _)
    (hone : ∀ μ ∈ lamSel h (2 ^ k) a S α' (geo _ (baseA (puAmalgam h.le)) α' 2),
      S5.zHat _ (baseA (puAmalgam h.le)) α' ≤ Subgroup.normalizer
        (((S5.uSub h.le L μ ⊓ Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2)) ⊔
          XM _ (baseA (puAmalgam h.le)) : Subgroup _) : Set _)) :
    ∃ μ ∈ lamSel h (2 ^ k) a S α' (geo _ (baseA (puAmalgam h.le)) α' 2),
      IsCritical _ μ (geo _ (baseA (puAmalgam h.le)) α' 2) := by
  have hyp := h.hyp20
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  have hd' : (puAmalgam h.le).treeGraph.dist (baseA _) α' = 4 := hc.2.1.trans hb4
  have hα : IsMVtx _ (baseA (puAmalgam h.le)) := isMVtx_baseA _
  have hβδ : (puAmalgam h.le).treeGraph.Adj (baseB _) (geo _ (baseA (puAmalgam h.le)) α' 2) := by
    have := adj_geo _ (u := baseA (puAmalgam h.le)) (w := α') (i := 1) (by omega)
    rwa [hαβ] at this
  have hdδ : (puAmalgam h.le).treeGraph.dist (baseA _) (geo _ (baseA (puAmalgam h.le)) α' 2) = 2 :=
    dist_geo _ (by omega)
  have hδα : geo _ (baseA (puAmalgam h.le)) α' 2 ≠ baseA _ := by
    intro he
    rw [he, SimpleGraph.dist_self] at hdδ
    exact absurd hdδ (by norm_num)
  by_contra hno
  push Not at hno
  apply not_uSub_le_bSub_of_isCritical h58 h hmin hb hd hc
  refine uSub_le_bSub_of_forall_normalizes_sel h32 h55 h hmin hb hd h56S hc hαβ hβδ hδα ?_
  intro μ hμ
  obtain ⟨y, hy, rfl⟩ := exists_mem_stab_of_mem_lamSel hμ
  have hyα : y • baseA (puAmalgam h.le) = baseA _ := (mem_stab _).1 hy
  have hδM : IsMVtx _ (geo _ (baseA (puAmalgam h.le)) α' 2) :=
    isMVtx_geo_two _ hyp h.critDist_pos hc
  have hμM : IsMVtx _ (y • geo _ (baseA (puAmalgam h.le)) α' 2) := (isMVtx_smul _ y _).2 hδM
  have hdyα : (puAmalgam h.le).treeGraph.dist (baseA _)
      (y • geo _ (baseA (puAmalgam h.le)) α' 2) = 2 := by
    have := dist_smul _ y (baseA (puAmalgam h.le)) (geo _ (baseA (puAmalgam h.le)) α' 2)
    rw [hyα] at this
    rw [this, hdδ]
  have hZQ : ZM _ (y • geo _ (baseA (puAmalgam h.le)) α' 2) ≤
      Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2) := by
    by_contra hZ
    have htri := dist_triangle _ (y • geo _ (baseA (puAmalgam h.le)) α' 2) (baseA _)
      (geo _ (baseA (puAmalgam h.le)) α' 2)
    have e1 : (puAmalgam h.le).treeGraph.dist (y • geo _ (baseA (puAmalgam h.le)) α' 2)
        (baseA _) = 2 := by
      rw [SimpleGraph.dist_comm]
      exact hdyα
    have hge : critDist (puAmalgam h.le) ≤ (puAmalgam h.le).treeGraph.dist
        (y • geo _ (baseA (puAmalgam h.le)) α' 2) (geo _ (baseA (puAmalgam h.le)) α' 2) := by
      by_contra hlt
      exact hZ (zm_le_qv_of_dist_lt _ hμM (by omega))
    exact hno _ hμ ⟨hμM, by omega, hZ⟩
  have key := hone _ hμ
  have hU : S5.uSub h.le L (y • geo _ (baseA (puAmalgam h.le)) α' 2) ⊓
      Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2) =
      S5.uSub h.le L (y • geo _ (baseA (puAmalgam h.le)) α' 2) :=
    inf_eq_left.2 ((uSub_le_zm h.le _).trans hZQ)
  have hadj₁ : (puAmalgam h.le).treeGraph.Adj (baseA _) (y • baseB (puAmalgam h.le)) := by
    rw [← hyα]
    exact (adj_smul _ y _ _).2 (adj_baseA_baseB _)
  have hadj₂ : (puAmalgam h.le).treeGraph.Adj (y • geo _ (baseA (puAmalgam h.le)) α' 2)
      (y • baseB (puAmalgam h.le)) := (adj_smul _ y _ _).2 hβδ.symm
  have hZX : ZM _ (y • geo _ (baseA (puAmalgam h.le)) α' 2) ⊔ XM _ (baseA (puAmalgam h.le)) =
      S5.uSub h.le L (y • geo _ (baseA (puAmalgam h.le)) α' 2) ⊔
        XM _ (baseA (puAmalgam h.le)) := by
    rw [zm_eq_zh_sup_uSub h hμM hadj₂]
    have hZβ : ZH _ (y • baseB (puAmalgam h.le)) ≤ XM _ (baseA (puAmalgam h.le)) :=
      (zh_le_zm _ hadj₁).trans (zm_le_xm _ hyp h.critDist_pos hα)
    exact le_antisymm (sup_le (sup_le (hZβ.trans le_sup_right) le_sup_left) le_sup_right)
      (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
  rw [hZX, ← hU]
  exact key

end S5B

end CFSG.Quasithin.MS93
