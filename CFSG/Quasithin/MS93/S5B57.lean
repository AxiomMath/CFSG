module

public import CFSG.Quasithin.MS93.S5BAux
public import CFSG.Quasithin.MS93.S5BL2
public import CFSG.Quasithin.MS93.S33II2
public import CFSG.Quasithin.MS93.S5BLamSel
public import CFSG.Quasithin.MS93.S5Q2Idx
public import CFSG.Quasithin.MS93.S5BJ

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Pointwise

namespace S5B

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

section Facts

theorem zm_le_vv_of_dist {A B : Type} {C : Type} [Group A] [Group C] [Group B]
    {X : GoldAmalgam A C B} {α μ : Vtx X} (hμ : IsMVtx X μ) (hd : X.treeGraph.dist α μ ≤ 2) :
    ZM X μ ≤ Vv X α := by
  rw [← zv_of_isMVtx X hμ]
  exact le_iSup₂_of_le (f := fun ρ (_ : ρ ∈ {ρ : Vtx X | X.treeGraph.dist α ρ ≤ 2}) => Zv X ρ)
    μ hd le_rfl

theorem relIndex_bSub_uSub_smul (h : PUHyp M T L) {g : (puAmalgam h.le).Universal}
    (hg : g ∈ stab _ (baseA (puAmalgam h.le))) (δ : Vtx (puAmalgam h.le)) :
    (S5.bSub h.le L (baseA _)).relIndex (S5.uSub h.le L (g • δ)) =
      (S5.bSub h.le L (baseA _)).relIndex (S5.uSub h.le L δ) := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have hgα : g • baseA (puAmalgam h.le) = baseA _ := (mem_stab _).1 hg
  calc (S5.bSub h.le L (baseA _)).relIndex (S5.uSub h.le L (g • δ)) =
      (S5.bSub h.le L (g • baseA _)).relIndex (S5.uSub h.le L (g • δ)) := by rw [hgα]
    _ = _ := by
      rw [bSub_smul h.le hLn, uSub_smul h.le hLn,
        Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]

omit [Finite G] in
theorem uSub_le_zm (hTM : T ≤ M) (δ : Vtx (puAmalgam hTM)) :
    S5.uSub hTM L δ ≤ ZM _ δ :=
  commutator_le_left_of_le_normalizer ((puTrans_le_stab hTM L δ).trans
    (stab_le_normalizer_zm _ _))

theorem crit_facts (h : PUHyp M T L) {α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical _ (baseA (puAmalgam h.le)) α') :
    ZM _ α' ≤ stab _ (baseA (puAmalgam h.le)) ∧ XM _ α' ≤ stab _ (baseA (puAmalgam h.le)) ∧
      S5.zHat _ (baseA (puAmalgam h.le)) α' ≤ stab _ (baseA (puAmalgam h.le)) ∧
      critR _ (baseA (puAmalgam h.le)) α' ≤ XM _ (baseA (puAmalgam h.le)) ∧
      ⁅XM (puAmalgam h.le) (baseA _), XM (puAmalgam h.le) α'⁆ ≤ XM _ (baseA (puAmalgam h.le)) ∧
      Qv _ (geo _ α' (baseA (puAmalgam h.le)) 2) ≤ Qv _ (geo _ α' (baseA (puAmalgam h.le)) 1) := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hC := h.centHyp
  have hα : IsMVtx _ (baseA (puAmalgam h.le)) := isMVtx_baseA _
  have hα' : IsMVtx _ α' := hc.isMVtx_right _ hyp
  have hcr' := ms22_iii _ hyp hb0 hC hc
  have hb2 := two_le_critDist _ hyp hb0
  have hd := hc.2.1
  have hX'st : XM _ α' ≤ stab _ (baseA (puAmalgam h.le)) :=
    xm_le_stab_of_isCritical _ hyp hb0 hC hcr'
  have hZ'st : ZM _ α' ≤ stab _ (baseA (puAmalgam h.le)) :=
    (zm_le_xm _ hyp hb0 hα').trans hX'st
  have hRZ : critR _ (baseA (puAmalgam h.le)) α' ≤ ZM _ (baseA (puAmalgam h.le)) :=
    commutator_le_left_of_le_normalizer (hZ'st.trans (stab_le_normalizer_zm _ _))
  refine ⟨hZ'st, hX'st, (inf_le_left.trans hZ'st), hRZ.trans (zm_le_xm _ hyp hb0 hα),
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hX'st.trans (stab_le_normalizer_xm _ _)), ?_⟩
  have hadj : (puAmalgam h.le).treeGraph.Adj (geo _ α' (baseA (puAmalgam h.le)) 1)
      (geo _ α' (baseA _) 2) := adj_geo _ (i := 1) (by rw [SimpleGraph.dist_comm, hd]; omega)
  exact qv_le_qv _ hyp (isMVtx_geo_two _ hyp hb0 hcr') hadj.symm

theorem zm_le_centralizer_critR (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    {α' μ : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    (hμ : IsMVtx _ μ) (hdμ : (puAmalgam h.le).treeGraph.dist (baseA _) μ = 2) :
    ZM _ μ ≤ Qv _ (baseA (puAmalgam h.le)) ∧
      ZM _ μ ≤ Subgroup.centralizer (critR _ (baseA (puAmalgam h.le)) α' : Set _) := by
  have hZQ : ZM _ μ ≤ Qv _ (baseA (puAmalgam h.le)) :=
    zm_le_qv_of_dist_lt _ hμ (by rw [SimpleGraph.dist_comm, hdμ]; exact hb)
  refine ⟨hZQ, hZQ.trans ((qv_le_centralizer_xm _ _).trans (Subgroup.centralizer_le ?_))⟩
  exact (crit_facts h hc).2.2.2.1

end Facts

theorem s57_s33 (h32 : S32) (hX2 : S33.S33X52) (h52 : S52) (h : PUHyp M T L)
    (hmin : PUMin M T L)
    (hb : 2 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a)
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    {μ : Vtx (puAmalgam h.le)} (hμ : IsMVtx _ μ)
    (hdμ : (puAmalgam h.le).treeGraph.dist (baseA _) μ = 2)
    (hZμ : ZM _ μ ≤ Qv _ (geo _ α' (baseA (puAmalgam h.le)) 2))
    (hn : ¬ S5.zHat _ (baseA (puAmalgam h.le)) α' ≤
      Subgroup.normalizer ((ZM _ μ ⊔ XM _ (baseA (puAmalgam h.le)) : Subgroup _) : Set _)) :
    (Qv _ α').relIndex (ZM _ (baseA (puAmalgam h.le))) = 2 ^ k ∧
      Xq M = Uq M T L ⊔ Zq M L ∧
      Nat.card ↥⁅ZM _ μ, critA _ (baseA (puAmalgam h.le)) α'⁆ = 2 ^ k ∧
      ⁅ZM _ μ, critA _ (baseA (puAmalgam h.le)) α'⁆ ≤
        critR _ (baseA (puAmalgam h.le)) α' ⊔ stabCenter _ α' := by
  obtain ⟨-, -, hZhst, hRX, hXX, hQQ⟩ := crit_facts h hc
  obtain ⟨hZQ, hZR⟩ := zm_le_centralizer_critR h hb hc hμ hdμ
  have hZhX : S5.zHat _ (baseA (puAmalgam h.le)) α' ≤
      Subgroup.normalizer (XM _ (baseA (puAmalgam h.le)) : Set _) :=
    hZhst.trans (stab_le_normalizer_xm _ _)
  have hAQ : critA _ (baseA (puAmalgam h.le)) α' ≤ Qv _ (baseA (puAmalgam h.le)) := inf_le_right
  have hQμ : Qv _ (baseA (puAmalgam h.le)) ≤ Subgroup.normalizer (ZM _ μ : Set _) := by
    have hαγ : (puAmalgam h.le).treeGraph.Adj (baseA _) (geo _ (baseA (puAmalgam h.le)) μ 1) :=
      adj_geo_one _ (by rw [hdμ]; norm_num)
    have hγμ : (puAmalgam h.le).treeGraph.Adj (geo _ (baseA (puAmalgam h.le)) μ 1) μ := by
      have := adj_geo _ (u := baseA (puAmalgam h.le)) (w := μ) (i := 1) (by rw [hdμ]; norm_num)
      rwa [show (1 + 1 : ℕ) = 2 from rfl, ← hdμ, geo_dist] at this
    exact (qv_le_qv _ h.hyp20 (isMVtx_baseA _) hαγ).trans
      ((qv_le_stab_of_adj _ hγμ).trans (stab_le_normalizer_zm _ _))
  have hAZ : ⁅critA _ (baseA (puAmalgam h.le)) α', ZM _ μ⁆ ≤ ZM _ μ := by
    rw [Subgroup.commutator_comm]
    exact commutator_le_left_of_le_normalizer (hAQ.trans hQμ)
  have hY : ¬ ⁅ZM (puAmalgam h.le) α', ZM _ μ⁆ ≤
      ⁅XM (puAmalgam h.le) (baseA _), XM (puAmalgam h.le) α'⁆ ⊔
        ⁅critA (puAmalgam h.le) (baseA _) α', ZM _ μ⁆ := by
    intro hle
    apply hn
    refine le_normalizer_sup_of_commutator_le hZhX ?_
    rw [Subgroup.commutator_comm]
    refine ((Subgroup.commutator_mono inf_le_left le_rfl).trans hle).trans
      (sup_le (hXX.trans le_sup_right) (hAZ.trans le_sup_left))
  have hYZ : ¬ ⁅ZM _ μ, S5.zHat _ (baseA (puAmalgam h.le)) α'⁆ ≤
      critR _ (baseA (puAmalgam h.le)) α' := by
    intro hle
    exact hn (le_normalizer_sup_of_commutator_le hZhX (hle.trans (hRX.trans le_sup_right)))
  have hZT := hZμ.trans hQQ
  obtain ⟨h1, h3, h4⟩ := s33ii2_of' hX2 h hd (h32 G M T L h).2.1 hc hZT hZR
    (hZQ.trans (qv_le_centralizer_xm _ _)) hY hYZ
  refine ⟨h1, h3, h4 ?_⟩
  have h52iii := (h52 G M T L h hmin hb k F _ _ a hd α' hc).2.2.2
  have hle : ZM _ μ ≤ Vv _ (baseA (puAmalgam h.le)) ⊓
      Qv _ (geo _ α' (baseA (puAmalgam h.le)) 2) :=
    le_inf (zm_le_vv_of_dist hμ hdμ.le) hZμ
  refine le_bot_iff.1 ?_
  rw [← h52iii]
  exact Subgroup.commutator_mono (Subgroup.commutator_mono le_rfl hle) hle

theorem finite_of_le_qv (h : PUHyp M T L) {μ : Vtx (puAmalgam h.le)} (hμ : IsMVtx _ μ)
    {K : Subgroup (puAmalgam h.le).Universal} (hK : K ≤ Qv _ μ) : Finite K := by
  obtain ⟨γ, hγ⟩ := exists_adj _ μ
  have hγM : ¬ IsMVtx _ γ := (isMVtx_iff_of_adj _ hγ).1 hμ
  have : Finite ↥(Qv (puAmalgam h.le) γ) := finite_qv _ h.hyp20 hγM
  have hKγ : K ≤ Qv _ γ := hK.trans (qv_le_qv _ h.hyp20 hμ hγ)
  exact Finite.of_injective (Subgroup.inclusion hKγ) (Subgroup.inclusion_injective hKγ)

theorem relIndex_le_of_inf_centralizer_le (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {μ : Vtx (puAmalgam h.le)} (hμ : IsMVtx _ μ) {E : Subgroup (puAmalgam h.le).Universal}
    (hE : E ≤ stab _ μ) (hE2 : IsPGroup 2 E) (hEQ : ¬ E ≤ Qv _ μ)
    (hcard : Nat.card ↥⁅S5.uSub h.le L μ, E⁆ ≤ 2 ^ k) {B : Subgroup (puAmalgam h.le).Universal}
    (hB : S5.uSub h.le L μ ⊓ Subgroup.centralizer (E : Set _) ≤ B) :
    B.relIndex (S5.uSub h.le L μ) ≤ 2 ^ k := by
  have htv := (tv_card h hd hμ hE hE2 hEQ hcard).2
  have hfin : Finite ↥(S5.uSub h.le L μ) := finite_of_le_qv h hμ
    ((uSub_le_zm h.le μ).trans (zm_le_qv_self _ hμ h.critDist_pos))
  have hle : Subgroup.centralizer (E : Set (puAmalgam h.le).Universal) ⊓ S5.uSub h.le L μ ≤
      B ⊓ S5.uSub h.le L μ := fun x hx => ⟨hB ⟨hx.2, hx.1⟩, hx.2⟩
  calc B.relIndex (S5.uSub h.le L μ) = (B ⊓ S5.uSub h.le L μ).relIndex (S5.uSub h.le L μ) :=
        (Subgroup.inf_relIndex_right _ _).symm
    _ ≤ (Subgroup.centralizer (E : Set (puAmalgam h.le).Universal) ⊓
          S5.uSub h.le L μ).relIndex (S5.uSub h.le L μ) := by
        refine Subgroup.relIndex_le_of_le_left hle ?_
        rw [Subgroup.relIndex]
        exact Subgroup.index_ne_zero_of_finite
    _ = 2 ^ k := by rw [Subgroup.inf_relIndex_right, htv]

theorem critA_facts (h : PUHyp M T L) {α' μ : Vtx (puAmalgam h.le)} (hμ : IsMVtx _ μ)
    (hdμ : (puAmalgam h.le).treeGraph.dist (baseA _) μ = 2)
    (hcard : Nat.card ↥⁅ZM _ μ, critA _ (baseA (puAmalgam h.le)) α'⁆ ≤ 2 ^ k)
    (hne : ⁅ZM _ μ, critA _ (baseA (puAmalgam h.le)) α'⁆ ≠ ⊥) :
    critA _ (baseA (puAmalgam h.le)) α' ≤ stab _ μ ∧
      IsPGroup 2 (critA _ (baseA (puAmalgam h.le)) α') ∧
      ¬ critA _ (baseA (puAmalgam h.le)) α' ≤ Qv _ μ ∧
      Nat.card ↥⁅S5.uSub h.le L μ, critA _ (baseA (puAmalgam h.le)) α'⁆ ≤ 2 ^ k := by
  have hyp := h.hyp20
  have hαγ : (puAmalgam h.le).treeGraph.Adj (baseA _) (geo _ (baseA (puAmalgam h.le)) μ 1) :=
    adj_geo_one _ (by rw [hdμ]; norm_num)
  have hγμ : (puAmalgam h.le).treeGraph.Adj (geo _ (baseA (puAmalgam h.le)) μ 1) μ := by
    have := adj_geo _ (u := baseA (puAmalgam h.le)) (w := μ) (i := 1) (by rw [hdμ]; norm_num)
    rwa [show (1 + 1 : ℕ) = 2 from rfl, ← hdμ, geo_dist] at this
  have hγ : ¬ IsMVtx _ (geo _ (baseA (puAmalgam h.le)) μ 1) :=
    (isMVtx_iff_of_adj _ hαγ).1 (isMVtx_baseA _)
  have hAT : critA _ (baseA (puAmalgam h.le)) α' ≤ Qv _ (geo _ (baseA (puAmalgam h.le)) μ 1) :=
    inf_le_right.trans (qv_le_qv _ hyp (isMVtx_baseA _) hαγ)
  refine ⟨hAT.trans (qv_le_stab_of_adj _ hγμ), (isPGroup_qv _ hyp hγ).to_le hAT, ?_, ?_⟩
  · intro hAQ
    apply hne
    refine le_bot_iff.1 ?_
    rw [← commutator_zm_qv _ hyp hμ]
    exact Subgroup.commutator_mono le_rfl hAQ
  · refine le_trans ?_ hcard
    have : Finite ↥⁅ZM (puAmalgam h.le) μ, critA _ (baseA (puAmalgam h.le)) α'⁆ :=
      finite_of_le_qv h hμ ((commutator_le_left_of_le_normalizer
        (inf_le_right.trans ((qv_le_qv _ hyp (isMVtx_baseA _) hαγ).trans
          ((qv_le_stab_of_adj _ hγμ).trans (stab_le_normalizer_zm _ _))))).trans
        (zm_le_qv_self _ hμ h.critDist_pos))
    exact Subgroup.card_le_of_le (Subgroup.commutator_mono (uSub_le_zm h.le μ) le_rfl)

omit [Finite G] in
theorem commutator_ne_bot_of_card (hd : S5.IsSp4Data M T L k F a) {G' : Type*} [Group G']
    {K : Subgroup G'}
    (hK : Nat.card K = 2 ^ k) : K ≠ ⊥ := by
  rintro rfl
  rw [Subgroup.card_bot] at hK
  have := Nat.one_lt_two_pow (show k ≠ 0 by have := hd.1; omega)
  omega

theorem s57_finish (h32 : S32) (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    (hd : S5.IsSp4Data M T L k F a) {α' μ : Vtx (puAmalgam h.le)} (hμ : IsMVtx _ μ)
    (hdμ : (puAmalgam h.le).treeGraph.dist (baseA _) μ = 2)
    (hcard : Nat.card ↥⁅ZM _ μ, critA _ (baseA (puAmalgam h.le)) α'⁆ = 2 ^ k)
    (hn : puTrans h.le L (baseA _) ≤ Subgroup.normalizer
      ((S5.uSub h.le L μ ⊓ Subgroup.centralizer (critA _ (baseA (puAmalgam h.le)) α' : Set _) ⊔
        XM _ (baseA (puAmalgam h.le)) : Subgroup _) : Set _)) :
    (S5.bSub h.le L (baseA _)).relIndex (S5.uSub h.le L μ) ≤ 2 ^ k := by
  have h32' := (h32 G M T L h).2.1
  obtain ⟨hAst, hA2, hAQ, hAc⟩ :=
    critA_facts h hμ hdμ hcard.le (commutator_ne_bot_of_card hd hcard)
  have hYZ : S5.uSub h.le L μ ⊓ Subgroup.centralizer
      (critA _ (baseA (puAmalgam h.le)) α' : Set _) ≤ ZM _ μ :=
    inf_le_left.trans (uSub_le_zm h.le μ)
  have hB := le_bSub_of_xm h hb h32' (isMVtx_baseA _) hdμ
    (hYZ.trans (zm_le_xm _ h.hyp20 h.critDist_pos hμ)) (hYZ.trans (zm_le_vv_of_dist hμ hdμ.le)) hn
  exact relIndex_le_of_inf_centralizer_le h hd hμ hAst hA2 hAQ hAc hB

theorem s57_case55 (h32 : S32) (hX2 : S33.S33X52) (h52 : S52) (h54 : S54)
    (h : PUHyp M T L) (hmin : PUMin M T L) (hb : 2 < critDist (puAmalgam h.le))
    (hd : S5.IsSp4Data M T L k F a) {α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical _ (baseA (puAmalgam h.le)) α') {δ : Vtx (puAmalgam h.le)}
    (hβδ : (puAmalgam h.le).treeGraph.Adj (baseB _) δ) {g x : (puAmalgam h.le).Universal}
    (hg : g ∈ stab _ (baseA (puAmalgam h.le))) (hconc : S5.Concl55 h (2 ^ k) α' δ g x)
    (hZ₁ : ZM _ (g⁻¹ • δ) ≤ Qv _ (geo _ α' (baseA (puAmalgam h.le)) 2)) :
    (S5.bSub h.le L (baseA _)).relIndex (S5.uSub h.le L δ) ≤ 2 ^ k := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have h32' := (h32 G M T L h).2.1
  have hα : IsMVtx _ (baseA (puAmalgam h.le)) := isMVtx_baseA _
  have hαβ := adj_baseA_baseB (puAmalgam h.le)
  have hδ : IsMVtx _ δ := by
    have := isMVtx_iff_of_adj _ hβδ
    have hβ := not_isMVtx_baseB (puAmalgam h.le)
    tauto
  have hg' : g⁻¹ ∈ stab _ (baseA (puAmalgam h.le)) := inv_mem hg
  have hgα : g⁻¹ • baseA (puAmalgam h.le) = baseA _ := (mem_stab _).1 hg'
  rw [← relIndex_bSub_uSub_smul h hg' δ]
  by_contra hq
  push Not at hq
  have hBα : S5.uSub h.le L (baseA (puAmalgam h.le)) ≤ S5.bSub h.le L (baseA _) := by
    intro u hu
    refine Subgroup.subset_closure ⟨zm_le_vv_of_dist hα (by simp) (uSub_le_zm h.le _ hu),
      fun y hy => ?_⟩
    exact commutator_le_left_of_le_normalizer ((puTrans_le_stab h.le L _).trans
      (stab_le_normalizer_zm _ _)) (Subgroup.commutator_mem_commutator (uSub_le_zm h.le _ hu) hy)
  have hδα : δ ≠ baseA _ := by
    rintro rfl
    rw [hgα, Subgroup.relIndex_eq_one.2 hBα] at hq
    have := Nat.one_le_two_pow (n := k)
    omega
  have hαβ₁ : (puAmalgam h.le).treeGraph.Adj (baseA _) (g⁻¹ • baseB (puAmalgam h.le)) := by
    rw [← hgα]
    exact (adj_smul _ g⁻¹ _ _).2 hαβ
  have hβ₁α₁ : (puAmalgam h.le).treeGraph.Adj (g⁻¹ • baseB (puAmalgam h.le)) (g⁻¹ • δ) :=
    (adj_smul _ g⁻¹ _ _).2 hβδ
  have hα₁ : IsMVtx _ (g⁻¹ • δ) := (isMVtx_smul _ g⁻¹ δ).2 hδ
  have hdα₁ : (puAmalgam h.le).treeGraph.dist (baseA _) (g⁻¹ • δ) = 2 := by
    rw [← hgα, dist_smul]
    exact dist_eq_two_of_adj_adj _ hαβ hβδ (Ne.symm hδα)
  have hT₁ : Qv _ (g⁻¹ • baseB (puAmalgam h.le)) ≤ stab _ (baseA (puAmalgam h.le)) :=
    qv_le_stab_of_isMVtx _ hyp hα hαβ₁
  have hT₁α₁ : Qv _ (g⁻¹ • baseB (puAmalgam h.le)) ≤ stab _ (g⁻¹ • δ) :=
    qv_le_stab_of_adj _ hβ₁α₁
  have hBne : ¬ S5.uSub h.le L (g⁻¹ • δ) ≤ S5.bSub h.le L (baseA _) := by
    intro hle
    rw [Subgroup.relIndex_eq_one.2 hle] at hq
    have := Nat.one_le_two_pow (n := k)
    omega
  have hn : ¬ S5.zHat _ (baseA (puAmalgam h.le)) α' ≤ Subgroup.normalizer
      ((ZM _ (g⁻¹ • δ) ⊔ XM _ (baseA (puAmalgam h.le)) : Subgroup _) : Set _) := by
    intro hZ
    apply hBne
    have hTn : Qv _ (g⁻¹ • baseB (puAmalgam h.le)) ≤ Subgroup.normalizer
        ((ZM _ (g⁻¹ • δ) ⊔ XM _ (baseA (puAmalgam h.le)) : Subgroup _) : Set _) :=
      le_normalizer_sup (hT₁α₁.trans (stab_le_normalizer_zm _ _))
        (hT₁.trans (stab_le_normalizer_xm _ _))
    have hall : stab _ (baseA (puAmalgam h.le)) ≤ Subgroup.normalizer
        ((ZM _ (g⁻¹ • δ) ⊔ XM _ (baseA (puAmalgam h.le)) : Subgroup _) : Set _) := by
      rw [← hconc.1.1]
      exact sup_le hTn hZ
    have := le_bSub_of_xm h hb h32' hα hdα₁ (zm_le_xm _ hyp hb0 hα₁)
      (zm_le_vv_of_dist hα₁ hdα₁.le) ((puTrans_le_stab h.le L _).trans hall)
    exact (uSub_le_zm h.le _).trans this
  obtain ⟨-, hXU, hcard, -⟩ := s57_s33 h32 hX2 h52 h hmin hb hd hc hα₁ hdα₁ hZ₁ hn
  have hXZ' : XM _ (baseA (puAmalgam h.le)) = S5.uSub h.le L (baseA _) ⊔
      XM _ (baseA (puAmalgam h.le)) ⊓
        Subgroup.centralizer (puTrans h.le L (baseA _) : Set (puAmalgam h.le).Universal) := by
    rw [uSub_baseA h, puTrans_L_baseA h, xm_baseA_eq h, ← imM_inf_centralizer h.le _ h.L_le,
      ← imM_sup_of_le h.le (Uq_le h.L_le) (inf_le_left.trans (Xq_le M))]
    conv_lhs => rw [hXU]
  have hL : puTrans h.le L (baseA _) ≤
      S5.jOff h.le L (2 ^ k) (g⁻¹ • δ) (g⁻¹ • baseB (puAmalgam h.le)) ⊔
        S5.zHat _ (baseA (puAmalgam h.le)) α' := by
    rcases hconc.2.2 with h1 | h2
    · exact h1.trans inf_le_left
    · exact absurd hXZ' h2.2.2
  obtain ⟨hAst, hA2, hAQ, hAc⟩ :=
    critA_facts h hα₁ hdα₁ hcard.le (commutator_ne_bot_of_card hd hcard)
  obtain ⟨-, -, hZhst, hRX, hXX, hQQ⟩ := crit_facts h hc
  obtain ⟨-, hZR⟩ := zm_le_centralizer_critR h hb hc hα₁ hdα₁
  have hAT : critA _ (baseA (puAmalgam h.le)) α' ≤ Qv _ (g⁻¹ • baseB (puAmalgam h.le)) :=
    inf_le_right.trans (qv_le_qv _ hyp hα hαβ₁)
  set Y := S5.uSub h.le L (g⁻¹ • δ) ⊓
    Subgroup.centralizer (critA _ (baseA (puAmalgam h.le)) α' : Set _) with hYdef
  have hYZ : Y ≤ ZM _ (g⁻¹ • δ) := inf_le_left.trans (uSub_le_zm h.le _)
  have hJn : S5.jOff h.le L (2 ^ k) (g⁻¹ • δ) (g⁻¹ • baseB (puAmalgam h.le)) ≤
      Subgroup.normalizer ((Y ⊔ XM _ (baseA (puAmalgam h.le)) : Subgroup _) : Set _) :=
    le_normalizer_sup (jOff_le_normalizer h hmin hb hd h54 hα₁ hβ₁α₁.symm hAT hAQ hAc)
      ((jOff_le_qv h.le L _ _ _).trans (hT₁.trans (stab_le_normalizer_xm _ _)))
  have hZn : S5.zHat _ (baseA (puAmalgam h.le)) α' ≤
      Subgroup.normalizer ((Y ⊔ XM _ (baseA (puAmalgam h.le)) : Subgroup _) : Set _) := by
    refine le_normalizer_sup_of_commutator_le (hZhst.trans (stab_le_normalizer_xm _ _)) ?_
    have hAY : ⁅critA _ (baseA (puAmalgam h.le)) α', Y⁆ = ⊥ := by
      rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact inf_le_right
    exact (commutator_zHat_le' h hd hc ((hYZ.trans hZ₁).trans hQQ) (hYZ.trans hZR) hAY).trans
      (sup_le (hXX.trans le_sup_right) (hRX.trans le_sup_right))
  exact absurd (s57_finish h32 h hb hd hα₁ hdα₁ hcard (hL.trans (sup_le hJn hZn))) (not_le.2 hq)

theorem commutator_sup_le_of_le {Γ : Type*} [Group Γ] {H₁ H₂ A N : Subgroup Γ}
    (hN₁ : H₁ ≤ Subgroup.normalizer (N : Set Γ)) (hN₂ : H₂ ≤ Subgroup.normalizer (N : Set Γ))
    (h₁ : ⁅H₁, A⁆ ≤ N) (h₂ : ⁅H₂, A⁆ ≤ N) : ⁅H₁ ⊔ H₂, A⁆ ≤ N := by
  let S : Subgroup Γ :=
    { carrier := {y | y ∈ Subgroup.normalizer (N : Set Γ) ∧ ∀ x ∈ A, ⁅y, x⁆ ∈ N}
      one_mem' := ⟨one_mem _, fun x _ => by simp⟩
      mul_mem' := by
        rintro y₁ y₂ ⟨hy₁, h₁⟩ ⟨hy₂, h₂⟩
        refine ⟨mul_mem hy₁ hy₂, fun x hx => ?_⟩
        have e : ⁅y₁ * y₂, x⁆ = (y₁ * ⁅y₂, x⁆ * y₁⁻¹) * ⁅y₁, x⁆ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact mul_mem ((Subgroup.mem_normalizer_iff.1 hy₁ _).1 (h₂ x hx)) (h₁ x hx)
      inv_mem' := by
        rintro y ⟨hy, h₁⟩
        refine ⟨inv_mem hy, fun x hx => ?_⟩
        have e : ⁅y⁻¹, x⁆ = y⁻¹ * ⁅y, x⁆⁻¹ * y := by
          simp only [commutatorElement_def]
          group
        rw [e]
        have := (Subgroup.mem_normalizer_iff.1 (inv_mem hy) _).1 (inv_mem (h₁ x hx))
        simpa using this }
  have hS : H₁ ⊔ H₂ ≤ S := sup_le
    (fun y hy => ⟨hN₁ hy, fun x hx => h₁ (Subgroup.commutator_mem_commutator hy hx)⟩)
    (fun y hy => ⟨hN₂ hy, fun x hx => h₂ (Subgroup.commutator_mem_commutator hy hx)⟩)
  rw [Subgroup.commutator_le]
  intro y hy x hx
  exact (hS hy).2 x hx

theorem s57_vert (h : PUHyp M T L) {δ : Vtx (puAmalgam h.le)}
    (hβδ : (puAmalgam h.le).treeGraph.Adj (baseB _) δ) (hδα : δ ≠ baseA _)
    {y : (puAmalgam h.le).Universal} (hy : y ∈ stab _ (baseA (puAmalgam h.le))) :
    (puAmalgam h.le).treeGraph.Adj (baseA _) (y⁻¹ • baseB (puAmalgam h.le)) ∧
      (puAmalgam h.le).treeGraph.Adj (y⁻¹ • baseB (puAmalgam h.le)) (y⁻¹ • δ) ∧
      IsMVtx _ (y⁻¹ • δ) ∧ (puAmalgam h.le).treeGraph.dist (baseA _) (y⁻¹ • δ) = 2 := by
  have hαβ := adj_baseA_baseB (puAmalgam h.le)
  have hδ : IsMVtx _ δ := by
    have := isMVtx_iff_of_adj _ hβδ
    have hβ := not_isMVtx_baseB (puAmalgam h.le)
    tauto
  have hyα : y⁻¹ • baseA (puAmalgam h.le) = baseA _ := (mem_stab _).1 (inv_mem hy)
  refine ⟨?_, (adj_smul _ y⁻¹ _ _).2 hβδ, (isMVtx_smul _ y⁻¹ δ).2 hδ, ?_⟩
  · rw [← hyα]
    exact (adj_smul _ y⁻¹ _ _).2 hαβ
  · rw [← hyα, dist_smul]
    exact dist_eq_two_of_adj_adj _ hαβ hβδ (Ne.symm hδα)

omit [Finite G] in
theorem s57_comm_conj (hTM : T ≤ M) {δ : Vtx (puAmalgam hTM)}
    {Q : Subgroup (puAmalgam hTM).Universal}
    (hcomm : ⁅ZM _ δ, Qv _ (baseA (puAmalgam hTM))⁆ ≤ XM _ (baseA (puAmalgam hTM)) ⊓
      Subgroup.centralizer (Q : Set _)) {y : (puAmalgam hTM).Universal}
    (hy : y ∈ stab _ (baseA (puAmalgam hTM))) :
    ⁅ZM _ (y⁻¹ • δ), Qv _ (baseA (puAmalgam hTM))⁆ ≤ XM _ (baseA (puAmalgam hTM)) ⊓
      Subgroup.centralizer (S5.rconj y Q : Set (puAmalgam hTM).Universal) := by
  have hyα : y⁻¹ • baseA (puAmalgam hTM) = baseA _ := (mem_stab _).1 (inv_mem hy)
  have h1 := Subgroup.map_mono (f := (MulAut.conj y⁻¹).toMonoidHom) hcomm
  rw [Subgroup.map_commutator, ← zm_smul, ← qv_smul, hyα,
    Subgroup.map_inf _ _ _ (MulAut.conj y⁻¹).injective, ← xm_smul, hyα,
    ← PU.centralizer_map_mulEquiv] at h1
  exact h1

theorem s57_sub2 (hXU : Xq M = Uq M T L ⊔ Zq M L) (h52 : S52) (h : PUHyp M T L)
    (hmin : PUMin M T L)
    (hb : 2 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a)
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    {μ₁ μ₂ : Vtx (puAmalgam h.le)} (hμ₁ : IsMVtx _ μ₁)
    (hd₁ : (puAmalgam h.le).treeGraph.dist (baseA _) μ₁ = 2) (hμ₂ : IsMVtx _ μ₂)
    (hd₂ : (puAmalgam h.le).treeGraph.dist (baseA _) μ₂ = 2)
    (hZ₁ : ZM _ μ₁ ≤ Qv _ (geo _ α' (baseA (puAmalgam h.le)) 2))
    (hZ₂ : ZM _ μ₂ ≤ Qv _ (geo _ α' (baseA (puAmalgam h.le)) 2))
    (hn : ¬ S5.zHat _ (baseA (puAmalgam h.le)) α' ≤ Subgroup.normalizer
      ((ZM _ μ₁ ⊔ XM _ (baseA (puAmalgam h.le)) : Subgroup _) : Set _))
    (hcard₁ : Nat.card ↥⁅ZM _ μ₁, critA _ (baseA (puAmalgam h.le)) α'⁆ = 2 ^ k)
    (hX₁ : ⁅ZM _ μ₁, Qv _ (baseA (puAmalgam h.le))⁆ ≤ XM _ (baseA (puAmalgam h.le)))
    (hX₂ : ⁅ZM _ μ₂, Qv _ (baseA (puAmalgam h.le))⁆ ≤ XM _ (baseA (puAmalgam h.le)))
    (h0 : ⁅ZM _ μ₂, critA _ (baseA (puAmalgam h.le)) α'⁆ ≠ ⊥) :
    ⁅S5.uSub h.le L μ₂, critA _ (baseA (puAmalgam h.le)) α'⁆ =
        ⁅ZM _ μ₁, critA _ (baseA (puAmalgam h.le)) α'⁆ ∧
      critA _ (baseA (puAmalgam h.le)) α' ≤ stab _ μ₂ := by
  obtain ⟨-, -, hZhst, hRX, hXX, hQQ⟩ := crit_facts h hc
  obtain ⟨hZ₁Q, hZ₁R⟩ := zm_le_centralizer_critR h hb hc hμ₁ hd₁
  obtain ⟨hZ₂Q, hZ₂R⟩ := zm_le_centralizer_critR h hb hc hμ₂ hd₂
  have hAQ : critA _ (baseA (puAmalgam h.le)) α' ≤ Qv _ (baseA (puAmalgam h.le)) := inf_le_right
  have hZhX : S5.zHat _ (baseA (puAmalgam h.le)) α' ≤
      Subgroup.normalizer (XM _ (baseA (puAmalgam h.le)) : Set _) :=
    hZhst.trans (stab_le_normalizer_xm _ _)
  have hXn : Qv _ (baseA (puAmalgam h.le)) ≤
      Subgroup.normalizer (XM _ (baseA (puAmalgam h.le)) : Set _) :=
    (qv_le_stab _ _).trans (stab_le_normalizer_xm _ _)
  have hYA : ⁅ZM _ μ₁ ⊔ ZM _ μ₂, critA _ (baseA (puAmalgam h.le)) α'⁆ ≤
      XM _ (baseA (puAmalgam h.le)) :=
    commutator_sup_le_of_le (hZ₁Q.trans hXn) (hZ₂Q.trans hXn)
      ((Subgroup.commutator_mono le_rfl hAQ).trans hX₁)
      ((Subgroup.commutator_mono le_rfl hAQ).trans hX₂)
  have hY3 : ¬ ⁅ZM (puAmalgam h.le) α', ZM _ μ₁ ⊔ ZM _ μ₂⁆ ≤
      ⁅XM (puAmalgam h.le) (baseA _), XM (puAmalgam h.le) α'⁆ ⊔
        ⁅critA _ (baseA (puAmalgam h.le)) α', ZM _ μ₁ ⊔ ZM _ μ₂⁆ := by
    intro hle
    apply hn
    refine le_normalizer_sup_of_commutator_le hZhX ?_
    have h1 : ⁅ZM _ μ₁, S5.zHat _ (baseA (puAmalgam h.le)) α'⁆ ≤
        ⁅ZM (puAmalgam h.le) α', ZM _ μ₁ ⊔ ZM _ μ₂⁆ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mono inf_le_left le_sup_left
    refine (h1.trans hle).trans (sup_le (hXX.trans le_sup_right) ?_)
    rw [Subgroup.commutator_comm]
    exact hYA.trans le_sup_right
  have hYZ' : ¬ ⁅ZM _ μ₁ ⊔ ZM _ μ₂, S5.zHat _ (baseA (puAmalgam h.le)) α'⁆ ≤
      critR _ (baseA (puAmalgam h.le)) α' := by
    intro hle
    apply hn
    exact le_normalizer_sup_of_commutator_le hZhX
      (((Subgroup.commutator_mono le_sup_left le_rfl).trans hle).trans (hRX.trans le_sup_right))
  have hS : S33.S33Hyp h α' (ZM _ μ₁ ⊔ ZM _ μ₂) :=
    ⟨hc, sup_le (hZ₁.trans hQQ) (hZ₂.trans hQQ), sup_le hZ₁R hZ₂R, hY3⟩
  have hrel : (Qv _ α').relIndex (ZM _ (baseA (puAmalgam h.le))) = 2 ^ k := by
    rcases S33.relIndex_or_hat h hd hS with hrel | ⟨t₁, t₂, t₃, ht, htn⟩
    · exact hrel
    · exact absurd ((Subgroup.commutator_mono (le_inf (sup_le (hZ₁.trans hQQ) (hZ₂.trans hQQ))
        (sup_le hZ₁R hZ₂R)) le_rfl).trans (commutator_zHat_le_critR h hc ht htn)) hYZ'
  have h4 := fun hAYY => (S33.d_main h hd hS hrel hAYY).2 hXU
  have hYc : ⁅⁅critA _ (baseA (puAmalgam h.le)) α', ZM _ μ₁ ⊔ ZM _ μ₂⁆, ZM _ μ₁ ⊔ ZM _ μ₂⁆ =
      ⊥ := by
    have h52iii := (h52 G M T L h hmin hb k F _ _ a hd α' hc).2.2.2
    have hle : ZM _ μ₁ ⊔ ZM _ μ₂ ≤ Vv _ (baseA (puAmalgam h.le)) ⊓
        Qv _ (geo _ α' (baseA (puAmalgam h.le)) 2) :=
      le_inf (sup_le (zm_le_vv_of_dist hμ₁ hd₁.le) (zm_le_vv_of_dist hμ₂ hd₂.le))
        (sup_le hZ₁ hZ₂)
    refine le_bot_iff.1 ?_
    rw [← h52iii]
    exact Subgroup.commutator_mono (Subgroup.commutator_mono le_rfl hle) hle
  obtain ⟨hcardY, -⟩ := h4 hYc
  have hfinX : Finite ↥(XM (puAmalgam h.le) (baseA _)) :=
    finite_of_le_qv h (isMVtx_baseA _) (xm_le_qv _ _)
  have hfinYA : Finite ↥(⁅ZM (puAmalgam h.le) μ₁ ⊔ ZM (puAmalgam h.le) μ₂,
      critA _ (baseA (puAmalgam h.le)) α'⁆ : Subgroup (puAmalgam h.le).Universal) :=
    Finite.of_injective (Subgroup.inclusion hYA) (Subgroup.inclusion_injective hYA)
  have hR₁Y : ⁅ZM (puAmalgam h.le) μ₁, critA _ (baseA (puAmalgam h.le)) α'⁆ =
      ⁅ZM _ μ₁ ⊔ ZM _ μ₂, critA _ (baseA (puAmalgam h.le)) α'⁆ :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.commutator_mono le_sup_left le_rfl)
      (by rw [hcardY, hcard₁])
  have h2R : ⁅ZM (puAmalgam h.le) μ₂, critA _ (baseA (puAmalgam h.le)) α'⁆ ≤
      ⁅ZM (puAmalgam h.le) μ₁, critA _ (baseA (puAmalgam h.le)) α'⁆ := by
    rw [hR₁Y]
    exact Subgroup.commutator_mono le_sup_right le_rfl
  have hle₁ : ⁅ZM (puAmalgam h.le) μ₁, critA _ (baseA (puAmalgam h.le)) α'⁆ ≤
      XM _ (baseA (puAmalgam h.le)) := (Subgroup.commutator_mono le_rfl hAQ).trans hX₁
  have hfinR : Finite ↥(⁅ZM (puAmalgam h.le) μ₁, critA _ (baseA (puAmalgam h.le)) α'⁆ :
      Subgroup (puAmalgam h.le).Universal) :=
    Finite.of_injective (Subgroup.inclusion hle₁) (Subgroup.inclusion_injective hle₁)
  have hcard₂ : Nat.card ↥(⁅ZM (puAmalgam h.le) μ₂, critA _ (baseA (puAmalgam h.le)) α'⁆ :
      Subgroup (puAmalgam h.le).Universal) ≤ 2 ^ k :=
    (Subgroup.card_le_of_le h2R).trans hcard₁.le
  obtain ⟨hAst₂, hA2, hAQ₂, hAc₂⟩ := critA_facts h hμ₂ hd₂ hcard₂ h0
  have htv₂ := (tv_card h hd hμ₂ hAst₂ hA2 hAQ₂ hAc₂).1
  refine ⟨Subgroup.eq_of_le_of_card_ge
    ((Subgroup.commutator_mono (uSub_le_zm h.le _) le_rfl).trans h2R) ?_, hAst₂⟩
  rw [hcard₁]
  exact htv₂

theorem s57_case56_aux (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {α' : Vtx (puAmalgam h.le)} {μ₁ μ₂ : Vtx (puAmalgam h.le)} (hμ₁ : IsMVtx _ μ₁)
    (hd₁ : (puAmalgam h.le).treeGraph.dist (baseA _) μ₁ = 2)
    {x : (puAmalgam h.le).Universal} (hxst : x ∈ stab _ (baseA (puAmalgam h.le)))
    (hμ : μ₂ = x⁻¹ • μ₁)
    (hcard₁ : Nat.card ↥⁅ZM _ μ₁, critA _ (baseA (puAmalgam h.le)) α'⁆ = 2 ^ k)
    (hcase : ⁅ZM _ μ₂, critA _ (baseA (puAmalgam h.le)) α'⁆ = ⊥ ∨
      (⁅S5.uSub h.le L μ₂, critA _ (baseA (puAmalgam h.le)) α'⁆ =
          ⁅ZM _ μ₁, critA _ (baseA (puAmalgam h.le)) α'⁆ ∧
        critA _ (baseA (puAmalgam h.le)) α' ≤ stab _ μ₂ ∧
        ⁅ZM _ μ₁, critA _ (baseA (puAmalgam h.le)) α'⁆ ≤ stabCenter _ (baseA _))) :
    ⁅critA _ (baseA (puAmalgam h.le)) α', (S5.uSub h.le L μ₁ ⊓
      Subgroup.centralizer (critA _ (baseA (puAmalgam h.le)) α' : Set _)).map
        (MulAut.conj x⁻¹).toMonoidHom⁆ = ⊥ := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have hU₂ : S5.uSub h.le L μ₂ = (S5.uSub h.le L μ₁).map (MulAut.conj x⁻¹).toMonoidHom := by
    rw [hμ]
    exact uSub_smul h.le hLn _ _
  rcases hcase with h0 | ⟨hU₂R, hAst₂, hcen⟩
  · refine le_bot_iff.1 ?_
    rw [← h0, Subgroup.commutator_comm]
    refine Subgroup.commutator_mono ?_ le_rfl
    have h1 : (S5.uSub h.le L μ₁ ⊓ Subgroup.centralizer
        (critA _ (baseA (puAmalgam h.le)) α' : Set _)).map (MulAut.conj x⁻¹).toMonoidHom ≤
        S5.uSub h.le L μ₂ := by
      rw [hU₂]
      exact Subgroup.map_mono inf_le_left
    exact h1.trans (uSub_le_zm h.le _)
  · set A := critA _ (baseA (puAmalgam h.le)) α' with hAdef
    set R₁ := ⁅ZM _ μ₁, A⁆ with hR₁
    have hxR : R₁.map (MulAut.conj x).toMonoidHom = R₁ := by
      ext r
      constructor
      · rintro ⟨r', hr', rfl⟩
        show x * r' * x⁻¹ ∈ R₁
        rw [conj_eq_of_mem_stabCenter hxst (hcen hr')]
        exact hr'
      · intro hr
        exact ⟨r, hr, conj_eq_of_mem_stabCenter hxst (hcen hr)⟩
    obtain ⟨hAst₁, hA2, hAQ₁, hAc₁⟩ :=
      critA_facts h hμ₁ hd₁ hcard₁.le (commutator_ne_bot_of_card hd hcard₁)
    have htv₁ := (tv_card h hd hμ₁ hAst₁ hA2 hAQ₁ hAc₁).1
    have hfinR : Finite ↥R₁ := finite_of_le_qv h hμ₁
      ((commutator_le_left_of_le_normalizer (hAst₁.trans (stab_le_normalizer_zm _ _))).trans
        (zm_le_qv_self _ hμ₁ h.critDist_pos))
    have hU₁R : ⁅S5.uSub h.le L μ₁, A⁆ = R₁ :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.commutator_mono (uSub_le_zm h.le _) le_rfl)
        (by rw [hcard₁]; exact htv₁)
    have hμ₁eq : μ₁ = x • μ₂ := by rw [hμ, smul_inv_smul]
    have hU₁ : S5.uSub h.le L μ₁ = (S5.uSub h.le L μ₂).map (MulAut.conj x).toMonoidHom := by
      conv_lhs => rw [hμ₁eq]
      exact uSub_smul h.le hLn _ _
    have hA'U : ⁅S5.uSub h.le L μ₁, A.map (MulAut.conj x).toMonoidHom⁆ = R₁ := by
      rw [hU₁, ← Subgroup.map_commutator, hU₂R, hxR]
    have hA'st : A.map (MulAut.conj x).toMonoidHom ≤ stab _ μ₁ := by
      rw [hμ₁eq, stab_smul]
      exact Subgroup.map_mono hAst₂
    have hCeq := uSub_inf_centralizer_eq h hd hμ₁ hAst₁ hA'st (hU₁R.trans hA'U.symm)
    rw [hCeq, Subgroup.map_inf _ _ _ (MulAut.conj x⁻¹).injective, ← hU₂,
      ← PU.centralizer_map_mulEquiv, map_conj_inv_map_conj, Subgroup.commutator_comm,
      Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact inf_le_right

theorem s57_case56_fin (h32 : S32) (h54 : S54) (h : PUHyp M T L)
    (hmin : PUMin M T L) (hb : 2 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a)
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    {μ₁ β₁ μ₂ : Vtx (puAmalgam h.le)} (hμ₁ : IsMVtx _ μ₁)
    (hd₁ : (puAmalgam h.le).treeGraph.dist (baseA _) μ₁ = 2)
    (hαβ₁ : (puAmalgam h.le).treeGraph.Adj (baseA _) β₁)
    (hβ₁μ₁ : (puAmalgam h.le).treeGraph.Adj β₁ μ₁) (hμ₂ : IsMVtx _ μ₂)
    (hd₂ : (puAmalgam h.le).treeGraph.dist (baseA _) μ₂ = 2)
    (hZ₁ : ZM _ μ₁ ≤ Qv _ (geo _ α' (baseA (puAmalgam h.le)) 2))
    (hZ₂ : ZM _ μ₂ ≤ Qv _ (geo _ α' (baseA (puAmalgam h.le)) 2))
    (hcard₁ : Nat.card ↥⁅ZM _ μ₁, critA _ (baseA (puAmalgam h.le)) α'⁆ = 2 ^ k)
    {x : (puAmalgam h.le).Universal} (hxst : x ∈ stab _ (baseA (puAmalgam h.le)))
    (hY₂Z : (S5.uSub h.le L μ₁ ⊓ Subgroup.centralizer
      (critA _ (baseA (puAmalgam h.le)) α' : Set _)).map (MulAut.conj x⁻¹).toMonoidHom ≤ ZM _ μ₂)
    (hAY₂ : ⁅critA _ (baseA (puAmalgam h.le)) α', (S5.uSub h.le L μ₁ ⊓
      Subgroup.centralizer (critA _ (baseA (puAmalgam h.le)) α' : Set _)).map
        (MulAut.conj x⁻¹).toMonoidHom⁆ = ⊥)
    (hL : puTrans h.le L (baseA _) ≤ S5.jOff h.le L (2 ^ k) μ₁ β₁ ⊔
      S5.zHat _ (baseA (puAmalgam h.le)) α' ⊔
        S5.rconj x⁻¹ (S5.zHat _ (baseA (puAmalgam h.le)) α')) :
    (S5.bSub h.le L (baseA _)).relIndex (S5.uSub h.le L μ₁) ≤ 2 ^ k := by
  have hyp := h.hyp20
  obtain ⟨hAst₁, hA2, hAQ₁, hAc₁⟩ :=
    critA_facts h hμ₁ hd₁ hcard₁.le (commutator_ne_bot_of_card hd hcard₁)
  obtain ⟨-, -, hZhst, hRX, hXX, hQQ⟩ := crit_facts h hc
  obtain ⟨-, hZ₁R⟩ := zm_le_centralizer_critR h hb hc hμ₁ hd₁
  obtain ⟨-, hZ₂R⟩ := zm_le_centralizer_critR h hb hc hμ₂ hd₂
  have hZhX : S5.zHat _ (baseA (puAmalgam h.le)) α' ≤
      Subgroup.normalizer (XM _ (baseA (puAmalgam h.le)) : Set _) :=
    hZhst.trans (stab_le_normalizer_xm _ _)
  set A := critA _ (baseA (puAmalgam h.le)) α' with hAdef
  set Y₁ := S5.uSub h.le L μ₁ ⊓ Subgroup.centralizer (A : Set _) with hY₁
  have hAT₁ : A ≤ Qv _ β₁ := inf_le_right.trans (qv_le_qv _ hyp (isMVtx_baseA _) hαβ₁)
  have hT₁st : Qv _ β₁ ≤ stab _ (baseA (puAmalgam h.le)) :=
    qv_le_stab_of_isMVtx _ hyp (isMVtx_baseA _) hαβ₁
  have hJn : S5.jOff h.le L (2 ^ k) μ₁ β₁ ≤
      Subgroup.normalizer ((Y₁ ⊔ XM _ (baseA (puAmalgam h.le)) : Subgroup _) : Set _) :=
    le_normalizer_sup (jOff_le_normalizer h hmin hb hd h54 hμ₁ hβ₁μ₁.symm hAT₁ hAQ₁ hAc₁)
      ((jOff_le_qv h.le L _ _ _).trans (hT₁st.trans (stab_le_normalizer_xm _ _)))
  have hAY₁ : ⁅A, Y₁⁆ = ⊥ := by
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact inf_le_right
  have hY₁Z : Y₁ ≤ ZM _ μ₁ := inf_le_left.trans (uSub_le_zm h.le _)
  have hZn₁ : S5.zHat _ (baseA (puAmalgam h.le)) α' ≤
      Subgroup.normalizer ((Y₁ ⊔ XM _ (baseA (puAmalgam h.le)) : Subgroup _) : Set _) :=
    le_normalizer_sup_of_commutator_le hZhX ((commutator_zHat_le' h hd hc
      ((hY₁Z.trans hZ₁).trans hQQ) (hY₁Z.trans hZ₁R) hAY₁).trans
        (sup_le (hXX.trans le_sup_right) (hRX.trans le_sup_right)))
  have hZn₂ : S5.rconj x⁻¹ (S5.zHat _ (baseA (puAmalgam h.le)) α') ≤
      Subgroup.normalizer ((Y₁ ⊔ XM _ (baseA (puAmalgam h.le)) : Subgroup _) : Set _) := by
    have hxX : (XM _ (baseA (puAmalgam h.le))).map (MulAut.conj x).toMonoidHom =
        XM _ (baseA (puAmalgam h.le)) := by
      rw [← xm_smul, (mem_stab _).1 hxst]
    have hW : Y₁ ⊔ XM _ (baseA (puAmalgam h.le)) =
        (Y₁.map (MulAut.conj x⁻¹).toMonoidHom ⊔
          XM _ (baseA (puAmalgam h.le))).map (MulAut.conj x).toMonoidHom := by
      rw [Subgroup.map_sup, map_conj_map_conj_inv, hxX]
    rw [rconj_eq_map, inv_inv, hW, normalizer_map_conj, map_conj_le_map_conj_iff]
    exact le_normalizer_sup_of_commutator_le hZhX ((commutator_zHat_le' h hd hc
      ((hY₂Z.trans hZ₂).trans hQQ) (hY₂Z.trans hZ₂R) hAY₂).trans
        (sup_le (hXX.trans le_sup_right) (hRX.trans le_sup_right)))
  exact s57_finish h32 h hb hd hμ₁ hd₁ hcard₁ (hL.trans (sup_le (sup_le hJn hZn₁) hZn₂))

omit [Fintype F] in
theorem s57_xm_facts_of_le (h : PUHyp M T L) (hXU : Xq M = Uq M T L ⊔ Zq M L)
    (hZc : Zq M L ≤ Subgroup.centralizer (M : Set G)) (l : Submodule F (MSP.V4 F)) :
    XM _ (baseA (puAmalgam h.le)) ⊓ Subgroup.centralizer
        (S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) : Set _) ≤
      S5.uSub h.le L (baseA _) ⊔ XM _ (baseA (puAmalgam h.le)) ⊓ stabCenter _ (baseA _) ∧
    XM _ (baseA (puAmalgam h.le)) ⊓
        Subgroup.centralizer (S5.vPre h.le a (MSP.qLine l) : Set (puAmalgam h.le).Universal) ≤
      ZM _ (baseA (puAmalgam h.le)) :=
  ⟨inf_le_left.trans (xm_eq_uSub_sup h hXU hZc).le, inf_le_left.trans (xm_eq_zm h hXU hZc).le⟩

theorem s57_case56_core (h32 : S32) (hX2 : S33.S33X52) (h52 : S52) (h54 : S54)
    (h : PUHyp M T L) (hmin : PUMin M T L) (hb : 2 < critDist (puAmalgam h.le))
    (hd : S5.IsSp4Data M T L k F a) {α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical _ (baseA (puAmalgam h.le)) α') {δ : Vtx (puAmalgam h.le)}
    (hβδ : (puAmalgam h.le).treeGraph.Adj (baseB _) δ) {l : Submodule F (MSP.V4 F)}
    (hc56 : S5.Case56 h (2 ^ k) a δ l) {g x : (puAmalgam h.le).Universal}
    (hg : g ∈ stab _ (baseA (puAmalgam h.le))) (hx : x ∈ puTrans h.le L (baseA _))
    (hb6 : ZM _ (baseA (puAmalgam h.le)) ⊓
        Subgroup.centralizer (S5.rconj g (S5.vPre h.le a (MSP.qLine l)) :
          Set (puAmalgam h.le).Universal) ⊓
        Subgroup.centralizer (S5.rconj (g * x) (S5.vPre h.le a (MSP.qLine l)) :
          Set (puAmalgam h.le).Universal) ≤
      stabCenter _ (baseA _))
    (hc6 : puTrans h.le L (baseA _) ≤
      S5.rconj g (S5.jOff h.le L (2 ^ k) (baseA _) (baseB _)) ⊔
        S5.zHat _ (baseA (puAmalgam h.le)) α' ⊔
        S5.rconj x⁻¹ (S5.zHat _ (baseA (puAmalgam h.le)) α'))
    (hZ₁ : ZM _ (g⁻¹ • δ) ≤ Qv _ (geo _ α' (baseA (puAmalgam h.le)) 2))
    (hZ₂ : ZM _ (x⁻¹ • g⁻¹ • δ) ≤ Qv _ (geo _ α' (baseA (puAmalgam h.le)) 2))
    (hn : ¬ S5.zHat _ (baseA (puAmalgam h.le)) α' ≤ Subgroup.normalizer
      ((ZM _ (g⁻¹ • δ) ⊔ XM _ (baseA (puAmalgam h.le)) : Subgroup _) : Set _)) :
    (S5.bSub h.le L (baseA _)).relIndex (S5.uSub h.le L δ) ≤ 2 ^ k := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  by_cases hδα : δ = baseA _
  · subst hδα
    rw [Subgroup.relIndex_eq_one.2]
    · exact Nat.one_le_two_pow
    · intro u hu
      refine Subgroup.subset_closure ⟨zm_le_vv_of_dist (isMVtx_baseA _) (by simp)
        (uSub_le_zm h.le _ hu), fun y hy => ?_⟩
      exact commutator_le_left_of_le_normalizer ((puTrans_le_stab h.le L _).trans
        (stab_le_normalizer_zm _ _)) (Subgroup.commutator_mem_commutator
          (uSub_le_zm h.le _ hu) hy)
  have hxst : x ∈ stab _ (baseA (puAmalgam h.le)) := puTrans_le_stab h.le L _ hx
  have hgx : g * x ∈ stab _ (baseA (puAmalgam h.le)) := mul_mem hg hxst
  obtain ⟨hαβ₁, hβ₁α₁, hα₁, hdα₁⟩ := s57_vert h hβδ hδα hg
  have hα₂eq : x⁻¹ • g⁻¹ • δ = (g * x)⁻¹ • δ := by rw [mul_inv_rev, mul_smul]
  obtain ⟨-, -, hα₂, hdα₂⟩ := s57_vert h hβδ hδα hgx
  rw [← hα₂eq] at hα₂ hdα₂
  obtain ⟨hidx, hXU, hcard₁, -⟩ := s57_s33 h32 hX2 h52 h hmin hb hd hc hα₁ hdα₁ hZ₁ hn
  obtain ⟨hXJ, hXQ⟩ := s57_xm_facts_of_le h hXU
    (S5Q2.UC.zq_le_centralizer_of_relIndex_eq h hd hc hidx) l
  have hcomm := commutator_zm_qv_le_baseA h hmin hb hd h54 hβδ hc56 hXJ
  have hZ₀ : ⁅ZM _ (g⁻¹ • δ), Qv _ (baseA (puAmalgam h.le))⁆ ≤ ZM _ (baseA (puAmalgam h.le)) := by
    have hgα : g⁻¹ • baseA (puAmalgam h.le) = baseA _ := (mem_stab _).1 (inv_mem hg)
    have h1 := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) (hcomm.trans hXQ)
    rwa [Subgroup.map_commutator, ← zm_smul, ← qv_smul, ← zm_smul, hgα] at h1
  have hcomm₁ := s57_comm_conj h.le hcomm hg
  have hcomm₂ := s57_comm_conj h.le hcomm hgx
  rw [← hα₂eq] at hcomm₂
  have hAQ : critA _ (baseA (puAmalgam h.le)) α' ≤ Qv _ (baseA (puAmalgam h.le)) := inf_le_right
  have hcase : ⁅ZM _ (x⁻¹ • g⁻¹ • δ), critA _ (baseA (puAmalgam h.le)) α'⁆ = ⊥ ∨
      (⁅S5.uSub h.le L (x⁻¹ • g⁻¹ • δ), critA _ (baseA (puAmalgam h.le)) α'⁆ =
          ⁅ZM _ (g⁻¹ • δ), critA _ (baseA (puAmalgam h.le)) α'⁆ ∧
        critA _ (baseA (puAmalgam h.le)) α' ≤ stab _ (x⁻¹ • g⁻¹ • δ) ∧
        ⁅ZM _ (g⁻¹ • δ), critA _ (baseA (puAmalgam h.le)) α'⁆ ≤ stabCenter _ (baseA _)) := by
    by_cases h0 : ⁅ZM _ (x⁻¹ • g⁻¹ • δ), critA _ (baseA (puAmalgam h.le)) α'⁆ = ⊥
    · exact Or.inl h0
    · obtain ⟨hU₂R, hAst₂⟩ := s57_sub2 hXU h52 h hmin hb hd hc hα₁ hdα₁ hα₂ hdα₂ hZ₁ hZ₂ hn hcard₁
        (hcomm₁.trans inf_le_left) (hcomm₂.trans inf_le_left) h0
      refine Or.inr ⟨hU₂R, hAst₂, le_trans ?_ hb6⟩
      refine le_inf (le_inf ?_ ?_) ?_
      · exact (Subgroup.commutator_mono le_rfl hAQ).trans hZ₀
      · exact (Subgroup.commutator_mono le_rfl hAQ).trans (hcomm₁.trans inf_le_right)
      · rw [← hU₂R]
        exact (Subgroup.commutator_mono (uSub_le_zm h.le _) hAQ).trans
          (hcomm₂.trans inf_le_right)
  have hAY₂ := s57_case56_aux h hd hα₁ hdα₁ hxst rfl hcard₁ hcase
  have hY₂Z : (S5.uSub h.le L (g⁻¹ • δ) ⊓ Subgroup.centralizer
      (critA _ (baseA (puAmalgam h.le)) α' : Set _)).map (MulAut.conj x⁻¹).toMonoidHom ≤
      ZM _ (x⁻¹ • g⁻¹ • δ) := by
    have h1 : (S5.uSub h.le L (g⁻¹ • δ) ⊓ Subgroup.centralizer
        (critA _ (baseA (puAmalgam h.le)) α' : Set _)).map (MulAut.conj x⁻¹).toMonoidHom ≤
        S5.uSub h.le L (x⁻¹ • g⁻¹ • δ) := by
      rw [uSub_smul h.le hLn x⁻¹ (g⁻¹ • δ)]
      exact Subgroup.map_mono inf_le_left
    exact h1.trans (uSub_le_zm h.le _)
  have hJeq : S5.rconj g (S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _)) =
      S5.jOff h.le L (2 ^ k) (g⁻¹ • δ) (g⁻¹ • baseB (puAmalgam h.le)) := by
    rw [← hc56.1, rconj_eq_map, jOff_smul h.le hLn]
  rw [hJeq] at hc6
  have := s57_case56_fin h32 h54 h hmin hb hd hc hα₁ hdα₁ hαβ₁ hβ₁α₁ hα₂ hdα₂ hZ₁ hZ₂
    hcard₁ hxst hY₂Z hAY₂ hc6
  rwa [relIndex_bSub_uSub_smul h (inv_mem hg) δ] at this

theorem s57_both_normal (h32 : S32) (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    {α' : Vtx (puAmalgam h.le)} {δ : Vtx (puAmalgam h.le)}
    (hβδ : (puAmalgam h.le).treeGraph.Adj (baseB _) δ) {g x : (puAmalgam h.le).Universal}
    (hg : g ∈ stab _ (baseA (puAmalgam h.le))) (hx : x ∈ puTrans h.le L (baseA _))
    (hc6 : puTrans h.le L (baseA _) ≤
      S5.rconj g (S5.jOff h.le L (2 ^ k) (baseA _) (baseB _)) ⊔
        S5.zHat _ (baseA (puAmalgam h.le)) α' ⊔
        S5.rconj x⁻¹ (S5.zHat _ (baseA (puAmalgam h.le)) α'))
    (hn₁ : S5.zHat _ (baseA (puAmalgam h.le)) α' ≤ Subgroup.normalizer
      ((ZM _ (g⁻¹ • δ) ⊔ XM _ (baseA (puAmalgam h.le)) : Subgroup _) : Set _))
    (hn₂ : S5.zHat _ (baseA (puAmalgam h.le)) α' ≤ Subgroup.normalizer
      ((ZM _ (x⁻¹ • g⁻¹ • δ) ⊔ XM _ (baseA (puAmalgam h.le)) : Subgroup _) : Set _)) :
    (S5.bSub h.le L (baseA _)).relIndex (S5.uSub h.le L δ) ≤ 2 ^ k := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have h32' := (h32 G M T L h).2.1
  have hxst : x ∈ stab _ (baseA (puAmalgam h.le)) := puTrans_le_stab h.le L _ hx
  by_cases hδα : δ = baseA _
  · subst hδα
    rw [Subgroup.relIndex_eq_one.2]
    · exact Nat.one_le_two_pow
    · intro u hu
      refine Subgroup.subset_closure ⟨zm_le_vv_of_dist (isMVtx_baseA _) (by simp)
        (uSub_le_zm h.le _ hu), fun y hy => ?_⟩
      exact commutator_le_left_of_le_normalizer ((puTrans_le_stab h.le L _).trans
        (stab_le_normalizer_zm _ _)) (Subgroup.commutator_mem_commutator
          (uSub_le_zm h.le _ hu) hy)
  obtain ⟨hαβ₁, hβ₁α₁, hα₁, hdα₁⟩ := s57_vert h hβδ hδα hg
  have hxX : (XM _ (baseA (puAmalgam h.le))).map (MulAut.conj x).toMonoidHom =
      XM _ (baseA (puAmalgam h.le)) := by
    rw [← xm_smul, (mem_stab _).1 hxst]
  have h1 : S5.rconj g (S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _)) ≤
      Qv _ (g⁻¹ • baseB (puAmalgam h.le)) := by
    rw [rconj_eq_map, qv_smul]
    exact Subgroup.map_mono (jOff_le_qv h.le L _ _ _)
  have hJn : S5.rconj g (S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _)) ≤
      Subgroup.normalizer ((ZM _ (g⁻¹ • δ) ⊔ XM _ (baseA (puAmalgam h.le)) : Subgroup _) :
        Set _) :=
    le_normalizer_sup (h1.trans ((qv_le_stab_of_adj _ hβ₁α₁).trans
      (stab_le_normalizer_zm _ _))) (h1.trans ((qv_le_stab_of_isMVtx _ hyp
        (isMVtx_baseA _) hαβ₁).trans (stab_le_normalizer_xm _ _)))
  have hZn₂ : S5.rconj x⁻¹ (S5.zHat _ (baseA (puAmalgam h.le)) α') ≤
      Subgroup.normalizer ((ZM _ (g⁻¹ • δ) ⊔ XM _ (baseA (puAmalgam h.le)) : Subgroup _) :
        Set _) := by
    have hW : ZM _ (g⁻¹ • δ) ⊔ XM _ (baseA (puAmalgam h.le)) =
        (ZM _ (x⁻¹ • g⁻¹ • δ) ⊔ XM _ (baseA (puAmalgam h.le))).map
          (MulAut.conj x).toMonoidHom := by
      rw [Subgroup.map_sup, ← zm_smul, smul_inv_smul, hxX]
    rw [rconj_eq_map, inv_inv, hW, normalizer_map_conj, map_conj_le_map_conj_iff]
    exact hn₂
  have hall := hc6.trans (sup_le (sup_le hJn hn₁) hZn₂)
  have hZB := le_bSub_of_xm h hb h32' (isMVtx_baseA _) hdα₁ (zm_le_xm _ hyp hb0 hα₁)
    (zm_le_vv_of_dist hα₁ hdα₁.le) hall
  rw [← relIndex_bSub_uSub_smul h (inv_mem hg) δ,
    Subgroup.relIndex_eq_one.2 ((uSub_le_zm h.le _).trans hZB)]
  exact Nat.one_le_two_pow

omit [Finite G] [Fintype F] in
theorem s57_swap_c6 (hTM : T ≤ M) {α' : Vtx (puAmalgam hTM)}
    {J : Subgroup (puAmalgam hTM).Universal}
    {g x : (puAmalgam hTM).Universal} (hx : x ∈ puTrans hTM L (baseA _))
    (hc6 : puTrans hTM L (baseA _) ≤ S5.rconj g J ⊔ S5.zHat _ (baseA (puAmalgam hTM)) α' ⊔
      S5.rconj x⁻¹ (S5.zHat _ (baseA (puAmalgam hTM)) α')) :
    puTrans hTM L (baseA _) ≤ S5.rconj (g * x) J ⊔ S5.zHat _ (baseA (puAmalgam hTM)) α' ⊔
      S5.rconj x⁻¹⁻¹ (S5.zHat _ (baseA (puAmalgam hTM)) α') := by
  have h1 := (rconj_le_rconj_iff (g := x)).2 hc6
  rw [rconj_eq_self_of_mem hx, rconj_sup, rconj_sup, ← rconj_mul, rconj_rconj_inv] at h1
  rw [inv_inv]
  exact h1.trans (sup_right_comm _ _ _).le

theorem s57_case56 (h32 : S32) (hX2 : S33.S33X52) (h52 : S52) (h54 : S54)
    (h : PUHyp M T L) (hmin : PUMin M T L) (hb : 2 < critDist (puAmalgam h.le))
    (hd : S5.IsSp4Data M T L k F a) {α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical _ (baseA (puAmalgam h.le)) α') {δ : Vtx (puAmalgam h.le)}
    (hβδ : (puAmalgam h.le).treeGraph.Adj (baseB _) δ) {l : Submodule F (MSP.V4 F)}
    (hc56 : S5.Case56 h (2 ^ k) a δ l) {g x : (puAmalgam h.le).Universal}
    (hg : g ∈ stab _ (baseA (puAmalgam h.le))) (hx : x ∈ puTrans h.le L (baseA _))
    (hconc : S5.Concl56 h (2 ^ k) a α' l g x)
    (hZ₁ : ZM _ (g⁻¹ • δ) ≤ Qv _ (geo _ α' (baseA (puAmalgam h.le)) 2))
    (hZ₂ : ZM _ (x⁻¹ • g⁻¹ • δ) ≤ Qv _ (geo _ α' (baseA (puAmalgam h.le)) 2)) :
    (S5.bSub h.le L (baseA _)).relIndex (S5.uSub h.le L δ) ≤ 2 ^ k := by
  obtain ⟨-, hb6, hc6, -⟩ := hconc
  have hxst : x ∈ stab _ (baseA (puAmalgam h.le)) := puTrans_le_stab h.le L _ hx
  by_cases hn₁ : S5.zHat _ (baseA (puAmalgam h.le)) α' ≤ Subgroup.normalizer
      ((ZM _ (g⁻¹ • δ) ⊔ XM _ (baseA (puAmalgam h.le)) : Subgroup _) : Set _)
  · by_cases hn₂ : S5.zHat _ (baseA (puAmalgam h.le)) α' ≤ Subgroup.normalizer
        ((ZM _ (x⁻¹ • g⁻¹ • δ) ⊔ XM _ (baseA (puAmalgam h.le)) : Subgroup _) : Set _)
    · exact s57_both_normal h32 h hb hβδ hg hx hc6 hn₁ hn₂
    ·
      have hb6' : ZM _ (baseA (puAmalgam h.le)) ⊓
          Subgroup.centralizer (S5.rconj (g * x) (S5.vPre h.le a (MSP.qLine l)) :
            Set (puAmalgam h.le).Universal) ⊓
          Subgroup.centralizer (S5.rconj (g * x * x⁻¹) (S5.vPre h.le a (MSP.qLine l)) :
            Set (puAmalgam h.le).Universal) ≤ stabCenter _ (baseA _) := by
        rw [mul_inv_cancel_right]
        refine le_trans ?_ hb6
        exact le_inf (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
          (inf_le_left.trans inf_le_right)
      have hZ₁' : ZM _ ((g * x)⁻¹ • δ) ≤ Qv _ (geo _ α' (baseA (puAmalgam h.le)) 2) := by
        rw [mul_inv_rev, mul_smul]
        exact hZ₂
      have hZ₂' : ZM _ (x⁻¹⁻¹ • (g * x)⁻¹ • δ) ≤ Qv _ (geo _ α' (baseA (puAmalgam h.le)) 2) := by
        rw [inv_inv, mul_inv_rev, mul_smul, smul_inv_smul]
        exact hZ₁
      have hn' : ¬ S5.zHat _ (baseA (puAmalgam h.le)) α' ≤ Subgroup.normalizer
          ((ZM _ ((g * x)⁻¹ • δ) ⊔ XM _ (baseA (puAmalgam h.le)) : Subgroup _) : Set _) := by
        rw [mul_inv_rev, mul_smul]
        exact hn₂
      exact s57_case56_core h32 hX2 h52 h54 h hmin hb hd hc hβδ hc56 (mul_mem hg hxst)
        (inv_mem hx) hb6' (s57_swap_c6 h.le hx hc6) hZ₁' hZ₂' hn'
  · exact s57_case56_core h32 hX2 h52 h54 h hmin hb hd hc hβδ hc56 hg hx hb6 hc6 hZ₁ hZ₂
      hn₁

theorem s57_sel (h32 : S32) (hX2 : S33.S33X52) (h52 : S52) (h54 : S54) (h55 : S55)
    (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb : 2 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a)
    {S : Submodule F (MSP.V4 F) → (puAmalgam h.le).Universal → (puAmalgam h.le).Universal → Prop}
    (h56S : Prod56 h k a S) {α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    (hαβ : geo _ (baseA (puAmalgam h.le)) α' 1 = baseB _) {δ : Vtx (puAmalgam h.le)}
    (hβδ : (puAmalgam h.le).treeGraph.Adj (baseB _) δ)
    (hδ : ∀ μ ∈ lamSel h (2 ^ k) a S α' δ,
      ZM _ μ ≤ Qv _ (geo _ α' (baseA (puAmalgam h.le)) 2)) :
    (S5.bSub h.le L (baseA _)).relIndex (S5.uSub h.le L δ) ≤ 2 ^ k := by
  by_cases hcase : ∃ l, S5.Case56 h (2 ^ k) a δ l
  · obtain ⟨l, hl⟩ := hcase
    obtain ⟨hJδ, hline, hTl, hJl⟩ := hl
    obtain ⟨g, hg, x, hx, hconc, hS⟩ := h56S α' hc hαβ l hline hTl hJl
    have hmem₁ : g⁻¹ • δ ∈ lamSel h (2 ^ k) a S α' δ :=
      ⟨g, x, hg, hx, Or.inr ⟨l, ⟨hJδ, hline, hTl, hJl⟩, hconc, hS⟩, Or.inl rfl⟩
    have hmem₂ : x⁻¹ • g⁻¹ • δ ∈ lamSel h (2 ^ k) a S α' δ :=
      ⟨g, x, hg, hx, Or.inr ⟨l, ⟨hJδ, hline, hTl, hJl⟩, hconc, hS⟩, Or.inr rfl⟩
    exact s57_case56 h32 hX2 h52 h54 h hmin hb hd hc hβδ ⟨hJδ, hline, hTl, hJl⟩ hg hx hconc
      (hδ _ hmem₁) (hδ _ hmem₂)
  · push Not at hcase
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
    exact s57_case55 h32 hX2 h52 h54 h hmin hb hd hc hβδ hg hconc (hδ _ hmem₁)

theorem s57 (h32 : S32) (hX2 : S33.S33X52) (h52 : S52) (h54 : S54) (h55 : S55) (h56 : S56)
    (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb : 2 < critDist (puAmalgam h.le))
    (hd : S5.IsSp4Data M T L k F a) {α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    (hαβ : geo _ (baseA (puAmalgam h.le)) α' 1 = baseB _) {δ : Vtx (puAmalgam h.le)}
    (hβδ : (puAmalgam h.le).treeGraph.Adj (baseB _) δ)
    (hδ : ∀ μ ∈ S5.lam h (2 ^ k) a α' δ, ZM _ μ ≤ Qv _ (geo _ α' (baseA (puAmalgam h.le)) 2)) :
    (S5.bSub h.le L (baseA _)).relIndex (S5.uSub h.le L δ) ≤ 2 ^ k :=
  s57_sel h32 hX2 h52 h54 h55 h hmin hb hd (prod56_top h56 hmin hb hd) hc hαβ hβδ
    fun μ hμ => hδ μ (lamSel_subset hμ)

end S5B

end CFSG.Quasithin.MS93
