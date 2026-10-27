module

public import CFSG.Quasithin.MS93.S52i33
public import CFSG.Quasithin.MS93.S59Crit
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.MS93.S512NV
public import CFSG.Quasithin.MS93.S512NW
public import CFSG.Quasithin.MS93.S512TBad
public import CFSG.Quasithin.MS93.S512TTwo

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

namespace S512R

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem commutator_zHat_le_critR_at (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {δ δ' : Vtx (puAmalgam h.le)} (hc : IsCritical _ δ δ')
    (hΛ : (2 ^ k) ^ 2 ≤ (Qv _ δ').relIndex (ZM _ δ))
    {Y : Subgroup (puAmalgam h.le).Universal} (hY : Y ≤ Qv _ (geo _ δ' δ 1))
    (hYR : Y ≤ Subgroup.centralizer (critR _ δ δ' : Set (puAmalgam h.le).Universal)) :
    ⁅Y, S5.zHat _ δ δ'⁆ ≤ critR _ δ δ' := by
  obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ hc.1
  obtain ⟨δ₀, rfl⟩ : ∃ δ₀, δ' = g • δ₀ := ⟨g⁻¹ • δ', (smul_inv_smul g δ').symm⟩
  have hc₀ : IsCritical _ (baseA (puAmalgam h.le)) δ₀ := (isCritical_smul _ g _ _).1 hc
  have hΛ₀ : (2 ^ k) ^ 2 ≤ (Qv _ δ₀).relIndex (ZM _ (baseA (puAmalgam h.le))) := by
    rwa [S5B.relIndex_qv_zm_smul] at hΛ
  have hR : critR _ (g • baseA (puAmalgam h.le)) (g • δ₀) =
      (critR _ (baseA (puAmalgam h.le)) δ₀).map (MulAut.conj g).toMonoidHom := by
    rw [critR, critR, zm_smul, zm_smul, Subgroup.map_commutator]
  have hYe : Y = (Y.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
    rw [MSP.map_conj_map_conj, mul_inv_cancel, PU.map_conj_one]
  rw [hYe] at hY hYR ⊢
  rw [geo_smul, qv_smul, map_conj_le_map_conj_iff] at hY
  rw [hR, PU.centralizer_map_mulEquiv, map_conj_le_map_conj_iff] at hYR
  have key := S52i.commutator_zHat_le_critR_of_sq h hd hc₀ hΛ₀ hY hYR
  rw [S5B.zHat_smul, hR, ← Subgroup.map_commutator]
  exact Subgroup.map_mono key

theorem core56_facts (h52 : S52) (h55 : S55) (h56 : S56) (h : PUHyp M T L)
    (hmin : PUMin M T L) (hb4 : critDist (puAmalgam h.le) = 4) (hd : S5.IsSp4Data M T L k F a)
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    {μ : Vtx (puAmalgam h.le)} {y : (puAmalgam h.le).Universal}
    (hy : y ∈ stab _ (baseA (puAmalgam h.le))) (hμy : μ = y • geo _ (baseA (puAmalgam h.le)) α' 2)
    (hcμ : IsCritical _ μ (geo _ (baseA (puAmalgam h.le)) α' 2))
    (hbad : 2 ^ k < (Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2)).relIndex (ZM _ μ))
    (hRc : ⁅ZM (puAmalgam h.le) μ, ZM (puAmalgam h.le) (geo _ (baseA (puAmalgam h.le)) α' 2)⁆ ≤
      stabCenter _ (baseA (puAmalgam h.le))) :
    ⁅S5.voSub h.le L (baseA (puAmalgam h.le)), Qv _ (baseA (puAmalgam h.le))⁆ ≤
        S5.dSub h.le L (baseA _) ∧
      ⁅⁅S5.nclStab _ (baseA _) (ZM _ (geo _ (baseA (puAmalgam h.le)) α' 2)),
            puTrans h.le L (baseA _)⁆,
          ⁅S5.nclStab _ (baseA _) (ZM _ (geo _ (baseA (puAmalgam h.le)) α' 2)),
            puTrans h.le L (baseA _)⁆⁆ ≤
        S5.dSub h.le L (baseA _) := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hk : 1 < 2 ^ k := Nat.one_lt_two_pow (by have := hd.1; omega)
  set γ := geo _ (baseA (puAmalgam h.le)) α' 2 with hγdef
  have hγM : IsMVtx _ γ := isMVtx_geo_two _ hyp hb0 hc
  have hdαγ : (puAmalgam h.le).treeGraph.dist (baseA _) γ = 2 :=
    dist_geo _ (by have := hc.2.1; omega)
  obtain ⟨hμM, -, -, hd4, -, -, -, -, -, -, -, -⟩ := S512T.pair_facts h hb4 hcμ
  have hdαμ : (puAmalgam h.le).treeGraph.dist (baseA _) μ = 2 := by
    have := dist_smul _ y (baseA (puAmalgam h.le)) γ
    rw [(mem_stab _).1 hy, ← hμy] at this
    rw [this, hdαγ]
  obtain ⟨hrel, -⟩ := S512T.bad_indices h hb4 hd hcμ hbad
  have hΛ : (2 ^ k) ^ 2 ≤ (Qv _ γ).relIndex (ZM _ μ) := by
    rw [S512T.relIndex_qv_zm_eq h hb4 hcμ, hrel]
  have hmid : geo _ μ γ 2 = baseA (puAmalgam h.le) := by
    symm
    refine eq_geo_of_dist _ (by rw [tdist_comm]; exact hdαμ) ?_
    rw [tdist_comm, hdαμ, hdαγ, hd4]
  have hcγμ : IsCritical _ γ μ := ms22_iii _ hyp hb0 h.centHyp hcμ
  obtain ⟨-, -, -, hd4', hγρ, hρα, -, -, -, -, -, -⟩ := S512T.pair_facts h hb4 hcγμ
  have hmid' : geo _ γ μ 2 = baseA (puAmalgam h.le) := by
    have e : geo _ γ μ 2 = geo _ μ γ 2 := by
      have := geo_symm _ (show 2 ≤ (puAmalgam h.le).treeGraph.dist μ γ by omega)
      rwa [hd4] at this
    rw [e, hmid]
  rw [hmid'] at hρα
  set R := critR (puAmalgam h.le) μ γ with hRdef
  set Zh := S5.zHat (puAmalgam h.le) μ γ with hZhdef
  have hQR : Qv _ (baseA (puAmalgam h.le)) ≤
      Subgroup.centralizer (R : Set (puAmalgam h.le).Universal) := by
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact (S510.commute_of_mem_stabCenter (hRc hr) (qv_le_stab _ _ ht)).symm
  have hQZh : ⁅Qv _ (baseA (puAmalgam h.le)), Zh⁆ ≤ R :=
    commutator_zHat_le_critR_at h hd hcμ hΛ (qv_le_qv _ hyp hα hρα.symm) hQR
  have hZhZ : Zh ≤ ZM _ γ := inf_le_left
  have hZhB : ¬ Zh ≤ S5.bSub h.le L (baseA _) := by
    intro hle
    have hinf : ZM _ γ ⊓ S5.bSub h.le L (baseA _) ≤ Qv _ μ := by
      have e : y⁻¹ • μ = γ := by rw [hμy, inv_smul_smul]
      have := S512N.inf_bSub_le_qv h hb hα hμM hdαμ (inv_mem hy)
      rwa [e] at this
    exact S59.zHat_not_le_qv h55 h56 h hmin hb hd hcμ (le_inf hZhZ hle |>.trans hinf)
  set W := S5.nclStab _ (baseA (puAmalgam h.le)) Zh ⊔ ZM _ (baseA (puAmalgam h.le)) with hWdef
  have hZγV : S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ γ) ≤ Vv _ (baseA (puAmalgam h.le)) :=
    S512N.nclStab_le_vv h hγM hdαγ.le
  have hZγQ : S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ γ) ≤ Qv _ (baseA (puAmalgam h.le)) :=
    S310.nclStab_le_qv h hγM hdαγ hb
  have hncl : S5.nclStab _ (baseA (puAmalgam h.le)) Zh ≤
      S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ γ) :=
    iSup_mono fun g => Subgroup.map_mono hZhZ
  have hWV : W ≤ Vv _ (baseA (puAmalgam h.le)) :=
    sup_le (hncl.trans hZγV) (S5B.zm_le_vv_of_dist hα (by simp))
  have hWQ : W ≤ Qv _ (baseA (puAmalgam h.le)) :=
    sup_le (hncl.trans hZγQ) (zm_le_qv_self _ hα hb0)
  have hWn : stab _ (baseA (puAmalgam h.le)) ≤
      Subgroup.normalizer (W : Set (puAmalgam h.le).Universal) :=
    le_normalizer_sup (S310.stab_le_normalizer_nclStab _ _ _) (stab_le_normalizer_zm _ _)
  have hWR : ⁅W, Qv _ (baseA (puAmalgam h.le))⁆ ≤ R := by
    let P : Subgroup (puAmalgam h.le).Universal :=
      { carrier := {w | w ∈ stab _ (baseA (puAmalgam h.le)) ∧
          ∀ t ∈ Qv _ (baseA (puAmalgam h.le)), ⁅w, t⁆ ∈ R}
        one_mem' := ⟨one_mem _, fun t _ => by
          rw [commutatorElement_def, one_mul, inv_one, mul_one, mul_inv_cancel]
          exact one_mem _⟩
        mul_mem' := by
          rintro w₁ w₂ ⟨hw₁, h₁⟩ ⟨hw₂, h₂⟩
          refine ⟨mul_mem hw₁ hw₂, fun t ht => ?_⟩
          have e : ⁅w₁ * w₂, t⁆ = (w₁ * ⁅w₂, t⁆ * w₁⁻¹) * ⁅w₁, t⁆ := by
            simp only [commutatorElement_def]
            group
          have hc₂ := S510.commute_of_mem_stabCenter (hRc (h₂ t ht)) hw₁
          rw [e, hc₂, mul_inv_cancel_right]
          exact mul_mem (h₂ t ht) (h₁ t ht)
        inv_mem' := by
          rintro w ⟨hw, h₁⟩
          refine ⟨inv_mem hw, fun t ht => ?_⟩
          have e : ⁅w⁻¹, t⁆ = w⁻¹ * ⁅w, t⁆⁻¹ * w := by
            simp only [commutatorElement_def]
            group
          have hc' : w⁻¹ * ⁅w, t⁆⁻¹ = ⁅w, t⁆⁻¹ * w⁻¹ :=
            S510.commute_of_mem_stabCenter (inv_mem (hRc (h₁ t ht))) (inv_mem hw)
          rw [e, hc', inv_mul_cancel_right]
          exact inv_mem (h₁ t ht) }
    have hZhP : Zh ≤ P := fun z hz => ⟨hZhZ.trans ((S512N.zm_le_qv_two h hb hγM hdαγ).trans
      (qv_le_stab _ _)) hz, fun t ht => by
        rw [← commutatorElement_inv]
        exact inv_mem (hQZh (Subgroup.commutator_mem_commutator ht hz))⟩
    have hnclP : S5.nclStab _ (baseA (puAmalgam h.le)) Zh ≤ P := by
      refine iSup_le fun g => ?_
      rintro _ ⟨z, hz, rfl⟩
      refine ⟨mul_mem (mul_mem g.2 (hZhP hz).1) (inv_mem g.2), fun t ht => ?_⟩
      have htg : (g : (puAmalgam h.le).Universal)⁻¹ * t * g ∈ Qv _ (baseA (puAmalgam h.le)) := by
        have := (Subgroup.mem_normalizer_iff.1 (stab_le_normalizer_qv _ _ (inv_mem g.2)) t).1 ht
        simpa using this
      have h1 := (hZhP hz).2 _ htg
      have e : ⁅(MulAut.conj (g : (puAmalgam h.le).Universal)).toMonoidHom z, t⁆ =
          (g : (puAmalgam h.le).Universal) * ⁅z, (g : (puAmalgam h.le).Universal)⁻¹ * t * g⁆ *
            (g : (puAmalgam h.le).Universal)⁻¹ := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def]
        group
      rw [e, S510.commute_of_mem_stabCenter (hRc h1) g.2, mul_inv_cancel_right]
      exact h1
    have hZαP : ZM _ (baseA (puAmalgam h.le)) ≤ P := fun z hz =>
      ⟨(zm_le_qv_self _ hα hb0).trans (qv_le_stab _ _) hz, fun t ht => by
        have hzt : z * t = t * z := Subgroup.mem_centralizer_iff.1
          (Subgroup.le_centralizer_iff.1 (zm_le_centralizer_qv _ hyp hα) ht) z hz
        rw [commutatorElement_def, hzt, mul_inv_cancel_right, mul_inv_cancel]
        exact one_mem _⟩
    have hWP : W ≤ P := sup_le hnclP hZαP
    rw [Subgroup.commutator_le]
    intro w hw t ht
    exact (hWP hw).2 t ht
  obtain ⟨g₀, hg₀⟩ := exists_eq_smul_baseA _ hμM
  have hc₀ : IsCritical _ (baseA (puAmalgam h.le)) (g₀⁻¹ • γ) := by
    have := (isCritical_smul _ g₀⁻¹ _ _).2 hcμ
    rwa [hg₀, inv_smul_smul] at this
  have hΛ₀ : (2 ^ k) ^ 2 ≤ (Qv _ (g₀⁻¹ • γ)).relIndex (ZM _ (baseA (puAmalgam h.le))) := by
    have e := S5B.relIndex_qv_zm_smul g₀⁻¹ γ μ
    rw [hg₀, inv_smul_smul] at e
    rw [e, ← hg₀]
    exact hΛ
  have hone := (h52 G M T L h hmin hb k F _ _ a hd (g₀⁻¹ • γ) hc₀).1 hΛ₀
  have hVW : ⁅Vv _ (baseA (puAmalgam h.le)), puTrans h.le L (baseA _)⁆ ≤ W := by
    rcases hone.2 (ZM _ (baseA (puAmalgam h.le))) W (Vv _ (baseA (puAmalgam h.le))) le_rfl
      le_sup_right hWV le_rfl (stab_le_normalizer_zm _ _) hWn
      (stab_le_normalizer_of_smul _ (fun g ρ => vi_smul _ g ρ 2) _) with h1 | h1
    · exfalso
      refine hZhB (fun z hz => Subgroup.subset_closure ⟨hWV (S512N.le_nclStab _ _ _ |>.trans
        le_sup_left hz), fun t ht => h1 (Subgroup.commutator_mem_commutator
          ((S512N.le_nclStab _ _ _ |>.trans le_sup_left) hz) ht)⟩)
    · exact h1
  have hV₀W : ⁅S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ γ), puTrans h.le L (baseA _)⁆ ≤ W :=
    (Subgroup.commutator_mono hZγV le_rfl).trans hVW
  have hRD : R ≤ S5.dSub h.le L (baseA _) := by
    refine le_inf ?_ ?_
    · have hRZ : R ≤ ZM _ γ := by
        have hZμγ : ZM _ μ ≤ stab _ γ := zm_le_stab_of_isCritical _ hyp hb0 hcγμ
        exact Subgroup.le_normalizer_iff_commutator_le_right.1
          (hZμγ.trans (stab_le_normalizer_zm _ _))
      exact hRZ.trans (S512N.zm_le_qv_two h hb hγM hdαγ)
    · intro r hr
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      exact S510.commute_of_mem_stabCenter (hRc hr) (puTrans_le_stab h.le L _ ht)
  refine ⟨(Subgroup.commutator_mono hVW le_rfl).trans (hWR.trans hRD), ?_⟩
  exact (Subgroup.commutator_mono hV₀W hV₀W).trans
    (((Subgroup.commutator_mono le_rfl hWQ).trans hWR).trans hRD)

omit [Finite G] [Fintype F] in
theorem commutator_iSup_le_of' {ι : Type*} {A : ι → Subgroup G} {H N : Subgroup G}
    (hA : ∀ i, ⁅A i, H⁆ ≤ N) (hN : (⨆ i, A i) ≤ Subgroup.normalizer (N : Set G)) :
    ⁅⨆ i, A i, H⁆ ≤ N := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [Subgroup.iSup_eq_closure] at hx
  have hN' : Subgroup.closure (⋃ i, (A i : Set G)) ≤ Subgroup.normalizer (N : Set G) := by
    rw [← Subgroup.iSup_eq_closure]
    exact hN
  induction hx using Subgroup.closure_induction with
  | mem z hz =>
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    exact hA i (Subgroup.commutator_mem_commutator hi hy)
  | one => simp
  | mul a b ha hb iha ihb =>
    have hrw : ⁅a * b, y⁆ = a * ⁅b, y⁆ * a⁻¹ * ⁅a, y⁆ := by
      simp only [commutatorElement_def]
      group
    rw [hrw]
    exact N.mul_mem ((Subgroup.mem_normalizer_iff.mp (hN' ha) _).mp ihb) iha
  | inv a ha iha =>
    have hrw : ⁅a⁻¹, y⁆ = a⁻¹ * (⁅a, y⁆)⁻¹ * a⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [hrw]
    exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hN' ha)) _).mp (N.inv_mem iha)

theorem le_centralizer_commutator_of_le_qLine_M (h : PUHyp M T L)
    (hd : S5.IsSp4Data M T L k F a) {l : Submodule F (MSP.V4 F)} (hl : MSP.IsLine l)
    (hT : (T.subgroupOf M).map a ≤ MSP.qLine l) :
    T ≤ Subgroup.centralizer ((⁅Uq M T L, T⁆ : Subgroup G) : Set G) :=
  S512T.le_centralizer_of_map_le_M h hd h.le h.le
    (hT.trans (MSP.fixer_antitone ((MSP.commSp_mono hT).trans (MSP.commSp_qLine_le hl))))

theorem qv_le_centralizer_commutator_of_le_qLine (h : PUHyp M T L)
    (hd : S5.IsSp4Data M T L k F a) {l : Submodule F (MSP.V4 F)} (hl : MSP.IsLine l)
    (hTl : Qv _ (baseB (puAmalgam h.le)) ≤ S5.vPre h.le a (MSP.qLine l))
    {δ ε : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ) (hδε : (puAmalgam h.le).treeGraph.Adj δ ε) :
    Qv _ ε ≤ Subgroup.centralizer ((⁅S5.uSub h.le L δ, Qv _ ε⁆ : Subgroup _) :
      Set (puAmalgam h.le).Universal) := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨c, rfl, rfl⟩ := exists_smul_base_edge _ hδ hδε
  have hU : S5.uSub h.le L (c • baseA (puAmalgam h.le)) =
      (imM h.le (Uq M T L)).map (MulAut.conj c).toMonoidHom := by
    rw [S5B.uSub_smul h.le hLn, S5B.uSub_baseA h]
  have hQε : Qv _ (c • baseB (puAmalgam h.le)) =
      (imM h.le T).map (MulAut.conj c).toMonoidHom := by
    rw [qv_smul, puAmalgam.qv_baseB]
  have hTl' : (T.subgroupOf M).map a ≤ MSP.qLine l :=
    S512T.imSp_le_of_imM_le_vPre h.le (by rw [← puAmalgam.qv_baseB]; exact hTl)
  have key := le_centralizer_commutator_of_le_qLine_M h hd hl hTl'
  have hcommM : ⁅Uq M T L, T⁆ ≤ M := commutator_le_of_le (Uq_le h.L_le) h.le
  rw [hU, hQε, ← Subgroup.map_commutator, ← imM_commutator h.le (Uq_le h.L_le) h.le,
    PU.centralizer_map_mulEquiv, map_conj_le_map_conj_iff,
    S512T.imM_le_centralizer_iff h.le h.le hcommM]
  exact key

theorem commutator_zm_qv_le_centralizer (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    (hb : 2 < critDist (puAmalgam h.le)) {l : Submodule F (MSP.V4 F)} (hl : MSP.IsLine l)
    (hTl : Qv _ (baseB (puAmalgam h.le)) ≤ S5.vPre h.le a (MSP.qLine l))
    {δ : Vtx (puAmalgam h.le)} (hβδ : (puAmalgam h.le).treeGraph.Adj (baseB _) δ) :
    ⁅ZM _ δ, Qv _ (baseA (puAmalgam h.le))⁆ ≤
      Subgroup.centralizer (Qv _ (baseB (puAmalgam h.le)) : Set (puAmalgam h.le).Universal) := by
  have hyp := h.hyp20
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hδM : IsMVtx _ δ := (isMVtx_iff_of_adj _ hβδ.symm).2 (not_isMVtx_baseB _)
  have hQαβ : Qv _ (baseA (puAmalgam h.le)) ≤ Qv _ (baseB (puAmalgam h.le)) :=
    qv_le_qv _ hyp hα (adj_baseA_baseB _)
  have hZδβ : ZM _ δ ≤ Qv _ (baseB (puAmalgam h.le)) :=
    zm_le_qv_of_dist_lt _ hδM (by rw [dist_eq_one_of_adj _ hβδ.symm]; omega)
  have hN : Qv _ (baseB (puAmalgam h.le)) ≤ Subgroup.normalizer
      (Subgroup.centralizer (Qv _ (baseB (puAmalgam h.le)) : Set (puAmalgam h.le).Universal) :
        Set (puAmalgam h.le).Universal) :=
    S310.le_normalizer_centralizer Subgroup.le_normalizer
  rw [S5B.zm_eq_zh_sup_uSub h hδM hβδ.symm]
  refine S310.commutator_sup_left_le (((zh_le_zm _ hβδ.symm).trans hZδβ).trans hN)
    (((S5B.uSub_le_zm h.le δ).trans hZδβ).trans hN) ?_ ?_
  · rw [Subgroup.commutator_eq_bot_iff_le_centralizer.2
      ((zh_le_centralizer _ _).trans (Subgroup.centralizer_le hQαβ))]
    exact bot_le
  · exact (Subgroup.commutator_mono le_rfl hQαβ).trans (Subgroup.le_centralizer_iff.1
      (qv_le_centralizer_commutator_of_le_qLine h hd hl hTl hδM hβδ.symm))

theorem vv_le_voSub_sup (h : PUHyp M T L) :
    Vv _ (baseA (puAmalgam h.le)) ≤ S5.voSub h.le L (baseA _) ⊔
      ⨆ δ : {δ : Vtx (puAmalgam h.le) // (puAmalgam h.le).treeGraph.Adj (baseB _) δ},
        ZM _ δ.1 := by
  have hyp := h.hyp20
  have hα := isMVtx_baseA (puAmalgam h.le)
  set Vb := ⨆ δ : {δ : Vtx (puAmalgam h.le) // (puAmalgam h.le).treeGraph.Adj (baseB _) δ},
    ZM _ δ.1 with hVb
  have hZVb : ∀ {δ : Vtx (puAmalgam h.le)}, (puAmalgam h.le).treeGraph.Adj (baseB _) δ →
      ZM _ δ ≤ Vb := fun {δ} hδ =>
    le_iSup (f := fun δ : {δ : Vtx (puAmalgam h.le) //
      (puAmalgam h.le).treeGraph.Adj (baseB _) δ} => ZM _ δ.1) ⟨δ, hδ⟩
  have hZα : ZM _ (baseA (puAmalgam h.le)) ≤ Vb := hZVb (adj_baseA_baseB _).symm
  refine iSup₂_le fun ρ hρ => ?_
  have hρ' : (puAmalgam h.le).treeGraph.dist (baseA _) ρ ≤ 2 := hρ
  by_cases hρM : IsMVtx _ ρ
  · rw [zv_of_isMVtx _ hρM]
    have heven : Even ((puAmalgam h.le).treeGraph.dist (baseA _) ρ) :=
      (even_dist_iff _ _ _).2 ⟨fun _ => hρM, fun _ => hα⟩
    rcases Nat.lt_or_ge ((puAmalgam h.le).treeGraph.dist (baseA _) ρ) 1 with h0 | h2
    · have : (puAmalgam h.le).treeGraph.dist (baseA _) ρ = 0 := by omega
      rw [(dist_eq_zero_iff _).1 this] at hZα
      exact hZα.trans le_sup_right
    · have hd2 : (puAmalgam h.le).treeGraph.dist (baseA _) ρ = 2 := by
        obtain ⟨r, hr⟩ := heven
        omega
      have hαβ₁ : (puAmalgam h.le).treeGraph.Adj (baseA _) (geo _ (baseA (puAmalgam h.le)) ρ 1) :=
        adj_geo_one _ (by omega)
      have hβ₁ρ : (puAmalgam h.le).treeGraph.Adj (geo _ (baseA (puAmalgam h.le)) ρ 1) ρ := by
        have := adj_geo _ (u := baseA (puAmalgam h.le)) (w := ρ) (i := 1) (by omega)
        rwa [show (1 : ℕ) + 1 = 2 by rfl, ← hd2, geo_dist] at this
      obtain ⟨g, hg, hgβ⟩ := exists_mem_stab_smul _ (adj_baseA_baseB (puAmalgam h.le)) hαβ₁
      obtain ⟨l, hl, t, ht, hglt⟩ := S310.exists_mul_of_mem_stab h (adj_baseA_baseB _) hg
      have hδ₀ : (puAmalgam h.le).treeGraph.Adj (baseB _) (g⁻¹ • ρ) := by
        have := (adj_smul _ g⁻¹ _ _).2 hβ₁ρ
        rwa [← hgβ, inv_smul_smul] at this
      have hρe : ρ = g • (g⁻¹ • ρ) := (smul_inv_smul g ρ).symm
      have hδ₀M : IsMVtx _ (g⁻¹ • ρ) := (isMVtx_iff_of_adj _ hδ₀.symm).2 (not_isMVtx_baseB _)
      have hdδ₀ : (puAmalgam h.le).treeGraph.dist (baseA _) (g⁻¹ • ρ) ≤ 2 := by
        have := dist_smul _ g⁻¹ (baseA (puAmalgam h.le)) ρ
        rw [(mem_stab _).1 (inv_mem hg)] at this
        rw [this, hd2]
      rw [hρe, zm_smul]
      rintro _ ⟨z, hz, rfl⟩
      have htz : t * z * t⁻¹ ∈ ZM _ (g⁻¹ • ρ) :=
        (Subgroup.mem_normalizer_iff.1 (stab_le_normalizer_zm _ _
          (qv_le_stab_of_adj _ hδ₀ ht)) z).1 hz
      have hc' : ⁅l, t * z * t⁻¹⁆ ∈ S5.voSub h.le L (baseA (puAmalgam h.le)) := by
        show ⁅l, t * z * t⁻¹⁆ ∈ ⁅Vv _ (baseA (puAmalgam h.le)), puTrans h.le L (baseA _)⁆
        rw [Subgroup.commutator_comm]
        exact Subgroup.commutator_mem_commutator hl (S5B.zm_le_vv_of_dist hδ₀M hdδ₀ htz)
      have e : (MulAut.conj g).toMonoidHom z = ⁅l, t * z * t⁻¹⁆ * (t * z * t⁻¹) := by
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hglt]
        simp only [commutatorElement_def]
        group
      rw [e]
      exact mul_mem (Subgroup.mem_sup_left hc') (Subgroup.mem_sup_right (hZVb hδ₀ htz))
  · rw [zv_of_not_isMVtx _ hρM]
    have hd1 : (puAmalgam h.le).treeGraph.dist (baseA _) ρ = 1 := by
      have hodd : ¬ Even ((puAmalgam h.le).treeGraph.dist (baseA _) ρ) := fun he =>
        hρM (((even_dist_iff _ _ _).1 he).1 hα)
      have h0 : (puAmalgam h.le).treeGraph.dist (baseA _) ρ ≠ 0 := fun h0 => hodd (h0 ▸ ⟨0, rfl⟩)
      have h2 : (puAmalgam h.le).treeGraph.dist (baseA _) ρ ≠ 2 := fun h2 => hodd (h2 ▸ ⟨1, rfl⟩)
      omega
    have hadj : (puAmalgam h.le).treeGraph.Adj (baseA _) ρ :=
      SimpleGraph.dist_eq_one_iff_adj.1 hd1
    exact (zh_le_zm _ hadj).trans (hZα.trans le_sup_right)

theorem fullVQD56_holds (h52 : S52) (h54 : S54) (h55 : S55) (h56 : S56) :
    ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
      PUMin M T L → critDist (puAmalgam h.le) = 4 →
      ∀ (k : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (a : ↥M →* ↥(StatedSp 2 F)),
        S5.IsSp4Data M T L k F a →
        ∀ α' : Vtx (puAmalgam h.le), IsCritical _ (baseA _) α' → geo _ (baseA _) α' 1 = baseB _ →
        ∀ l : Submodule F (MSP.V4 F), S5.Case56 h (2 ^ k) a (geo _ (baseA (puAmalgam h.le)) α' 2) l →
        ∀ μ : Vtx (puAmalgam h.le),
          (∃ y ∈ stab _ (baseA (puAmalgam h.le)), μ = y • geo _ (baseA (puAmalgam h.le)) α' 2) →
          IsCritical _ μ (geo _ (baseA (puAmalgam h.le)) α' 2) →
          2 ^ k < (Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2)).relIndex (ZM _ μ) →
          ⁅ZM (puAmalgam h.le) μ, ZM (puAmalgam h.le) (geo _ (baseA (puAmalgam h.le)) α' 2)⁆ ≤
            stabCenter _ (baseA (puAmalgam h.le)) →
          ⁅Vv _ (baseA (puAmalgam h.le)), Qv _ (baseA (puAmalgam h.le))⁆ ≤ S5.dSub h.le L (baseA _) := by
  intro G _ _ M T L h hmin hb4 k F _ _ a hd α' hc hαβ l hl μ ⟨y, hy, hμy⟩ hcμ hbad hRc
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have h1 := (core56_facts h52 h55 h56 h hmin hb4 hd hc hy hμy hcμ hbad hRc).1
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
  have hTl : Qv _ (baseB (puAmalgam h.le)) ≤ S5.vPre h.le a (MSP.qLine l') := hJT ▸ hJl'
  have hDn : stab _ (baseA (puAmalgam h.le)) ≤
      Subgroup.normalizer (S5.dSub h.le L (baseA _) : Set (puAmalgam h.le).Universal) :=
    S310.le_normalizer_inf (stab_le_normalizer_qv _ _)
      (S310.le_normalizer_centralizer (stab_le_normalizer_puTrans h.le hLn _))
  have hQβst : Qv _ (baseB (puAmalgam h.le)) ≤ stab _ (baseA (puAmalgam h.le)) :=
    qv_le_stab_of_adj _ (adj_baseA_baseB _).symm
  set N := (stab _ (baseA (puAmalgam h.le)) ⊓ Subgroup.centralizer
    (Qv _ (baseB (puAmalgam h.le)) : Set (puAmalgam h.le).Universal)) ⊔
      S5.dSub h.le L (baseA _) with hNdef
  have hNn : Qv _ (baseB (puAmalgam h.le)) ≤ Subgroup.normalizer (N : Set _) :=
    le_normalizer_sup (S310.le_normalizer_inf (hQβst.trans Subgroup.le_normalizer)
      (S310.le_normalizer_centralizer Subgroup.le_normalizer)) (hQβst.trans hDn)
  have hVQ : Vv _ (baseA (puAmalgam h.le)) ≤ Qv _ (baseA (puAmalgam h.le)) :=
    S310.vv_le_qv_baseA h hb
  have hQαβ : Qv _ (baseA (puAmalgam h.le)) ≤ Qv _ (baseB (puAmalgam h.le)) :=
    qv_le_qv _ hyp hα (adj_baseA_baseB _)
  have hVoβ : S5.voSub h.le L (baseA (puAmalgam h.le)) ≤ Qv _ (baseB (puAmalgam h.le)) :=
    ((Subgroup.le_normalizer_iff_commutator_le_left.1 ((puTrans_le_stab h.le L _).trans
      (stab_le_normalizer_of_smul _ (fun g ρ => vi_smul _ g ρ 2) _))).trans hVQ).trans hQαβ
  have hVbβ : (⨆ δ : {δ : Vtx (puAmalgam h.le) // (puAmalgam h.le).treeGraph.Adj (baseB _) δ},
      ZM _ δ.1) ≤ Qv _ (baseB (puAmalgam h.le)) :=
    iSup_le fun δ => zm_le_qv_of_dist_lt _
      ((isMVtx_iff_of_adj _ δ.2.symm).2 (not_isMVtx_baseB _))
      (by rw [dist_eq_one_of_adj _ δ.2.symm]; omega)
  have hVbN : ⁅⨆ δ : {δ : Vtx (puAmalgam h.le) // (puAmalgam h.le).treeGraph.Adj (baseB _) δ},
      ZM _ δ.1, Qv _ (baseA (puAmalgam h.le))⁆ ≤ N := by
    refine commutator_iSup_le_of' (fun δ => ?_) (hVbβ.trans hNn)
    refine le_sup_left.trans' (le_inf ?_ (commutator_zm_qv_le_centralizer h hd hb hl' hTl δ.2))
    exact commutator_le_of_le ((zm_le_qv_of_dist_lt _
      ((isMVtx_iff_of_adj _ δ.2.symm).2 (not_isMVtx_baseB _))
      (by rw [dist_eq_one_of_adj _ δ.2.symm]; omega)).trans hQβst) (qv_le_stab _ _)
  have hX : ⁅Vv _ (baseA (puAmalgam h.le)), Qv _ (baseA (puAmalgam h.le))⁆ ≤ N :=
    (Subgroup.commutator_mono (vv_le_voSub_sup h) le_rfl).trans
      (S310.commutator_sup_left_le (hVoβ.trans hNn) (hVbβ.trans hNn) (h1.trans le_sup_right) hVbN)
  have hcr' := ms22_iii _ hyp hb0 h.centHyp hc
  obtain ⟨z, hz, hzQ⟩ := Set.not_subset.1 hcr'.2.2
  have hZ'β : ZM _ α' ≤ Qv _ (baseB (puAmalgam h.le)) := by
    refine zm_le_qv_of_dist_lt _ (hc.isMVtx_right _ hyp) ?_
    rw [← hαβ, SimpleGraph.dist_comm, dist_geo_right _ (by have := hc.2.1; omega), hc.2.1]
    omega
  have hzβ : z ∈ Qv _ (baseB (puAmalgam h.le)) := hZ'β hz
  have hzst : z ∈ stab _ (baseA (puAmalgam h.le)) := hQβst hzβ
  have hWst : ⁅Vv _ (baseA (puAmalgam h.le)), Qv _ (baseA (puAmalgam h.le))⁆ ≤
      stab _ (baseA (puAmalgam h.le)) :=
    commutator_le_of_le (hVQ.trans (qv_le_stab _ _)) (qv_le_stab _ _)
  have hL2 := S310.commutator_le_of_two_elt_baseA h hWst
    (inf_le_left.trans (qv_le_stab _ _))
    (le_normalizer_commutator ((puTrans_le_stab h.le L _).trans
      (stab_le_normalizer_of_smul _ (fun g ρ => vi_smul _ g ρ 2) _))
      ((puTrans_le_stab h.le L _).trans (stab_le_normalizer_qv _ _)))
    ((puTrans_le_stab h.le L _).trans hDn) hzst
    ⟨1, by
      have := (isElemAbelian_zm _ hyp hb0 (hc.isMVtx_right _ hyp)).2 z hz
      simpa using this⟩ hzQ (hDn hzst) (fun w hw => by
      have hwN := hX hw
      rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _
        (inf_le_left.trans hDn)] at hwN
      obtain ⟨c, hcC, d, hdD, rfl⟩ := hwN
      have hcz : z * c = c * z := Subgroup.mem_centralizer_iff.1 hcC.2 z hzβ
      have hzd : z * d * z⁻¹ ∈ S5.dSub h.le L (baseA _) :=
        (Subgroup.mem_normalizer_iff.1 (hDn hzst) d).1 hdD
      have e : z * (c * d) * z⁻¹ * (c * d)⁻¹ = c * ((z * d * z⁻¹) * d⁻¹) * c⁻¹ := by
        calc z * (c * d) * z⁻¹ * (c * d)⁻¹ = (z * c) * d * z⁻¹ * d⁻¹ * c⁻¹ := by group
          _ = (c * z) * d * z⁻¹ * d⁻¹ * c⁻¹ := by rw [hcz]
          _ = c * ((z * d * z⁻¹) * d⁻¹) * c⁻¹ := by group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.1 (hDn hcC.1) _).1 (mul_mem hzd (inv_mem hdD)))
  have hXL : ⁅⁅Vv _ (baseA (puAmalgam h.le)), Qv _ (baseA (puAmalgam h.le))⁆,
      puTrans h.le L (baseA _)⁆ ≤ ⊥ :=
    S5B.commutator_le_of_perfect (S512N.perfect_puTrans h)
      (fun x _ => by rw [Subgroup.normalizer_eq_top ⊥]; exact Subgroup.mem_top x)
      (fun x _ => by rw [Subgroup.normalizer_eq_top ⊥]; exact Subgroup.mem_top x) hL2
      (Subgroup.commutator_eq_bot_iff_le_centralizer.2 inf_le_right).le
  refine le_inf ?_ (Subgroup.commutator_eq_bot_iff_le_centralizer.1 (le_bot_iff.1 hXL))
  rw [Subgroup.commutator_comm]
  exact commutator_le_left_of_le_normalizer
    ((hVQ.trans (qv_le_stab _ _)).trans (stab_le_normalizer_qv _ _))

end S512R

end CFSG.Quasithin.MS93
