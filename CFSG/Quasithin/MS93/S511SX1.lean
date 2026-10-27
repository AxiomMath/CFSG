module

public import CFSG.Quasithin.MS93.S511SV
public import CFSG.Quasithin.MS93.S511SMod
public import CFSG.Quasithin.MS93.S511SVec

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

namespace S511S

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem commutator_xm_le_uSub_gp (h32 : S32) (h : PUHyp M T L) {ρ : Vtx (puAmalgam h.le)}
    (hρ : IsMVtx _ ρ) : ⁅XM _ ρ, puTrans h.le L ρ⁆ ≤ S5.uSub h.le L ρ := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ hρ
  have key := S5C56.commutator_xm_puTrans_le_uSub h32 h
  rw [xm_smul, puTrans_smul h.le hLn, S5B.uSub_smul h.le hLn, ← Subgroup.map_commutator]
  exact Subgroup.map_mono key

theorem lt_relIndex_centralizer_qv (h32 : S32) (h59 : S5B.S59) (h : PUHyp M T L)
    (hmin : PUMin M T L) (hb : 4 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a)
    {μ μ' : Vtx (puAmalgam h.le)} (hc : IsCritical _ μ μ') :
    2 ^ k < (Subgroup.centralizer (Qv _ μ : Set (puAmalgam h.le).Universal)).relIndex
      (S5.uSub h.le L (geo _ μ μ' 2)) := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have key := S510.s59_gp h59 h hmin hb hd hc
  have hd2 : (puAmalgam h.le).treeGraph.dist μ μ' = critDist (puAmalgam h.le) := hc.2.1
  set ρ := geo _ μ μ' 2 with hρ
  have hμ : IsMVtx _ μ := hc.1
  have hρM : IsMVtx _ ρ := isMVtx_geo_two _ hyp hb0 hc
  have hdμρ : (puAmalgam h.le).treeGraph.dist μ ρ = 2 := dist_geo _ (by omega)
  have hUZ : S5.uSub h.le L ρ ≤ ZM _ ρ := S5B.uSub_le_zm h.le _
  have hUQ : S5.uSub h.le L ρ ≤ Qv _ μ :=
    hUZ.trans (zm_le_qv_of_dist_lt _ hρM (by rw [tdist_comm]; omega))
  have hXL := commutator_xm_le_uSub_gp h32 h hμ
  have hUμZ : S5.uSub h.le L μ ≤ ZM _ μ := S5B.uSub_le_zm h.le _
  have hCB : Subgroup.centralizer (Qv _ μ : Set (puAmalgam h.le).Universal) ⊓
      S5.uSub h.le L ρ ≤ S5.bSub h.le L μ ⊓ S5.uSub h.le L ρ := by
    rintro u ⟨huC, huU⟩
    have huX : u ∈ XM _ μ :=
      mem_omegaOneCenterOf (hUQ huU) (fun y hy => Subgroup.mem_centralizer_iff.1 huC y hy)
        (sq_eq_one_of_mem_omegaOneCenterOf (zm_le_xm _ hyp hb0 hρM (hUZ huU)))
    refine ⟨Subgroup.subset_closure ⟨S38E.zm_le_vv _ hρM hdμρ.le (hUZ huU), fun y hy => ?_⟩,
      huU⟩
    exact hUμZ (hXL (Subgroup.commutator_mem_commutator huX hy))
  have hUfin : Finite ↥(S5.uSub h.le L ρ) := by
    obtain ⟨-, hfin⟩ := isPGroup_vv h (by omega) hρM
    exact Finite.of_injective _ (Subgroup.inclusion_injective
      (hUZ.trans (S38E.zm_le_vv (α := ρ) _ hρM (by simp))))
  have hle : (S5.bSub h.le L μ).relIndex (S5.uSub h.le L ρ) ≤
      (Subgroup.centralizer (Qv _ μ : Set (puAmalgam h.le).Universal)).relIndex
        (S5.uSub h.le L ρ) := by
    rw [← Subgroup.inf_relIndex_right (S5.bSub h.le L μ),
      ← Subgroup.inf_relIndex_right (Subgroup.centralizer (Qv _ μ :
        Set (puAmalgam h.le).Universal))]
    exact Subgroup.relIndex_le_of_le_left hCB
      (by rw [Subgroup.relIndex]; exact Subgroup.index_ne_zero_of_finite)
  omega

theorem finrank_fixSp_vIm_le_two (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {E : Subgroup (puAmalgam h.le).Universal} (hE : E ≤ stab _ (baseA (puAmalgam h.le)))
    (hrel : 2 ^ k < (Subgroup.centralizer (E : Set (puAmalgam h.le).Universal)).relIndex
      (S5.uSub h.le L (baseA (puAmalgam h.le)))) :
    Module.finrank F ↥(MSP.fixSp (S5.vIm h.le a E)) ≤ 2 := by
  obtain ⟨c⟩ := MSP.nonempty_natCoord hd.2.2.2
  have hlift := (sp4Lift_holds G M T L h k F _ _ a hd).2.2
  have hFq : Nat.card F = 2 ^ k := by rw [Nat.card_eq_fintype_card, hd.2.1]
  rw [puAmalgam.stab_baseA] at hE
  obtain ⟨E₀, -, hE₀M, rfl⟩ := S5.exists_eq_imM h.le hE
  have hUM : Uq M T L ≤ M := Uq_le h.L_le
  rw [S5B.uSub_baseA h, S5B.relIndex_centralizer_imM h.le hUM hE₀M] at hrel
  have hmul := S5B.relIndex_centralizer_mul_card h hlift c hE₀M
  rw [MSP.card_V4, hFq, Module.natCard_eq_pow_finrank (K := F), hFq] at hmul
  rw [S5B.vIm_imM h.le]
  set d := Module.finrank F ↥(MSP.fixSp ((E₀.subgroupOf M).map a))
  set r := (Subgroup.centralizer (E₀ : Set G)).relIndex (Uq M T L)
  have hq : 1 < 2 ^ k := Nat.one_lt_two_pow (by have := hd.1; omega)
  by_contra hd3
  push Not at hd3
  have h3 : (2 ^ k) ^ 3 ≤ (2 ^ k) ^ d := Nat.pow_le_pow_right (by omega) hd3
  have h4 : 2 ^ k * (2 ^ k) ^ 3 < r * (2 ^ k) ^ 3 :=
    Nat.mul_lt_mul_of_pos_right hrel (by positivity)
  have h5 : r * (2 ^ k) ^ 3 ≤ r * (2 ^ k) ^ d := Nat.mul_le_mul_left r h3
  have h6 : (2 ^ k) ^ 4 = 2 ^ k * (2 ^ k) ^ 3 := by ring
  omega

omit [Fintype F] in
theorem vIm_stab_baseA (h : PUHyp M T L) (ha : Function.Surjective a) :
    S5.vIm h.le a (stab _ (baseA (puAmalgam h.le))) = ⊤ := by
  rw [puAmalgam.stab_baseA, S5B.vIm_imM h.le, Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map,
    MonoidHom.range_eq_top]
  exact ha

theorem vIm_qv_baseA (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a) :
    S5.vIm h.le a (Qv _ (baseA (puAmalgam h.le))) = ⊥ := by
  rw [S5B.qv_baseA_eq h, S5B.vIm_imM h.le, eq_bot_iff]
  rintro _ ⟨m, hm, rfl⟩
  have hmQ : (m : G) ∈ pCoreOf 2 M := Subgroup.mem_subgroupOf.1 hm
  have h1 := ((S5.mem_kerG a).1 (hd.pCoreOf_le_kerG h hmQ)).2
  rw [Subgroup.mem_bot]
  exact h1

omit [Fintype F] in
theorem vIm_rconj_eq (h : PUHyp M T L) {y : (puAmalgam h.le).Universal}
    (hy : y ∈ stab _ (baseA (puAmalgam h.le))) {K K' : Subgroup (puAmalgam h.le).Universal}
    (hK : S5.vIm h.le a K = S5.vIm h.le a K') :
    S5.vIm h.le a (S5.rconj y K) = S5.vIm h.le a (S5.rconj y K') := by
  have hy' : y⁻¹ ∈ (puAmalgam h.le).ofA.range := by
    rw [S5.ofA_range_eq]
    exact inv_mem hy
  obtain ⟨m, hm⟩ := hy'
  rw [S5B.rconj_eq_map, S5B.rconj_eq_map, ← hm, S5.vIm_map_conj, S5.vIm_map_conj, hK]

theorem fixSp_vIm_qv_inf_eq_bot (h32 : S32) (h59 : S5B.S59) (h : PUHyp M T L)
    (hmin : PUMin M T L) (hb : 4 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a)
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    (hαβ : geo _ (baseA (puAmalgam h.le)) α' 1 = baseB _) {l : Submodule F (MSP.V4 F)}
    (hl : S5.Case56 h (2 ^ k) a (geo _ (baseA (puAmalgam h.le)) α' 2) l)
    {y : (puAmalgam h.le).Universal} (hy : y ∈ stab _ (baseA (puAmalgam h.le)))
    (hgen : ∀ E₁ E₂ : Subgroup (puAmalgam h.le).Universal, IsPGroup 2 E₁ → IsPGroup 2 E₂ →
      E₁ ≤ S5.rconj y (S5.vPre h.le a (MSP.qLine l)) → E₂ ≤ S5.vPre h.le a (MSP.qLine l) →
      (2 ^ k) ^ 2 < (Qv _ (baseA _)).relIndex E₁ → (2 ^ k) ^ 2 < (Qv _ (baseA _)).relIndex E₂ →
      E₁ ⊔ E₂ ⊔ Qv _ (baseA _) = stab _ (baseA _))
    {μ' : Vtx (puAmalgam h.le)} (hcμ : IsCritical _ (y⁻¹ • geo _ (baseA (puAmalgam h.le)) α' 2) μ')
    (hμα : geo _ (y⁻¹ • geo _ (baseA (puAmalgam h.le)) α' 2) μ' 2 = baseA _) :
    MSP.fixSp (S5.vIm h.le a (Qv _ (y⁻¹ • geo _ (baseA (puAmalgam h.le)) α' 2))) ⊓ l = ⊥ := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hd2 : (puAmalgam h.le).treeGraph.dist (baseA _) α' = critDist (puAmalgam h.le) := hc.2.1
  set γ := geo _ (baseA (puAmalgam h.le)) α' 2 with hγ
  set Q₁ := S5.vPre h.le a (MSP.qLine l) with hQ₁
  have hβγ : (puAmalgam h.le).treeGraph.Adj γ (baseB (puAmalgam h.le)) := by
    have := adj_geo _ (u := baseA (puAmalgam h.le)) (w := α') (i := 1) (by omega)
    rw [hαβ] at this
    exact this.symm
  have hγM : IsMVtx _ γ := isMVtx_geo_two _ hyp hb0 hc
  have hQγ : Qv _ γ ≤ Q₁ :=
    (S5B.qv_le_jOff h Nat.one_le_two_pow hγM hβγ).trans (hl.1.le.trans hl.2.2.2)
  have hQ₁st : Q₁ ≤ stab _ (baseA (puAmalgam h.le)) := S5.vPre_le_stab h _
  have hQμ : Qv _ (y⁻¹ • γ) ≤ S5.rconj y Q₁ := by
    rw [qv_smul, S5B.rconj_eq_map]
    exact Subgroup.map_mono hQγ
  have hrQ : S5.rconj y Q₁ ≤ stab _ (baseA (puAmalgam h.le)) := S5.rconj_le_stab h hQ₁st hy
  have hrel := lt_relIndex_centralizer_qv h32 h59 h hmin hb hd hcμ
  rw [hμα] at hrel
  have hfin := finrank_fixSp_vIm_le_two h hd (hQμ.trans hrQ) hrel
  obtain ⟨hl2, hlc⟩ := S5C56.isPGroup_qLine hd hl.2.1
  obtain ⟨E, hEle, hE2, hEim⟩ := S5C56.exists_isPGroup_vIm_eq h hd hl2
  have hEst : E ≤ stab _ (baseA (puAmalgam h.le)) := hEle.trans hQ₁st
  have hErel : (Qv _ (baseA (puAmalgam h.le))).relIndex E = (2 ^ k) ^ 3 := by
    rw [← S5.card_vIm h hd hEst hE2, hEim, hlc]
  have hk : 1 ≤ k := hd.1
  have hlt : (2 ^ k) ^ 2 < (Qv _ (baseA (puAmalgam h.le))).relIndex E := by
    rw [hErel]
    exact Nat.pow_lt_pow_right (Nat.one_lt_two_pow (by omega)) (by norm_num)
  have hst := hgen (S5.rconj y E) E (hE2.map _) hE2 ((S5B.rconj_le_rconj_iff (g := y)).2 hEle)
    hEle (by rw [S5C56.relIndex_rconj h hy]; exact hlt) hlt
  have hrE : S5.rconj y E ≤ stab _ (baseA (puAmalgam h.le)) := S5.rconj_le_stab h hEst hy
  have hrange : ∀ K : Subgroup (puAmalgam h.le).Universal,
      K ≤ stab _ (baseA (puAmalgam h.le)) → K ≤ (puAmalgam h.le).ofA.range := fun K hK => by
    rw [S5.ofA_range_eq]
    exact hK
  have hQαst : Qv _ (baseA (puAmalgam h.le)) ≤ stab _ (baseA (puAmalgam h.le)) :=
    qv_le_stab _ _
  have htop : S5.vIm h.le a (S5.rconj y E) ⊔ S5.vIm h.le a E = ⊤ := by
    have e1 := congrArg (S5.vIm h.le a) hst
    rw [vIm_stab_baseA h hd.2.2.1,
      S5.vIm_sup h.le (hrange _ (sup_le hrE hEst)) (hrange _ hQαst),
      S5.vIm_sup h.le (hrange _ hrE) (hrange _ hEst), vIm_qv_baseA h hd, sup_bot_eq] at e1
    exact e1
  have : CharP F 2 := S5B.charP_two_of_card hd.2.1
  have hbot := fixSp_sup_eq_bot htop
  have hW : S5.vIm h.le a (S5.rconj y Q₁) = S5.vIm h.le a (S5.rconj y E) :=
    vIm_rconj_eq h hy (by rw [hEim, hQ₁, S5.vIm_vPre h hd])
  have hfixE : MSP.fixSp (S5.vIm h.le a E) = l := by rw [hEim, MSP.fixSp_qLine hl.2.1]
  have hy' : y⁻¹ ∈ (puAmalgam h.le).ofA.range := by
    rw [S5.ofA_range_eq]
    exact inv_mem hy
  obtain ⟨m, hm⟩ := hy'
  have hline : MSP.IsLine (MSP.fixSp (S5.vIm h.le a (S5.rconj y E))) := by
    rw [S5B.rconj_eq_map, ← hm, S5.vIm_map_conj, hEim, MSP.fixSp_map_conj, MSP.fixSp_qLine hl.2.1]
    exact MSP.isLine_map hl.2.1 _
  have hle : MSP.fixSp (S5.vIm h.le a (S5.rconj y E)) ≤
      MSP.fixSp (S5.vIm h.le a (Qv _ (y⁻¹ • γ))) := by
    rw [← hW]
    exact MSP.fixSp_antitone (S5.vIm_mono' h hQμ)
  have heq : MSP.fixSp (S5.vIm h.le a (S5.rconj y E)) =
      MSP.fixSp (S5.vIm h.le a (Qv _ (y⁻¹ • γ))) :=
    Submodule.eq_of_le_of_finrank_le hle (by rw [hline.1]; exact hfin)
  rw [← heq, ← hfixE]
  exact hbot

omit [Fintype F] in
theorem GoodLamF.exists_conj {h : PUHyp M T L} {α' μ : Vtx (puAmalgam h.le)}
    (hgood : GoodLamF h (2 ^ k) a α' μ) :
    ∃ (l : Submodule F (MSP.V4 F)) (y : (puAmalgam h.le).Universal),
      S5.Case56 h (2 ^ k) a (geo _ (baseA (puAmalgam h.le)) α' 2) l ∧
      y ∈ stab _ (baseA (puAmalgam h.le)) ∧ μ = y⁻¹ • geo _ (baseA (puAmalgam h.le)) α' 2 ∧
      ∀ E₁ E₂ : Subgroup (puAmalgam h.le).Universal, IsPGroup 2 E₁ → IsPGroup 2 E₂ →
        E₁ ≤ S5.rconj y (S5.vPre h.le a (MSP.qLine l)) → E₂ ≤ S5.vPre h.le a (MSP.qLine l) →
        (2 ^ k) ^ 2 < (Qv _ (baseA _)).relIndex E₁ → (2 ^ k) ^ 2 < (Qv _ (baseA _)).relIndex E₂ →
        E₁ ⊔ E₂ ⊔ Qv _ (baseA _) = stab _ (baseA _) := by
  obtain ⟨l, g, x, hl, hg, hx, hconc, rfl | ⟨rfl, -⟩⟩ := hgood
  · exact ⟨l, g, hl, hg, rfl, hconc.1.1.1⟩
  · refine ⟨l, g * x, hl, mul_mem hg (puTrans_le_stab h.le L _ hx), ?_, hconc.2⟩
    rw [mul_inv_rev, mul_smul]

theorem qv_smul_le_stab (h : PUHyp M T L) {γ ε : Vtx (puAmalgam h.le)} (hγ : IsMVtx _ γ)
    (hγε : (puAmalgam h.le).treeGraph.Adj γ ε)
    (hεα : (puAmalgam h.le).treeGraph.Adj ε (baseA (puAmalgam h.le)))
    {y : (puAmalgam h.le).Universal} (hy : y ∈ stab _ (baseA (puAmalgam h.le))) :
    Qv _ (y⁻¹ • γ) ≤ stab _ (baseA (puAmalgam h.le)) := by
  have hQ : Qv _ γ ≤ stab _ (baseA (puAmalgam h.le)) :=
    (qv_le_qv _ h.hyp20 hγ hγε).trans (qv_le_stab_of_adj _ hεα)
  rw [qv_smul]
  rintro _ ⟨z, hz, rfl⟩
  have h1 := mul_mem (mul_mem (inv_mem hy) (hQ hz)) hy
  simpa [MulAut.conj_apply] using h1

theorem goodF_fixSp (h32 : S32) (h59 : S5B.S59) (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb : 4 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a)
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    (hαβ : geo _ (baseA (puAmalgam h.le)) α' 1 = baseB _) {μ : Vtx (puAmalgam h.le)}
    (hgood : GoodLamF h (2 ^ k) a α' μ) {μ' : Vtx (puAmalgam h.le)} (hcμ : IsCritical _ μ μ')
    (hμα : geo _ μ μ' 2 = baseA _) :
    ∃ l : Submodule F (MSP.V4 F), S5.Case56 h (2 ^ k) a (geo _ (baseA (puAmalgam h.le)) α' 2) l ∧
      Qv _ μ ≤ stab _ (baseA (puAmalgam h.le)) ∧
      Module.finrank F ↥(MSP.fixSp (S5.vIm h.le a (Qv _ μ))) ≤ 2 ∧
      MSP.fixSp (S5.vIm h.le a (Qv _ μ)) ⊓ l = ⊥ := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hd2 : (puAmalgam h.le).treeGraph.dist (baseA _) α' = critDist (puAmalgam h.le) := hc.2.1
  obtain ⟨l, y, hl, hy, rfl, hgen⟩ := hgood.exists_conj
  have hβγ : (puAmalgam h.le).treeGraph.Adj (geo _ (baseA (puAmalgam h.le)) α' 2)
      (baseB (puAmalgam h.le)) := by
    have := adj_geo _ (u := baseA (puAmalgam h.le)) (w := α') (i := 1) (by omega)
    rw [hαβ] at this
    exact this.symm
  have hγM : IsMVtx _ (geo _ (baseA (puAmalgam h.le)) α' 2) := isMVtx_geo_two _ hyp hb0 hc
  have hQst := qv_smul_le_stab h hγM hβγ (adj_baseA_baseB _).symm hy
  have hrel := lt_relIndex_centralizer_qv h32 h59 h hmin hb hd hcμ
  rw [hμα] at hrel
  exact ⟨l, hl, hQst, finrank_fixSp_vIm_le_two h hd hQst hrel,
    fixSp_vIm_qv_inf_eq_bot h32 h59 h hmin hb hd hc hαβ hl hy hgen hcμ hμα⟩

theorem isPGroup_of_le_qv (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    (hαβ : geo _ (baseA (puAmalgam h.le)) α' 1 = baseB _) {E : Subgroup (puAmalgam h.le).Universal}
    (hE : E ≤ Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2)) :
    IsPGroup 2 E ∧ E ≤ stab _ (baseA (puAmalgam h.le)) := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hd2 : (puAmalgam h.le).treeGraph.dist (baseA _) α' = critDist (puAmalgam h.le) := hc.2.1
  have hβγ : (puAmalgam h.le).treeGraph.Adj (geo _ (baseA (puAmalgam h.le)) α' 2)
      (baseB (puAmalgam h.le)) := by
    have := adj_geo _ (u := baseA (puAmalgam h.le)) (w := α') (i := 1) (by omega)
    rw [hαβ] at this
    exact this.symm
  have hγM : IsMVtx _ (geo _ (baseA (puAmalgam h.le)) α' 2) := isMVtx_geo_two _ hyp hb0 hc
  have hQβ := qv_le_qv _ hyp hγM hβγ
  exact ⟨(isPGroup_qv _ hyp (not_isMVtx_baseB _)).to_le (hE.trans hQβ),
    (hE.trans hQβ).trans (qv_le_stab_of_adj _ (adj_baseA_baseB _).symm)⟩

omit [Fintype F] in
theorem vIm_le_qLine (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    (hαβ : geo _ (baseA (puAmalgam h.le)) α' 1 = baseB _) {l : Submodule F (MSP.V4 F)}
    (hl : S5.Case56 h (2 ^ k) a (geo _ (baseA (puAmalgam h.le)) α' 2) l)
    {E : Subgroup (puAmalgam h.le).Universal}
    (hE : E ≤ Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2)) :
    S5.vIm h.le a E ≤ MSP.qLine l := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hd2 : (puAmalgam h.le).treeGraph.dist (baseA _) α' = critDist (puAmalgam h.le) := hc.2.1
  have hβγ : (puAmalgam h.le).treeGraph.Adj (geo _ (baseA (puAmalgam h.le)) α' 2)
      (baseB (puAmalgam h.le)) := by
    have := adj_geo _ (u := baseA (puAmalgam h.le)) (w := α') (i := 1) (by omega)
    rw [hαβ] at this
    exact this.symm
  have hγM : IsMVtx _ (geo _ (baseA (puAmalgam h.le)) α' 2) := isMVtx_geo_two _ hyp hb0 hc
  exact S5B.vIm_le_of_le_vPre h.le (hE.trans
    ((S5B.qv_le_jOff h Nat.one_le_two_pow hγM hβγ).trans (hl.1.le.trans hl.2.2.2)))

theorem le_stabCenter_x1 (h32 : S32) (h53 : S53) (h59 : S5B.S59) (h : PUHyp M T L)
    (hmin : PUMin M T L) (hb : 4 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a)
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    (hαβ : geo _ (baseA (puAmalgam h.le)) α' 1 = baseB _) {μ : Vtx (puAmalgam h.le)}
    (hgood : GoodLamF h (2 ^ k) a α' μ) {μ' : Vtx (puAmalgam h.le)} (hcμ : IsCritical _ μ μ')
    (hμα : geo _ μ μ' 2 = baseA _) {E : Subgroup (puAmalgam h.le).Universal}
    (hE : E ≤ Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2))
    (hEq : 2 ^ k < (Qv _ (baseA (puAmalgam h.le))).relIndex E) :
    ZM _ (baseA (puAmalgam h.le)) ⊓ Subgroup.centralizer (Qv _ μ : Set _) ⊓
        Subgroup.centralizer (E : Set _) ≤ stabCenter _ (baseA (puAmalgam h.le)) := by
  obtain ⟨l, hl, hQst, -, hbot⟩ := goodF_fixSp h32 h59 h hmin hb hd hc hαβ hgood hcμ hμα
  obtain ⟨hE2, hEst⟩ := isPGroup_of_le_qv h (by omega) hc hαβ hE
  have hFq : Nat.card F = 2 ^ k := by rw [Nat.card_eq_fintype_card, hd.2.1]
  have hfix : MSP.fixSp (S5.vIm h.le a E) = l := by
    refine fixSp_eq_of_le_qLine hl.2.1 (vIm_le_qLine h (by omega) hc hαβ hl hE) ?_
    rw [S5.card_vIm h hd hEst hE2, hFq]
    exact hEq
  exact le_stabCenter_of_fixSp h32 h53 h hmin (by omega) hd hQst hEst (by rw [hfix]; exact hbot)

theorem relIndex_x1_le (h32 : S32) (h53 : S53) (h59 : S5B.S59) (h : PUHyp M T L)
    (hmin : PUMin M T L) (hb : 4 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a)
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    (hαβ : geo _ (baseA (puAmalgam h.le)) α' 1 = baseB _) {μ : Vtx (puAmalgam h.le)}
    (hgood : GoodLamF h (2 ^ k) a α' μ) {μ' : Vtx (puAmalgam h.le)} (hcμ : IsCritical _ μ μ')
    (hμα : geo _ μ μ' 2 = baseA _) {E : Subgroup (puAmalgam h.le).Universal}
    (hE : E ≤ Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2))
    (hEQ : ¬ E ≤ Qv _ (baseA (puAmalgam h.le))) {H : Subgroup (puAmalgam h.le).Universal}
    (hH : H ≤ ZM _ (baseA (puAmalgam h.le)) ⊓ Subgroup.centralizer (Qv _ μ : Set _) ⊓
      Subgroup.centralizer (E : Set _)) :
    (stabCenter _ (baseA (puAmalgam h.le))).relIndex H ≤ 2 ^ k := by
  obtain ⟨l, hl, hQst, hfin, hbot⟩ := goodF_fixSp h32 h59 h hmin hb hd hc hαβ hgood hcμ hμα
  obtain ⟨hE2, hEst⟩ := isPGroup_of_le_qv h (by omega) hc hαβ hE
  have hFq : Nat.card F = 2 ^ k := by rw [Nat.card_eq_fintype_card, hd.2.1]
  have hne : S5.vIm h.le a E ≠ ⊥ := by
    intro hbot'
    have h1 := S5.card_vIm h hd hEst hE2
    rw [hbot', Subgroup.card_bot] at h1
    exact hEQ (Subgroup.relIndex_eq_one.1 h1.symm)
  have key := relIndex_stabCenter_le_card h32 h53 h hmin (by omega) hd
    (hH.trans (inf_le_left.trans inf_le_left)) hQst hEst
    (le_inf (hH.trans (inf_le_left.trans inf_le_right)) (hH.trans inf_le_right))
  have h1 := finrank_inf_fixSp_le_one hl.2.1 (vIm_le_qLine h (by omega) hc hαβ hl hE) hne hfin hbot
  have h2 := card_le_of_finrank_le_one h1
  rw [hFq] at h2
  exact key.trans h2

theorem le_relIndex_commutator_x1 (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    (hd : S5.IsSp4Data M T L k F a) {α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    (hαβ : geo _ (baseA (puAmalgam h.le)) α' 1 = baseB _) {l : Submodule F (MSP.V4 F)}
    (hl : S5.Case56 h (2 ^ k) a (geo _ (baseA (puAmalgam h.le)) α' 2) l)
    {E : Subgroup (puAmalgam h.le).Universal}
    (hE : E ≤ Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2))
    (hEq : 2 ^ k < (Qv _ (baseA (puAmalgam h.le))).relIndex E) :
    (2 ^ k) ^ 2 ≤ (stabCenter _ (baseA (puAmalgam h.le))).relIndex
      ⁅S5.uSub h.le L (baseA (puAmalgam h.le)), E⁆ := by
  obtain ⟨hE2, hEst⟩ := isPGroup_of_le_qv h hb hc hαβ hE
  have hFq : Nat.card F = 2 ^ k := by rw [Nat.card_eq_fintype_card, hd.2.1]
  have hcomm : MSP.commSp (S5.vIm h.le a E) = l := by
    refine commSp_eq_of_le_qLine hl.2.1 (vIm_le_qLine h hb hc hαβ hl hE) ?_
    rw [S5.card_vIm h hd hEst hE2, hFq]
    exact hEq
  have key := card_commSp_le_relIndex_baseA h hd hEst
  rw [hcomm, Module.natCard_eq_pow_finrank (K := F), hl.2.1.1, hFq] at key
  exact key

end S511S

end CFSG.Quasithin.MS93
