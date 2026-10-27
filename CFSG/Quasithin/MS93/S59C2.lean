module

public import CFSG.Quasithin.MS93.S59Set
public import CFSG.Quasithin.MS93.S59Crit
public import CFSG.Quasithin.MS93.S59L2
public import CFSG.Quasithin.MS93.S5B58

public noncomputable section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Pointwise

namespace S59

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

section Case2

theorem commutator_vSub_eq_bot (h : PUHyp M T L) (hb : 4 < critDist (puAmalgam h.le))
    (hd : S5.IsSp4Data M T L k F a) {γ ξ : Vtx (puAmalgam h.le)}
    (hβγ : (puAmalgam h.le).treeGraph.Adj (baseB _) γ) (hγα : γ ≠ baseA _)
    (hξ : IsCritical _ ξ γ)
    (hξα : (puAmalgam h.le).treeGraph.dist ξ (baseA _) + 2 = critDist (puAmalgam h.le))
    (hP : (S5.bSub h.le L (baseA _)).relIndex (S5.uSub h.le L γ) ≤ 2 ^ k)
    (hZc : hSub h.le L γ ≤ stabCenter _ (baseA (puAmalgam h.le)))
    {Z : Subgroup (puAmalgam h.le).Universal} (hZst : Z ≤ stab _ γ)
    (hZH : ¬ Z ≤ Subgroup.centralizer (hSub h.le L γ : Set (puAmalgam h.le).Universal))
    {N : Subgroup (puAmalgam h.le).Universal} (hNT : N ≤ tZero h.le L γ)
    (hN : ∀ g ∈ stab _ (baseA (puAmalgam h.le)),
      ⁅ZM _ (g • γ), N⁆ ≤ Subgroup.centralizer (Z : Set (puAmalgam h.le).Universal)) :
    ⁅vSub h.le γ, N⁆ = ⊥ := by
  have hb' : 2 < critDist (puAmalgam h.le) := by omega
  obtain ⟨hγ, -, -⟩ := gamma_facts h hβγ hγα
  obtain ⟨hHU, -, -, -, hpt⟩ := hSub_facts h hb' hd hβγ hγα hξ hξα hP
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hαβ := adj_baseA_baseB (puAmalgam h.le)
  have hHZ : ∀ x ∈ hSub h.le L γ, (∀ z ∈ Z, z * x = x * z) → x ∈ stabCenter _ γ := by
    intro x hx hxZ
    by_cases hxL : x ∈ Subgroup.centralizer (puTrans h.le L γ : Set (puAmalgam h.le).Universal)
    · exact uSub_inf_le_stabCenter h hd hγ ⟨hHU hx, hxL⟩
    · exfalso
      apply hZH
      intro z hz
      exact hpt x hx hxL ⟨hZst hz, Subgroup.mem_centralizer_singleton_iff.2 (hxZ z hz)⟩
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  refine (vSub_le_iff h.le γ).2 fun g hg => ?_
  have hgα : g • baseA (puAmalgam h.le) = baseA _ := (mem_stab _).1 hg
  have hνM : IsMVtx _ (g • γ) := (isMVtx_smul _ g γ).2 hγ
  have hgβ : (puAmalgam h.le).treeGraph.Adj (baseA _) (g • baseB (puAmalgam h.le)) := by
    have := (adj_smul _ g _ _).2 hαβ
    rwa [hgα] at this
  have hβν : (puAmalgam h.le).treeGraph.Adj (g • baseB (puAmalgam h.le)) (g • γ) :=
    (adj_smul _ g _ _).2 hβγ
  have hNQ : N ≤ Qv _ (g • baseB (puAmalgam h.le)) :=
    hNT.trans ((tZero_le_qv h.le γ).trans (qv_le_qv _ h.hyp20 hα hgβ))
  have hNst : N ≤ stab _ (g • γ) := hNQ.trans (qv_le_stab_of_adj _ hβν)
  have hHg : (hSub h.le L γ).map (MulAut.conj g).toMonoidHom = hSub h.le L γ := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      have hxc := (S510.mem_stabCenter_iff.1 (hZc hx)).2 g hg
      show g * x * g⁻¹ ∈ _
      rw [hxc, mul_inv_cancel_right]
      exact hx
    · intro x hx
      refine ⟨x, hx, ?_⟩
      have hxc := (S510.mem_stabCenter_iff.1 (hZc hx)).2 g hg
      show g * x * g⁻¹ = x
      rw [hxc, mul_inv_cancel_right]
  have hZN : ⁅ZM _ (g • γ), N⁆ ≤ hSub h.le L γ := by
    rw [← hHg, ← commutator_zm_tZero_smul h hb' hβγ hg]
    exact Subgroup.commutator_mono le_rfl hNT
  have hUN : ⁅S5.uSub h.le L (g • γ), N⁆ ≤
      Subgroup.centralizer (puTrans h.le L (g • γ) : Set (puAmalgam h.le).Universal) := by
    intro x hx
    have hxZ : x ∈ ⁅ZM _ (g • γ), N⁆ :=
      Subgroup.commutator_mono (S5B.uSub_le_zm h.le (g • γ)) le_rfl hx
    have hxH := hZN hxZ
    have hxcen : x ∈ stabCenter _ γ := hHZ x hxH fun z hz =>
      Subgroup.mem_centralizer_iff.1 (hN g hg hxZ) z hz
    have hxν : x ∈ stabCenter _ (g • γ) := by
      rw [S510.stabCenter_smul]
      refine ⟨x, hxcen, ?_⟩
      show g * x * g⁻¹ = x
      rw [(S510.mem_stabCenter_iff.1 (hZc hxH)).2 g hg, mul_inv_cancel_right]
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact (S510.mem_stabCenter_iff.1 hxν).2 l (puTrans_le_stab h.le L _ hl)
  have hUN' := commutator_eq_bot_of_le h hd hνM hNst hUN
  rw [S5B.zm_eq_zh_sup_uSub h hνM hβν.symm]
  refine sup_le ?_ (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hUN')
  rw [Subgroup.le_centralizer_iff]
  exact hNQ.trans (Subgroup.le_centralizer_iff.1 (zh_le_centralizer _ _))

theorem commutator_vSub_zHat_le (h32 : S32) (hX2 : S33.S33X52) (h55 : S55) (h56 : S56)
    (h : PUHyp M T L) (hmin : PUMin M T L) (hb : 4 < critDist (puAmalgam h.le))
    (hd : S5.IsSp4Data M T L k F a) {γ ξ : Vtx (puAmalgam h.le)}
    (hβγ : (puAmalgam h.le).treeGraph.Adj (baseB _) γ) (hγα : γ ≠ baseA _)
    (hξ : IsCritical _ ξ γ)
    (hξα : (puAmalgam h.le).treeGraph.dist ξ (baseA _) + 2 = critDist (puAmalgam h.le))
    (hP : (S5.bSub h.le L (baseA _)).relIndex (S5.uSub h.le L γ) ≤ 2 ^ k)
    (hZc : hSub h.le L γ ≤ stabCenter _ (baseA (puAmalgam h.le)))
    {ρ : Vtx (puAmalgam h.le)} (hc : IsCritical _ γ ρ)
    (hHρ : ¬ S5.zHat _ γ ρ ≤
      Subgroup.centralizer (hSub h.le L γ : Set (puAmalgam h.le).Universal)) :
    ⁅vSub h.le γ, S5.zHat _ γ ρ⁆ ≤ XM _ γ ⊔ ⁅vSub h.le γ, Qv _ γ⁆ := by
  have hb' : 2 < critDist (puAmalgam h.le) := by omega
  have hb0 := h.critDist_pos
  have hyp := h.hyp20
  have hC := h.centHyp
  have h32' := (h32 G M T L h).2.1
  obtain ⟨m₀, hm₀⟩ := ms21_v _ hyp
  obtain ⟨hγ, hd2, hgeoγ⟩ := gamma_facts h hβγ hγα
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hαβ := adj_baseA_baseB (puAmalgam h.le)
  have hρ : IsMVtx _ ρ := hc.isMVtx_right _ hyp
  have hdγρ : (puAmalgam h.le).treeGraph.dist γ ρ = critDist (puAmalgam h.le) := hc.2.1
  obtain ⟨hVZ, hVV, hVQα, hVab, hVQ, -⟩ := vSub_facts h hb hβγ hγα
  have hUγB := uSub_not_le_bSub_of_hyp h hb' hd hβγ hγα hξ hξα hP
  have hZγV : ZM _ γ ≤ vSub h.le γ := by
    have := zm_smul_le_vSub h.le γ (one_mem (stab _ (baseA (puAmalgam h.le))))
    rwa [one_smul] at this
  have hUVV : S5.uSub h.le L γ ≤ vSub h.le γ ⊓ Vv _ (baseA (puAmalgam h.le)) :=
    le_inf ((S5B.uSub_le_zm h.le γ).trans hZγV)
      ((S5B.uSub_le_zm h.le γ).trans (S5B.zm_le_vv_of_dist hγ hd2.le))
  have hZhZ : S5.zHat _ γ ρ ≤ ZM _ ρ := inf_le_left
  have hZρst : ZM _ ρ ≤ stab _ γ := zm_le_stab_of_isCritical _ hyp hb0 hc
  have hZhst : S5.zHat _ γ ρ ≤ stab _ γ := hZhZ.trans hZρst
  have hQρZ : Qv _ ρ ≤ Subgroup.centralizer (S5.zHat _ γ ρ : Set (puAmalgam h.le).Universal) :=
    (Subgroup.le_centralizer_iff.1 (zm_le_centralizer_qv _ hyp hρ)).trans
      (Subgroup.centralizer_le hZhZ)
  have hVst : vSub h.le γ ≤ stab _ (baseA (puAmalgam h.le)) := hVQα.trans (qv_le_stab _ _)
  have hVn : puTrans h.le L (baseA _) ≤
      Subgroup.normalizer (vSub h.le γ : Set (puAmalgam h.le).Universal) :=
    (puTrans_le_stab h.le L _).trans (stab_le_normalizer_vSub h.le γ)
  have hne : geo _ γ ρ 1 ≠ baseB (puAmalgam h.le) := by
    intro he
    apply hHρ
    have hZβ : ZM _ ρ ≤ Qv _ (baseB (puAmalgam h.le)) := by
      rw [← he]
      exact zm_le_qv_geo_one _ hyp hb0 hc
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact ((S510.mem_stabCenter_iff.1 (hZc hx)).2 z
      (qv_le_stab_of_isMVtx _ hyp hα hαβ (hZβ (hZhZ hz)))).symm
  obtain ⟨hdαρ, hgeoαρ⟩ := S510.geo_ext (s' := baseA (puAmalgam h.le)) (s := γ) (t := ρ)
    hd2 (by rw [hdγρ]; exact hb0) (by rw [hgeoγ]; exact Ne.symm hne)
  set σ := geo _ γ ρ (critDist (puAmalgam h.le) - 2) with hσdef
  set σ₂ := geo _ γ ρ (critDist (puAmalgam h.le) - 4) with hσ₂def
  have hσα : geo _ (baseA (puAmalgam h.le)) ρ (critDist (puAmalgam h.le)) = σ := by
    have := hgeoαρ (critDist (puAmalgam h.le) - 2) (by omega)
    rwa [show critDist (puAmalgam h.le) - 2 + 2 = critDist (puAmalgam h.le) by omega] at this
  have hσ₂α : geo _ (baseA (puAmalgam h.le)) ρ (critDist (puAmalgam h.le) - 2) = σ₂ := by
    have := hgeoαρ (critDist (puAmalgam h.le) - 4) (by omega)
    rwa [show critDist (puAmalgam h.le) - 4 + 2 = critDist (puAmalgam h.le) - 2 by omega] at this
  have hdασ : (puAmalgam h.le).treeGraph.dist (baseA _) σ = critDist (puAmalgam h.le) := by
    rw [← hσα]
    exact dist_geo _ (by omega)
  have hdασ₂ : (puAmalgam h.le).treeGraph.dist (baseA _) σ₂ = critDist (puAmalgam h.le) - 2 := by
    rw [← hσ₂α]
    exact dist_geo _ (by omega)
  have hdγσ : (puAmalgam h.le).treeGraph.dist γ σ = critDist (puAmalgam h.le) - 2 :=
    dist_geo _ (by omega)
  have hdσ₂ρ : (puAmalgam h.le).treeGraph.dist σ₂ ρ = 4 := by
    rw [dist_geo_right _ (by omega), hdγρ]
    omega
  have hdσρ : (puAmalgam h.le).treeGraph.dist σ ρ = 2 := by
    rw [dist_geo_right _ (by omega), hdγρ]
    omega
  have hdσ₂σ : (puAmalgam h.le).treeGraph.dist σ₂ σ = 2 := by
    rw [dist_geo_geo _ (by omega) (by omega)]
    omega
  have hσM : IsMVtx _ σ :=
    (isMVtx_geo _ (by omega)).2 (iff_of_true hγ ⟨m₀ - 1, by omega⟩)
  have hσ₂M : IsMVtx _ σ₂ :=
    (isMVtx_geo _ (by omega)).2 (iff_of_true hγ ⟨m₀ - 2, by omega⟩)
  have hZσ₂T : ZM _ σ₂ ≤ tZero h.le L γ :=
    zm_le_tZero h hb' hαβ hβγ hσ₂M (by omega) (by omega)
  have hXσT : XM _ σ ⊓ Qv _ (baseA (puAmalgam h.le)) ≤ tZero h.le L γ :=
    xm_inf_le_tZero h hγ (by omega)
  have hB1 : ⁅vSub h.le γ, ZM _ σ₂⁆ = ⊥ := by
    refine commutator_vSub_eq_bot h hb hd hβγ hγα hξ hξα hP hZc hZhst hHρ hZσ₂T fun g hg => ?_
    have hgν : (puAmalgam h.le).treeGraph.dist (g • γ) σ₂ ≤ critDist (puAmalgam h.le) := by
      have t := dist_triangle _ (g • γ) (baseA (puAmalgam h.le)) σ₂
      have h2 : (puAmalgam h.le).treeGraph.dist (g • γ) (baseA _) = 2 := by
        rw [SimpleGraph.dist_comm, ← (mem_stab _).1 hg, dist_smul, hd2]
      omega
    have hst := zm_le_stab_of_dist_le h ((isMVtx_smul _ g γ).2 hγ) hgν
    rw [Subgroup.commutator_comm]
    exact (commutator_le_left_of_le_normalizer (hst.trans (stab_le_normalizer_zm _ _))).trans
      ((zm_le_qv_of_dist_lt _ hσ₂M (by omega)).trans hQρZ)
  have hε₂ : (puAmalgam h.le).treeGraph.Adj σ₂ (geo _ σ₂ (baseA (puAmalgam h.le)) 1) :=
    adj_geo_one _ (by rw [SimpleGraph.dist_comm, hdασ₂]; omega)
  have hdαε₂ : (puAmalgam h.le).treeGraph.dist (baseA _) (geo _ σ₂ (baseA (puAmalgam h.le)) 1) =
      critDist (puAmalgam h.le) - 3 := by
    rw [SimpleGraph.dist_comm, dist_geo_right _ (by rw [SimpleGraph.dist_comm, hdασ₂]; omega),
      SimpleGraph.dist_comm, hdασ₂]
    omega
  have hVσ₂ : vSub h.le γ ≤ Qv _ σ₂ :=
    le_qv_of_le_centralizer _ hC hσ₂M hε₂ (hVQ _ (by omega))
      (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hB1)
  have hε₁ : (puAmalgam h.le).treeGraph.Adj σ₂ (geo _ σ₂ σ 1) :=
    adj_geo_one _ (by rw [hdσ₂σ]; norm_num)
  have hε₁σ : (puAmalgam h.le).treeGraph.Adj (geo _ σ₂ σ 1) σ := by
    have := adj_geo _ (u := σ₂) (w := σ) (i := 1) (by rw [hdσ₂σ]; norm_num)
    rwa [show (1 + 1 : ℕ) = 2 from rfl, ← hdσ₂σ, geo_dist] at this
  have hVσst : vSub h.le γ ≤ stab _ σ :=
    hVσ₂.trans ((qv_le_qv _ hyp hσ₂M hε₁).trans (qv_le_stab_of_adj _ hε₁σ))
  have hXσρ : XM _ σ ≤ Subgroup.centralizer (S5.zHat _ γ ρ : Set (puAmalgam h.le).Universal) :=
    (ms22_i _ hyp hC hσM hρ (by omega)).trans hQρZ
  have hB2 : ⁅vSub h.le γ, XM _ σ ⊓ Qv _ (baseA (puAmalgam h.le))⁆ = ⊥ := by
    refine commutator_vSub_eq_bot h hb hd hβγ hγα hξ hξα hP hZc hZhst hHρ hXσT fun g hg => ?_
    have hst : ZM _ (g • γ) ≤ stab _ σ := (zm_smul_le_vSub h.le γ hg).trans hVσst
    rw [Subgroup.commutator_comm]
    exact ((Subgroup.commutator_mono inf_le_left le_rfl).trans
      (commutator_le_left_of_le_normalizer (hst.trans (stab_le_normalizer_xm _ _)))).trans hXσρ
  have hVσ : vSub h.le γ ≤ Qv _ σ := by
    by_cases hZσ : ZM _ σ ≤ Qv _ (baseA (puAmalgam h.le))
    · have hVc : vSub h.le γ ≤ Subgroup.centralizer (ZM _ σ : Set (puAmalgam h.le).Universal) := by
        rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
        refine le_bot_iff.1 ?_
        rw [← hB2]
        exact Subgroup.commutator_mono le_rfl (le_inf (zm_le_xm _ hyp hb0 hσM) hZσ)
      exact le_qv_of_le_centralizer _ hC hσM hε₁σ.symm (hVσ₂.trans (qv_le_qv _ hyp hσ₂M hε₁))
        hVc
    · exfalso
      have hcσα : IsCritical _ σ (baseA (puAmalgam h.le)) :=
        ⟨hσM, by rw [SimpleGraph.dist_comm]; exact hdασ, hZσ⟩
      have hcασ := ms22_iii _ hyp hb0 hC hcσα
      have hσ₂eq : σ₂ = geo _ σ (baseA (puAmalgam h.le)) 2 := by
        apply eq_geo_of_dist _ (by rw [SimpleGraph.dist_comm]; exact hdσ₂σ)
        rw [SimpleGraph.dist_comm (u := σ) (v := σ₂), hdσ₂σ,
          SimpleGraph.dist_comm (u := σ₂) (v := baseA _), hdασ₂,
          SimpleGraph.dist_comm (u := σ) (v := baseA _), hdασ]
        omega
      have hadj1 : (puAmalgam h.le).treeGraph.Adj (geo _ σ (baseA (puAmalgam h.le)) 1) σ₂ := by
        have := adj_geo _ (u := σ) (w := baseA (puAmalgam h.le)) (i := 1)
          (by rw [SimpleGraph.dist_comm, hdασ]; omega)
        rwa [show (1 + 1 : ℕ) = 2 from rfl, ← hσ₂eq] at this
      have hYT : vSub h.le γ ≤ Qv _ (geo _ σ (baseA (puAmalgam h.le)) 1) :=
        hVσ₂.trans (qv_le_qv _ hyp hσ₂M hadj1.symm)
      obtain ⟨-, -, -, hRX, hXX, -⟩ := S5B.crit_facts h hcασ
      have hYR : vSub h.le γ ≤
          Subgroup.centralizer (critR _ (baseA (puAmalgam h.le)) σ : Set _) :=
        hVQα.trans ((qv_le_centralizer_xm _ _).trans (Subgroup.centralizer_le hRX))
      have hAασ : ⁅critA _ (baseA (puAmalgam h.le)) σ, vSub h.le γ⁆ = ⊥ := by
        rw [critA, Subgroup.commutator_comm]
        exact hB2
      have hcomm := S5B.commutator_zHat_le' h hd hcασ hYT hYR hAασ
      obtain ⟨y, hyZ, hyst, hy2, hyQ⟩ := exists_zHat_not_mem h55 h56 h hmin hb' hd hcασ
      have hVB := inf_le_bSub_of_elt h h32' hα hVst hVn hyst hy2 hyQ fun w hw => by
        have h1 : ⁅w, y⁆ ∈ ⁅vSub h.le γ, S5.zHat _ (baseA (puAmalgam h.le)) σ⁆ :=
          Subgroup.commutator_mem_commutator hw hyZ
        have hX := (hcomm.trans (sup_le hXX hRX)) h1
        have e : y * w * y⁻¹ * w⁻¹ = ⁅w, y⁆⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact inv_mem hX
      exact hUγB (hUVV.trans hVB)
  have hσρ : σ = geo _ ρ γ 2 := by
    have := geo_symm _ (u := γ) (w := ρ) (i := critDist (puAmalgam h.le) - 2) (by omega)
    rw [hdγρ, show critDist (puAmalgam h.le) - (critDist (puAmalgam h.le) - 2) = 2 by omega]
      at this
    exact this.symm
  have hρ1σ : (puAmalgam h.le).treeGraph.Adj (geo _ ρ γ 1) σ := by
    have := adj_geo _ (u := ρ) (w := γ) (i := 1) (by rw [SimpleGraph.dist_comm, hdγρ]; omega)
    rwa [show (1 + 1 : ℕ) = 2 from rfl, ← hσρ] at this
  have hVT : vSub h.le γ ≤ Qv _ (geo _ ρ γ 1) := hVσ.trans (qv_le_qv _ hyp hσM hρ1σ.symm)
  have hcργ := ms22_iii _ hyp hb0 hC hc
  have hRγX : critR _ γ ρ ≤ XM _ γ :=
    (commutator_le_left_of_le_normalizer (hZρst.trans (stab_le_normalizer_zm _ _))).trans
      (zm_le_xm _ hyp hb0 hγ)
  have hYR : vSub h.le γ ≤ Subgroup.centralizer (critR _ γ ρ : Set (puAmalgam h.le).Universal) :=
    (hVQ γ (by omega)).trans ((qv_le_centralizer_xm _ γ).trans (Subgroup.centralizer_le hRγX))
  have hAst : critA _ γ ρ ≤ stab _ (baseA (puAmalgam h.le)) :=
    inf_le_right.trans ((qv_le_qv _ hyp hγ hβγ.symm).trans (qv_le_stab_of_isMVtx _ hyp hα hαβ))
  have hA₀V : ⁅critA _ γ ρ, vSub h.le γ⁆ ≤ vSub h.le γ := by
    rw [Subgroup.commutator_comm]
    exact commutator_le_left_of_le_normalizer (hAst.trans (stab_le_normalizer_vSub h.le γ))
  have hAYY : ⁅⁅critA _ γ ρ, vSub h.le γ⁆, vSub h.le γ⁆ = ⊥ := by
    refine le_bot_iff.1 ((Subgroup.commutator_mono hA₀V le_rfl).trans ?_)
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer.2 hVab]
  have hYX : vSub h.le γ ≤ Subgroup.centralizer (XM _ γ : Set (puAmalgam h.le).Universal) :=
    (hVQ γ (by omega)).trans (qv_le_centralizer_xm _ γ)
  rcases s33_dich hX2 h32 h hd hc hVT hYR hYX hAYY with hl | ⟨hcard, hle⟩
  · refine hl.trans (sup_le (sup_le ?_ (hRγX.trans le_sup_left)) ?_)
    · rw [Subgroup.commutator_comm]
      exact (commutator_xm_le_right _ hyp hb0 hC hcργ).trans le_sup_left
    · rw [Subgroup.commutator_comm]
      exact (Subgroup.commutator_mono le_rfl inf_le_right).trans le_sup_right
  · exfalso
    have hRZ : critR _ γ ρ ⊔ stabCenter _ ρ ≤
        Subgroup.centralizer (S5.zHat _ γ ρ : Set (puAmalgam h.le).Universal) := by
      refine sup_le ?_ ?_
      · have hRρ : critR _ γ ρ ≤ ZM _ ρ := by
          rw [critR, Subgroup.commutator_comm]
          exact commutator_le_left_of_le_normalizer
            ((zm_le_stab_of_isCritical _ hyp hb0 hcργ).trans (stab_le_normalizer_zm _ _))
        exact hRρ.trans ((zm_le_qv_self _ hρ hb0).trans hQρZ)
      · intro z hz
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact (S510.mem_stabCenter_iff.1 hz).2 y
          (((zm_le_qv_self _ hρ hb0).trans (qv_le_stab _ _)) (hZhZ hy))
    by_cases hA : critA _ γ ρ ≤ Qv _ (baseA (puAmalgam h.le))
    · have hAT : critA _ γ ρ ≤ tZero h.le L γ := by
        refine le_inf hA ?_
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro v hv
        exact (Subgroup.mem_centralizer_iff.1
          (zm_le_centralizer_qv _ hyp hγ (S5B.uSub_le_zm h.le γ hv.1)) x hx.2).symm
      have hbot := commutator_vSub_eq_bot h hb hd hβγ hγα hξ hξα hP hZc hZhst hHρ hAT
        fun g hg => ((Subgroup.commutator_mono (zm_smul_le_vSub h.le γ hg) le_rfl).trans
          hle).trans hRZ
      rw [hbot, Subgroup.card_bot] at hcard
      have := Nat.one_lt_two_pow (show k ≠ 0 by have := hd.1; omega)
      omega
    · have hA2 : IsPGroup 2 (critA _ γ ρ) :=
        (isPGroup_qv _ hyp (not_isMVtx_baseB _)).to_le
          (inf_le_right.trans (qv_le_qv _ hyp hγ hβγ.symm))
      have hUle : ⁅S5.uSub h.le L (baseA _), critA _ γ ρ⁆ ≤ ⁅vSub h.le γ, critA _ γ ρ⁆ :=
        Subgroup.commutator_mono ((S5B.uSub_le_zm h.le _).trans hVZ) le_rfl
      have hfin : Finite ↥⁅vSub h.le γ, critA _ γ ρ⁆ :=
        S5B.finite_of_le_qv h hα ((commutator_le_left_of_le_normalizer
          (hAst.trans (stab_le_normalizer_vSub h.le γ))).trans hVQα)
      have hcU : Nat.card ↥⁅S5.uSub h.le L (baseA _), critA _ γ ρ⁆ ≤ 2 ^ k :=
        (Subgroup.card_le_of_le hUle).trans hcard.le
      have htv := (S5B.tv_card h hd hα hAst hA2 hA hcU).1
      have heq : ⁅S5.uSub h.le L (baseA _), critA _ γ ρ⁆ = ⁅vSub h.le γ, critA _ γ ρ⁆ :=
        Subgroup.eq_of_le_of_card_ge hUle (by rw [hcard]; exact htv)
      obtain ⟨y, hyA, hyQ⟩ := Set.not_subset.1 hA
      obtain ⟨e, he⟩ := hA2 ⟨y, hyA⟩
      have hy2 : ∃ e : ℕ, y ^ 2 ^ e = 1 := ⟨e, by simpa using congrArg Subtype.val he⟩
      have hUU : ⁅S5.uSub h.le L (baseA _), critA _ γ ρ⁆ ≤ S5.uSub h.le L (baseA _) :=
        commutator_le_left_of_le_normalizer (hAst.trans (stab_le_normalizer_uSub h _))
      have hVB := inf_le_bSub_of_elt h h32' hα hVst hVn (hAst hyA) hy2 hyQ fun w hw => by
        have h1 : ⁅y, w⁆ ∈ ⁅critA _ γ ρ, vSub h.le γ⁆ := Subgroup.commutator_mem_commutator hyA hw
        rw [Subgroup.commutator_comm, ← heq] at h1
        exact zm_le_xm _ hyp hb0 hα (S5B.uSub_le_zm h.le _ (hUU h1))
      exact hUγB (hUVV.trans hVB)

theorem case2_false (h32 : S32) (hX2 : S33.S33X52) (h55 : S55) (h56 : S56) (h58 : S5B.S58)
    (h : PUHyp M T L) (hmin : PUMin M T L) (hb : 4 < critDist (puAmalgam h.le))
    (hd : S5.IsSp4Data M T L k F a) {α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    (hαβ' : geo _ (baseA (puAmalgam h.le)) α' 1 = baseB _) {ξ : Vtx (puAmalgam h.le)}
    (hξ : IsCritical _ ξ (geo _ (baseA (puAmalgam h.le)) α' 2))
    (hξα : (puAmalgam h.le).treeGraph.dist ξ (baseA _) + 2 = critDist (puAmalgam h.le))
    (hP : (S5.bSub h.le L (baseA _)).relIndex
      (S5.uSub h.le L (geo _ (baseA (puAmalgam h.le)) α' 2)) ≤ 2 ^ k)
    (hZc : hSub h.le L (geo _ (baseA (puAmalgam h.le)) α' 2) ≤
      stabCenter _ (baseA (puAmalgam h.le))) : False := by
  have hb' : 2 < critDist (puAmalgam h.le) := by omega
  have hb0 := h.critDist_pos
  have hyp := h.hyp20
  have hC := h.centHyp
  have h32' := (h32 G M T L h).2.1
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hαβ := adj_baseA_baseB (puAmalgam h.le)
  have hdd : (puAmalgam h.le).treeGraph.dist (baseA _) α' = critDist (puAmalgam h.le) := hc.2.1
  set γ := geo _ (baseA (puAmalgam h.le)) α' 2 with hγdef
  have hβγ : (puAmalgam h.le).treeGraph.Adj (baseB _) γ := by
    have := adj_geo _ (u := baseA (puAmalgam h.le)) (w := α') (i := 1) (by omega)
    rwa [hαβ'] at this
  have hd2 : (puAmalgam h.le).treeGraph.dist (baseA _) γ = 2 := dist_geo _ (by omega)
  have hγα : γ ≠ baseA _ := by
    intro he
    rw [he, SimpleGraph.dist_self] at hd2
    exact absurd hd2 (by norm_num)
  obtain ⟨hγ, -, hgeoγ⟩ := gamma_facts h hβγ hγα
  obtain ⟨-, hTst, hT2, hTQ, -⟩ := tZero_facts h hb' hd hβγ hγα hξ hξα hP
  obtain ⟨hHU, -, hHL, hHX, hpt⟩ := hSub_facts h hb' hd hβγ hγα hξ hξα hP
  obtain ⟨hVZ, hVV, hVQα, hVab, hVQ, -⟩ := vSub_facts h hb hβγ hγα
  have hVQγ : vSub h.le γ ≤ Qv _ γ := hVQ γ (by omega)
  have hQγst : Qv _ γ ≤ stab _ γ := qv_le_stab _ _
  have hQγα : Qv _ γ ≤ stab _ (baseA (puAmalgam h.le)) :=
    (qv_le_qv _ hyp hγ hβγ.symm).trans (qv_le_stab_of_isMVtx _ hyp hα hαβ)
  have hcα'α := ms22_iii _ hyp hb0 hC hc
  obtain ⟨ρ₀, -, hρ₀c⟩ := S5B.exists_isCritical_step h hcα'α (vv_not_le_gp h58 h hmin hb' hd hcα'α)
  have hcγρ₀ := ms22_iii _ hyp hb0 hC hρ₀c
  obtain ⟨h₀, hh₀, hh₀L⟩ := Set.not_subset.1 hHL
  have hZ₀st : S5.zHat _ γ ρ₀ ≤ stab _ γ :=
    inf_le_left.trans (zm_le_stab_of_isCritical _ hyp hb0 hcγρ₀)
  have hZ₀2 : IsPGroup 2 (S5.zHat _ γ ρ₀) :=
    (isPGroup_qv _ hyp ((isMVtx_iff_of_adj _ (adj_geo_one_of_isCritical _ hb0 hcγρ₀)).1 hγ)).to_le
      (inf_le_left.trans (zm_le_qv_geo_one _ hyp hb0 hcγρ₀))
  obtain ⟨y, hy, e, he, hne⟩ := exists_conj_not_comm h hd hγ (hHU hh₀) hh₀L hZ₀st hZ₀2
    (zHat_not_le_qv h55 h56 h hmin hb' hd hcγρ₀)
  have hyγ : y⁻¹ • γ = γ := (mem_stab _).1 (inv_mem hy)
  set ρ := y⁻¹ • ρ₀ with hρdef
  have hcγρ : IsCritical _ γ ρ := by
    have := (isCritical_smul _ y⁻¹ _ _).2 hcγρ₀
    rwa [hyγ] at this
  have hZρ : S5.zHat _ γ ρ = (S5.zHat _ γ ρ₀).map (MulAut.conj y⁻¹).toMonoidHom := by
    have := S5B.zHat_smul _ y⁻¹ γ ρ₀
    rwa [hyγ] at this
  have he' : y⁻¹ * e * y ∈ S5.zHat _ γ ρ := by
    rw [hZρ]
    exact ⟨e, he, by simp [mul_assoc]⟩
  have hne' : y⁻¹ * e * y * h₀ ≠ h₀ * (y⁻¹ * e * y) := by
    intro hc'
    apply hne
    calc e * (y * h₀ * y⁻¹) = y * (y⁻¹ * e * y * h₀) * y⁻¹ := by group
      _ = y * (h₀ * (y⁻¹ * e * y)) * y⁻¹ := by rw [hc']
      _ = y * h₀ * y⁻¹ * e := by group
  have hHρ : ¬ S5.zHat _ γ ρ ≤
      Subgroup.centralizer (hSub h.le L γ : Set (puAmalgam h.le).Universal) := by
    intro hle
    exact hne' (Subgroup.mem_centralizer_iff.1 (hle he') h₀ hh₀).symm
  have hZρst : S5.zHat _ γ ρ ≤ stab _ γ :=
    inf_le_left.trans (zm_le_stab_of_isCritical _ hyp hb0 hcγρ)
  have hZρ2 : IsPGroup 2 (S5.zHat _ γ ρ) :=
    (isPGroup_qv _ hyp ((isMVtx_iff_of_adj _ (adj_geo_one_of_isCritical _ hb0 hcγρ)).1 hγ)).to_le
      (inf_le_left.trans (zm_le_qv_geo_one _ hyp hb0 hcγρ))
  set K := stab _ γ ⊓ Subgroup.centralizer (hSub h.le L γ : Set (puAmalgam h.le).Universal)
    with hKdef
  have hgen : K ⊔ S5.zHat _ γ ρ = stab _ γ := by
    refine le_antisymm (sup_le inf_le_left hZρst) ?_
    rw [← centralizer_sup_eq h hd hγ (hHU hh₀) hh₀L hZρst hZρ2 he' hne']
    exact sup_le_sup_right (fun m hm => ⟨hm.1, hpt h₀ hh₀ hh₀L hm⟩) _
  have hQγK : Qv _ γ ≤ K := by
    refine le_inf hQγst ?_
    rw [← Subgroup.le_centralizer_iff]
    exact hHU.trans ((S5B.uSub_le_zm h.le γ).trans (zm_le_centralizer_qv _ hyp hγ))
  have hstep : ∀ x ∈ K, ⁅(vSub h.le γ).map (MulAut.conj x).toMonoidHom, S5.zHat _ γ ρ⁆ ≤
      XM _ γ ⊔ ⁅(vSub h.le γ).map (MulAut.conj x).toMonoidHom, Qv _ γ⁆ := by
    intro x hx
    have hxγ : x⁻¹ • γ = γ := (mem_stab _).1 (inv_mem hx.1)
    have hcx : IsCritical _ γ (x⁻¹ • ρ) := by
      have := (isCritical_smul _ x⁻¹ _ _).2 hcγρ
      rwa [hxγ] at this
    have hZx : S5.zHat _ γ (x⁻¹ • ρ) = (S5.zHat _ γ ρ).map (MulAut.conj x⁻¹).toMonoidHom := by
      have := S5B.zHat_smul _ x⁻¹ γ ρ
      rwa [hxγ] at this
    have hHx : (hSub h.le L γ).map (MulAut.conj x).toMonoidHom = hSub h.le L γ := by
      apply le_antisymm
      · rintro _ ⟨z, hz, rfl⟩
        have hcz := Subgroup.mem_centralizer_iff.1 hx.2 z hz
        show x * z * x⁻¹ ∈ _
        rw [← hcz, mul_inv_cancel_right]
        exact hz
      · intro z hz
        refine ⟨z, hz, ?_⟩
        have hcz := Subgroup.mem_centralizer_iff.1 hx.2 z hz
        show x * z * x⁻¹ = z
        rw [← hcz, mul_inv_cancel_right]
    have hHρx : ¬ S5.zHat _ γ (x⁻¹ • ρ) ≤
        Subgroup.centralizer (hSub h.le L γ : Set (puAmalgam h.le).Universal) := by
      intro hle
      apply hHρ
      rw [hZx, map_conj_le_iff, inv_inv, ← PU.centralizer_map_mulEquiv, hHx] at hle
      exact hle
    have key := commutator_vSub_zHat_le h32 hX2 h55 h56 h hmin hb hd hβγ hγα hξ hξα hP hZc hcx
      hHρx
    rw [hZx] at key
    have hXx : (XM _ γ).map (MulAut.conj x).toMonoidHom = XM _ γ := by
      rw [← xm_smul, (mem_stab _).1 hx.1]
    have hQx : (Qv _ γ).map (MulAut.conj x).toMonoidHom = Qv _ γ := by
      rw [← qv_smul, (mem_stab _).1 hx.1]
    have := Subgroup.map_mono (f := (MulAut.conj x).toMonoidHom) key
    rwa [Subgroup.map_commutator, Subgroup.map_sup, Subgroup.map_commutator, hXx, hQx,
      map_conj_map_conj_inv] at this
  obtain ⟨W, hWdef⟩ : ∃ W : Subgroup (puAmalgam h.le).Universal,
      W = ⨆ x : ↥K, (vSub h.le γ).map (MulAut.conj (x : (puAmalgam h.le).Universal)).toMonoidHom :=
    ⟨_, rfl⟩
  have hgenW : ∀ x : ↥K,
      (vSub h.le γ).map (MulAut.conj (x : (puAmalgam h.le).Universal)).toMonoidHom ≤ W :=
    fun x => hWdef ▸ le_iSup_of_le x le_rfl
  have hVW : vSub h.le γ ≤ W := by
    refine le_trans ?_ (hgenW 1)
    intro v hv
    exact ⟨v, hv, by simp⟩
  have hWQ : W ≤ Qv _ γ := by
    rw [hWdef]
    refine iSup_le fun x => ?_
    have hQx :
        (Qv _ γ).map (MulAut.conj (x : (puAmalgam h.le).Universal)).toMonoidHom = Qv _ γ := by
      rw [← qv_smul, (mem_stab _).1 x.2.1]
    rw [← hQx]
    exact Subgroup.map_mono hVQγ
  have hKW : K ≤ Subgroup.normalizer (W : Set (puAmalgam h.le).Universal) := by
    refine le_normalizer_of_map_conj_le fun k hk => ?_
    conv_lhs => rw [hWdef]
    rw [Subgroup.map_iSup]
    refine iSup_le fun x => ?_
    rw [map_conj_map_conj]
    exact hgenW ⟨k * x, mul_mem hk x.2⟩
  have hWst : W ≤ stab _ γ := hWQ.trans hQγst
  have hWn : W ≤ Subgroup.normalizer (W : Set (puAmalgam h.le).Universal) :=
    Subgroup.le_normalizer
  have hWQn : W ≤ Subgroup.normalizer (Qv _ γ : Set (puAmalgam h.le).Universal) :=
    hWst.trans (stab_le_normalizer_qv _ _)
  have hWZ : ⁅W, S5.zHat _ γ ρ⁆ ≤ XM _ γ ⊔ ⁅W, Qv _ γ⁆ := by
    conv_lhs => rw [hWdef]
    refine commutator_iSup_le (fun x => ?_) fun x => ?_
    · exact (hgenW x).trans (le_normalizer_sup
        (hWst.trans (stab_le_normalizer_xm _ _)) (le_normalizer_commutator hWn hWQn))
    · exact (hstep x x.2).trans (sup_le_sup_left
        (Subgroup.commutator_mono (hgenW x) le_rfl) _)
  have hWQW : ⁅W, Qv _ γ⁆ ≤ W := commutator_le_left_of_le_normalizer (hQγK.trans hKW)
  set P := W ⊔ XM _ γ with hPdef
  have hPst : P ≤ stab _ γ := sup_le hWst ((xm_le_qv _ _).trans hQγst)
  have hZρP : S5.zHat _ γ ρ ≤ Subgroup.normalizer (P : Set (puAmalgam h.le).Universal) :=
    le_normalizer_sup_of_commutator_le (hZρst.trans (stab_le_normalizer_xm _ _))
      (hWZ.trans (sup_le le_sup_right (hWQW.trans le_sup_left)))
  have hKP : K ≤ Subgroup.normalizer (P : Set (puAmalgam h.le).Universal) :=
    le_normalizer_sup hKW (inf_le_left.trans (stab_le_normalizer_xm _ _))
  have hstP : stab _ γ ≤ Subgroup.normalizer (P : Set (puAmalgam h.le).Universal) := by
    rw [← hgen]
    exact sup_le hKP hZρP
  set N := XM _ γ ⊔ ⁅P, Qv _ γ⁆ with hNdef
  have hstN : stab _ γ ≤ Subgroup.normalizer (N : Set (puAmalgam h.le).Universal) :=
    le_normalizer_sup (stab_le_normalizer_xm _ _)
      (le_normalizer_commutator hstP (stab_le_normalizer_qv _ _))
  have hNst : N ≤ stab _ γ := sup_le ((xm_le_qv _ _).trans hQγst)
    ((commutator_le_left_of_le_normalizer (hQγst.trans hstP)).trans hPst)
  obtain ⟨y₀, hy₀Z, hy₀st, hy₀2, hy₀Q⟩ := exists_zHat_not_mem h55 h56 h hmin hb' hd hcγρ
  have hPy : ∀ w ∈ P, y₀ * w * y₀⁻¹ * w⁻¹ ∈ N := by
    have hz : ⁅P, Subgroup.zpowers y₀⁆ ≤ N := by
      refine S5B.commutator_sup_le_of_le (hWst.trans hstN)
        (((xm_le_qv _ _).trans hQγst).trans hstN) ?_ ?_
      · refine ((Subgroup.commutator_mono le_rfl ((Subgroup.zpowers_le).2 hy₀Z)).trans hWZ).trans
          (sup_le_sup_left (Subgroup.commutator_mono le_sup_left le_rfl) _)
      · exact (commutator_le_left_of_le_normalizer
          ((Subgroup.zpowers_le).2 (stab_le_normalizer_xm _ _ hy₀st))).trans le_sup_left
    intro w hw
    have h1 := hz (Subgroup.commutator_mem_commutator hw (Subgroup.mem_zpowers y₀))
    have e : y₀ * w * y₀⁻¹ * w⁻¹ = ⁅w, y₀⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact inv_mem h1
  have hPL : ⁅P, puTrans h.le L γ⁆ ≤ N :=
    commutator_le_of_elt h hγ hPst hNst ((puTrans_le_stab h.le L γ).trans hstP)
      ((puTrans_le_stab h.le L γ).trans hstN) hy₀st hy₀2 hy₀Q (hstN hy₀st) hPy
  have hVX : vSub h.le γ ⊔ XM _ γ ≤ P := sup_le_sup_right hVW _
  have hNR : N ≤ (vSub h.le γ ⊔ XM _ γ) ⊔ ⁅P, Qv _ γ⁆ :=
    sup_le (le_sup_right.trans le_sup_left) le_sup_right
  have hVR : vSub h.le γ ≤ (vSub h.le γ ⊔ XM _ γ) ⊔ ⁅P, Qv _ γ⁆ := le_sup_left.trans le_sup_left
  have hPle : P ≤ (vSub h.le γ ⊔ XM _ γ) ⊔ ⁅P, Qv _ γ⁆ := by
    refine sup_le ?_ (le_sup_right.trans le_sup_left)
    rw [hWdef]
    refine iSup_le fun x => ?_
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨l, hl, t, ht, hxlt⟩ := exists_puTrans_mul_vtx h hγ hβγ.symm x.2.1
    have htv : t * v * t⁻¹ ∈ vSub h.le γ :=
      (Subgroup.mem_normalizer_iff.1 (stab_le_normalizer_vSub h.le γ
        (qv_le_stab_of_isMVtx _ hyp hα hαβ ht)) v).1 hv
    have hc1 : ⁅l, t * v * t⁻¹⁆ ∈ N := by
      rw [← commutatorElement_inv]
      exact inv_mem (hPL (Subgroup.commutator_mem_commutator (hVX (Subgroup.mem_sup_left htv)) hl))
    have e : (MulAut.conj (x : (puAmalgam h.le).Universal)).toMonoidHom v =
        ⁅l, t * v * t⁻¹⁆ * (t * v * t⁻¹) := by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hxlt]
      simp only [commutatorElement_def]
      group
    rw [e]
    exact mul_mem (hNR hc1) (hVR htv)
  have hQnil : Group.IsNilpotent ↥(Qv _ γ) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Finite ↥(Qv _ γ) := S5B.finite_of_le_qv h hγ le_rfl
    exact ((isPGroup_qv _ hyp (not_isMVtx_baseB (puAmalgam h.le))).to_le
      (qv_le_qv _ hyp hγ hβγ.symm)).isNilpotent
  have hPVX : P ≤ vSub h.le γ ⊔ XM _ γ :=
    le_of_le_sup_commutator hQnil (sup_le hWQ (xm_le_qv _ _)) (hQγst.trans hstP) hVX
      (le_normalizer_sup (hQγα.trans (stab_le_normalizer_vSub h.le γ))
        (hQγst.trans (stab_le_normalizer_xm _ _))) hPle
  have hQγC : Qv _ γ ≤ Subgroup.normalizer (hSub h.le L γ : Set (puAmalgam h.le).Universal) :=
    (hQγK.trans inf_le_right).trans (Subgroup.centralizer_le_normalizer _)
  have hVT : ⁅vSub h.le γ, tZero h.le L γ⁆ ≤ hSub h.le L γ := by
    rw [vSub, S5.nclStab]
    refine commutator_iSup_le (fun g => ?_) fun g => ?_
    · rw [← zm_smul]
      exact ((zm_smul_le_vSub h.le γ g.2).trans hVQγ).trans hQγC
    · rw [← zm_smul, commutator_zm_tZero_smul h hb' hβγ g.2]
      rintro _ ⟨x, hx, rfl⟩
      have hxc := (S510.mem_stabCenter_iff.1 (hZc hx)).2 g g.2
      show (g : (puAmalgam h.le).Universal) * x * (g : (puAmalgam h.le).Universal)⁻¹ ∈ _
      rw [hxc, mul_inv_cancel_right]
      exact hx
  obtain ⟨t₀, ht₀T, ht₀Q⟩ := Set.not_subset.1 hTQ
  obtain ⟨n₀, hn₀⟩ := hT2 ⟨t₀, ht₀T⟩
  have ht₀2 : ∃ e : ℕ, t₀ ^ 2 ^ e = 1 := ⟨n₀, by simpa using congrArg Subtype.val hn₀⟩
  have hPt₀ : ∀ w ∈ vSub h.le γ ⊔ XM _ γ, t₀ * w * t₀⁻¹ * w⁻¹ ∈ XM _ γ := by
    have hz : ⁅vSub h.le γ ⊔ XM _ γ, Subgroup.zpowers t₀⁆ ≤ XM _ γ := by
      refine S5B.commutator_sup_le_of_le (hVQγ.trans (hQγst.trans (stab_le_normalizer_xm _ _)))
        ((xm_le_qv _ _).trans (hQγst.trans (stab_le_normalizer_xm _ _))) ?_ ?_
      · exact ((Subgroup.commutator_mono le_rfl ((Subgroup.zpowers_le).2 ht₀T)).trans hVT).trans
          (hHU.trans ((S5B.uSub_le_zm h.le γ).trans (zm_le_xm _ hyp hb0 hγ)))
      · exact commutator_le_left_of_le_normalizer
          ((Subgroup.zpowers_le).2 (stab_le_normalizer_xm _ _ (hTst ht₀T)))
    intro w hw
    have h1 := hz (Subgroup.commutator_mem_commutator hw (Subgroup.mem_zpowers t₀))
    have e : t₀ * w * t₀⁻¹ * w⁻¹ = ⁅w, t₀⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact inv_mem h1
  have hPeq : P = vSub h.le γ ⊔ XM _ γ := le_antisymm hPVX hVX
  have hVXn : puTrans h.le L γ ≤
      Subgroup.normalizer
        ((vSub h.le γ ⊔ XM _ γ : Subgroup _) : Set (puAmalgam h.le).Universal) := by
    rw [← hPeq]
    exact (puTrans_le_stab h.le L γ).trans hstP
  have hB := inf_le_bSub_of_elt h h32' hγ (sup_le (hVQγ.trans hQγst) ((xm_le_qv _ _).trans hQγst))
    hVXn (hTst ht₀T) ht₀2 ht₀Q hPt₀
  have hUα : S5.uSub h.le L (baseA _) ≤ S5.bSub h.le L γ := by
    refine le_trans ?_ hB
    exact le_inf ((S5B.uSub_le_zm h.le _).trans (hVZ.trans le_sup_left))
      ((S5B.uSub_le_zm h.le _).trans
        (S5B.zm_le_vv_of_dist hα (by rw [SimpleGraph.dist_comm, hd2])))
  have hcγξ := ms22_iii _ hyp hb0 hC hξ
  have hgeoξ : geo _ γ ξ 2 = baseA (puAmalgam h.le) := by
    symm
    apply eq_geo_of_dist _ (by rw [SimpleGraph.dist_comm]; exact hd2)
    rw [SimpleGraph.dist_comm (u := γ) (v := baseA _), hd2,
      SimpleGraph.dist_comm (u := baseA _) (v := ξ), hcγξ.2.1]
    omega
  have hno := uSub_not_le_bSub h58 h hmin hb' hd hcγξ
  rw [hgeoξ] at hno
  exact hno hUα

end Case2

end S59

end CFSG.Quasithin.MS93
