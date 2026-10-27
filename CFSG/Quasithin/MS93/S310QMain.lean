module

public import CFSG.Quasithin.MS93.S310QNat
public import CFSG.Quasithin.MS93.S310QGam
public import CFSG.Quasithin.MS93.S5NQD

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

namespace S310Q

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem exists_isCritical_of_not_le (h : PUHyp M T L) (hb : critDist (puAmalgam h.le) = 4)
    {α γ : Vtx (puAmalgam h.le)} (hγ : IsMVtx _ γ)
    (hαγ : (puAmalgam h.le).treeGraph.dist α γ = 2)
    (hV : ¬ S5.nclStab _ α (ZM _ γ) ≤ Qv _ γ) :
    ∃ g ∈ stab _ α, IsCritical _ (g • γ) γ := by
  by_contra hall
  push Not at hall
  apply hV
  refine iSup_le fun g => ?_
  rw [← zm_smul]
  by_contra hle
  have hgα : (g : (puAmalgam h.le).Universal) • α = α := (mem_stab _).1 g.2
  have hgγ : IsMVtx _ ((g : (puAmalgam h.le).Universal) • γ) := (isMVtx_smul _ _ _).2 hγ
  have hd : (puAmalgam h.le).treeGraph.dist ((g : (puAmalgam h.le).Universal) • γ) γ = 4 := by
    have h1 := dist_triangle _ ((g : (puAmalgam h.le).Universal) • γ) α γ
    have h2 : (puAmalgam h.le).treeGraph.dist ((g : (puAmalgam h.le).Universal) • γ) α = 2 := by
      have h4 : (puAmalgam h.le).treeGraph.dist ((g : (puAmalgam h.le).Universal) • γ)
          ((g : (puAmalgam h.le).Universal) • α) = 2 := by
        rw [dist_smul, SimpleGraph.dist_comm, hαγ]
      rwa [hgα] at h4
    have h3 : ¬ (puAmalgam h.le).treeGraph.dist ((g : (puAmalgam h.le).Universal) • γ) γ <
        critDist (puAmalgam h.le) := fun hlt => hle (zm_le_qv_of_dist_lt _ hgγ hlt)
    rw [hb] at h3
    omega
  exact hall g g.2 ⟨hgγ, hd.trans hb.symm, hle⟩

theorem le_relIndex_zm (h : PUHyp M T L) {k : ℕ} {F : Type} [Field F] [Fintype F]
    {a : ↥M →* ↥(StatedSp 2 F)} (hd : S5.IsSp4Data M T L k F a) {ρ ρ' ν : Vtx (puAmalgam h.le)}
    (hc : IsCritical _ ρ' ρ) (hρ'ν : (puAmalgam h.le).treeGraph.Adj ρ' ν)
    (hZν : ZM _ ρ ≤ Qv _ ν) (hZ'ν : ZM _ ρ' ≤ Qv _ ν) :
    2 ^ k ≤ (Qv _ ρ').relIndex (ZM _ ρ) := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hc' : IsCritical _ ρ ρ' := ms22_iii _ hyp hb0 h.centHyp hc
  have hρ : IsMVtx _ ρ := hc'.1
  have hρ' : IsMVtx _ ρ' := hc.1
  have hν : ¬ IsMVtx _ ν := (isMVtx_iff_of_adj _ hρ'ν).1 hρ'
  have hZ'ρ : ZM _ ρ' ≤ stab _ ρ := zm_le_stab_of_isCritical _ hyp hb0 hc'
  have hZρ : ZM _ ρ ≤ stab _ ρ := (zm_le_qv_self _ hρ hb0).trans (qv_le_stab _ _)
  have := S310.finite_stab_of_isMVtx h hρ
  have : Finite ↥(ZM (puAmalgam h.le) ρ) := Finite.of_injective _ (Subgroup.inclusion_injective hZρ)
  have hZ'2 : IsPGroup 2 (ZM _ ρ') := (isPGroup_qv _ hyp hν).to_le hZ'ν
  have h1 := S5B.le_relIndex_centralizer h hd hρ hZ'ρ hZ'2 hc.2.2
  have h2 : (Subgroup.centralizer (ZM _ ρ' : Set (puAmalgam h.le).Universal)).relIndex
        (S5.uSub h.le L ρ) ≤
      (Subgroup.centralizer (ZM _ ρ' : Set (puAmalgam h.le).Universal)).relIndex (ZM _ ρ) :=
    Subgroup.relIndex_le_of_le_right (S5B.uSub_le_zm h.le ρ) Subgroup.FiniteIndex.index_ne_zero
  have h3 : Subgroup.centralizer (ZM _ ρ' : Set (puAmalgam h.le).Universal) ⊓ ZM _ ρ =
      Qv _ ρ' ⊓ ZM _ ρ := by
    ext z
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hzc, hz⟩
      rw [← h.centHyp ρ' ν hρ' hρ'ν]
      exact ⟨⟨hZν hz, hzc⟩, hz⟩
    · rintro ⟨hzQ, hz⟩
      refine ⟨Subgroup.mem_centralizer_iff.2 fun w hw => ?_, hz⟩
      exact ((Subgroup.mem_centralizer_iff.1 (zm_le_centralizer_qv _ hyp hρ' hw)) z hzQ).symm
  rw [← Subgroup.inf_relIndex_right, ← h3, Subgroup.inf_relIndex_right]
  exact h1.trans h2

theorem bSub_inf_zm_le_centralizer (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    {α γ μ α' : Vtx (puAmalgam h.le)} (hγ : IsMVtx _ γ) (hα : IsMVtx _ α)
    (hγμ : (puAmalgam h.le).treeGraph.Adj γ μ) (hμα' : (puAmalgam h.le).treeGraph.Adj μ α')
    (hA3 : ∃ g ∈ stab _ γ, g • α = α') :
    S5.bSub h.le L γ ⊓ ZM _ α' ≤
      Subgroup.centralizer ((Qv _ α ⊓ Qv _ γ : Subgroup _) : Set (puAmalgam h.le).Universal) := by
  have hyp := h.hyp20
  obtain ⟨g, hg, hgα⟩ := hA3
  obtain ⟨t, ht, s, hs, hts⟩ := S310.exists_puTrans_mul_of_isMVtx h hγ hγμ (inv_mem hg)
  have htα' : t • α' = α := by
    have hsα' : s • α' = α' := (mem_stab _).1 (qv_le_stab_of_adj _ hμα' hs)
    have : g⁻¹ • α' = α := by rw [← hgα, inv_smul_smul]
    rw [← this, hts, mul_smul, hsα']
  rintro u ⟨huB, huZ⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro y ⟨hyα, hyγ⟩
  have hcγ : ⁅u, t⁆ ∈ ZM _ γ := S5B.commutator_mem_zm_of_mem_bSub h hb hγ huB ht
  have hzα : t * u * t⁻¹ ∈ ZM _ α := by
    rw [← htα', zm_smul]
    exact ⟨u, huZ, rfl⟩
  have h1 : y * ⁅u, t⁆ = ⁅u, t⁆ * y :=
    (Subgroup.mem_centralizer_iff.1 (zm_le_centralizer_qv _ hyp hγ hcγ) y hyγ)
  have h2 : y * (t * u * t⁻¹) = (t * u * t⁻¹) * y :=
    (Subgroup.mem_centralizer_iff.1 (zm_le_centralizer_qv _ hyp hα hzα) y hyα)
  have e : u = ⁅u, t⁆ * (t * u * t⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e, ← mul_assoc, h1, mul_assoc ⁅u, t⁆ y, h2]
  exact (mul_assoc _ _ _).symm

end S310Q

theorem s310mQ_holds : S310mQ := by
  intro G _ _ M T L h hmin hfull hb α' hc k F _ _ a hF ha hnat hV₀D hA1 hA2 hA3
  obtain ⟨k₀, F₀, _, _, a₀, hd⟩ := S5.isSp4Full_iff.1 hfull
  have hk : k = k₀ := S310.k_eq_of_nat h hd hF ha hnat
  subst hk
  have : CharP F 2 := S5B.charP_two_of_card hF
  by_contra hVQγ
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hb2 : 2 < critDist (puAmalgam h.le) := by omega
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hd4 : (puAmalgam h.le).treeGraph.dist (baseA _) α' = 4 := hc.2.1.trans hb
  have hγ : IsMVtx _ (geo _ (baseA (puAmalgam h.le)) α' 2) := isMVtx_geo_two _ hyp hb0 hc
  have hαγ : (puAmalgam h.le).treeGraph.dist (baseA _) (geo _ (baseA (puAmalgam h.le)) α' 2) =
      2 := dist_geo _ (by omega)
  have hαδ : (puAmalgam h.le).treeGraph.Adj (baseA _) (geo _ (baseA (puAmalgam h.le)) α' 1) :=
    adj_geo_one _ (by omega)
  have hδγ : (puAmalgam h.le).treeGraph.Adj (geo _ (baseA (puAmalgam h.le)) α' 1)
      (geo _ (baseA (puAmalgam h.le)) α' 2) := adj_geo _ (by omega)
  have hγμ : (puAmalgam h.le).treeGraph.Adj (geo _ (baseA (puAmalgam h.le)) α' 2)
      (geo _ (baseA (puAmalgam h.le)) α' 3) := adj_geo _ (by omega)
  have hμα' : (puAmalgam h.le).treeGraph.Adj (geo _ (baseA (puAmalgam h.le)) α' 3) α' := by
    have := adj_geo (puAmalgam h.le) (u := baseA _) (w := α') (i := 3) (by omega)
    rwa [show (3 + 1 : ℕ) = (puAmalgam h.le).treeGraph.dist (baseA _) α' by omega,
      geo_dist] at this
  set γ := geo _ (baseA (puAmalgam h.le)) α' 2 with hγdef
  set δ := geo _ (baseA (puAmalgam h.le)) α' 1 with hδdef
  have hγα : (puAmalgam h.le).treeGraph.dist γ (baseA _) = 2 := by
    rw [SimpleGraph.dist_comm, hαγ]
  have hδ : ¬ IsMVtx _ δ := (isMVtx_iff_of_adj _ hαδ).1 hα
  have hc' : IsCritical _ α' (baseA _) := ms22_iii _ hyp hb0 h.centHyp hc
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  set A := stab (puAmalgam h.le) (baseA (puAmalgam h.le)) with hAdef
  set Lt := puTrans h.le L (baseA (puAmalgam h.le)) with hLtdef
  set Zγ := ZM (puAmalgam h.le) γ with hZγdef
  set V := S5.nclStab _ (baseA (puAmalgam h.le)) Zγ with hVdef
  set B := S5.bSub h.le L (baseA (puAmalgam h.le)) with hBdef
  set D := S5.dSub h.le L (baseA (puAmalgam h.le)) with hDdef
  set Q := Qv (puAmalgam h.le) (baseA (puAmalgam h.le)) with hQdef
  set V₀ := ⁅V, Lt⁆ with hV₀def
  have hLA : Lt ≤ A := puTrans_le_stab h.le L _
  have hALt : A ≤ Subgroup.normalizer (Lt : Set _) := stab_le_normalizer_puTrans h.le hLn _
  have hAV : A ≤ Subgroup.normalizer (V : Set _) := hnat.1
  have hperf : ⁅Lt, Lt⁆ = Lt := S310Q.puTrans_perfect h hα
  have hQA : Q ≤ A := qv_le_stab _ _
  have hQst : Q ≤ stab _ γ := qv_le_stab_of_dist_le_two _ hyp hα (by omega)
  have hZγV : Zγ ≤ V := fun z hz =>
    Subgroup.mem_iSup_of_mem (⟨1, one_mem _⟩ : ↥A) ⟨z, hz, by simp⟩
  have hVQ : V ≤ Q := S310.nclStab_le_qv h hγ hαγ hb2
  have hVA : V ≤ A := hVQ.trans hQA
  have hVZγ : V ≤ Subgroup.normalizer (Zγ : Set _) :=
    hVQ.trans (hQst.trans (stab_le_normalizer_zm _ _))
  have hZγab : ⁅Zγ, Zγ⁆ = ⊥ := by
    refine Subgroup.commutator_eq_bot_iff_le_centralizer.2 ?_
    exact (zm_le_centralizer_qv _ hyp hγ).trans
      (Subgroup.centralizer_le (zm_le_qv_self _ hγ hb0))
  have hDC : D ≤ Subgroup.centralizer (Lt : Set _) := inf_le_right
  have hAD : A ≤ Subgroup.normalizer (D : Set _) :=
    le_normalizer_inf (stab_le_normalizer_qv _ _) (le_normalizer_centralizer hALt)
  have hV₀V : V₀ ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.1 (hLA.trans hAV)
  have hAV₀ : A ≤ Subgroup.normalizer (V₀ : Set _) := le_normalizer_commutator hAV hALt
  have hV₀L : ⁅V₀, Lt⁆ = V₀ := by
    have hn : A ≤ Subgroup.normalizer ((⁅V₀, Lt⁆ : Subgroup _) : Set _) :=
      le_normalizer_commutator hAV₀ hALt
    exact le_antisymm (Subgroup.le_normalizer_iff_commutator_le_left.1 (hLA.trans hAV₀))
      (S5B.commutator_le_of_perfect hperf (hVA.trans hn) (hLA.trans hn) le_rfl le_rfl)
  have hVsup : V ≤ V₀ ⊔ Zγ := by
    refine iSup_le fun g => ?_
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨l, hl, t, ht, hg⟩ := S310.exists_mul_of_mem_stab h hαδ g.2
    have hz' : t * z * t⁻¹ ∈ Zγ :=
      (Subgroup.mem_normalizer_iff.1 (stab_le_normalizer_zm _ _ (qv_le_stab_of_adj _ hδγ ht))
        z).1 hz
    have hc'' : ⁅l, t * z * t⁻¹⁆ ∈ V₀ := by
      rw [hV₀def, Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hl (hZγV hz')
    have e : (MulAut.conj (g : (puAmalgam h.le).Universal)).toMonoidHom z =
        ⁅l, t * z * t⁻¹⁆ * (t * z * t⁻¹) := by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hg]
      simp only [commutatorElement_def]
      group
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left hc'') (Subgroup.mem_sup_right hz')
  obtain ⟨hVV₀, hVcard⟩ := S310.s310a_core h hb hc hF ha hnat hV₀D
  have hV'D : ⁅V, V⁆ ≤ D := hVV₀ ▸ hV₀D
  have hcomm : ⁅V₀, V ⊓ B⁆ = ⊥ := by
    have hZα : ⁅ZM _ (baseA (puAmalgam h.le)), V₀⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.2 ((zm_le_centralizer_qv _ hyp hα).trans
        (Subgroup.centralizer_le (hV₀V.trans hVQ)))
    have h1 : ⁅⁅Lt, V ⊓ B⁆, V₀⁆ = ⊥ := by
      rw [← le_bot_iff, ← hZα]
      refine Subgroup.commutator_mono ?_ le_rfl
      rw [Subgroup.commutator_comm, Subgroup.commutator_le]
      intro x hx l hl
      exact S310.commutator_mem_zm_of_mem_bSub h hb2 hx.2 hl
    have h2 : ⁅⁅V ⊓ B, V₀⁆, Lt⁆ = ⊥ := by
      rw [← le_bot_iff]
      calc ⁅⁅V ⊓ B, V₀⁆, Lt⁆ ≤ ⁅⁅V, V⁆, Lt⁆ :=
            Subgroup.commutator_mono (Subgroup.commutator_mono inf_le_left hV₀V) le_rfl
        _ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 (hV'D.trans hDC)
    have := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
    rwa [hV₀L] at this
  obtain ⟨βv, hs⟩ := S310.exists_setup h ha hnat
  have hfinA : Finite ↥A := S310.finite_stab_of_isMVtx h hα
  have hfinγ : Finite ↥(stab (puAmalgam h.le) γ) := S310.finite_stab_of_isMVtx h hγ
  obtain ⟨x₁, hx₁, hc1⟩ := S310Q.exists_isCritical_of_not_le h hb hγ hαγ hVQγ
  have hγ₁ : IsMVtx _ (x₁ • γ) := hc1.1
  have hZ1V : ZM _ (x₁ • γ) ≤ V := by
    rw [zm_smul]
    exact le_iSup (fun y : ↥A =>
      Zγ.map (MulAut.conj (y : (puAmalgam h.le).Universal)).toMonoidHom) ⟨x₁, hx₁⟩
  have hc1' : IsCritical _ γ (x₁ • γ) := ms22_iii _ hyp hb0 h.centHyp hc1
  have hx₁α : x₁ • baseA (puAmalgam h.le) = baseA _ := (mem_stab _).1 hx₁
  have hdγ₁α : (puAmalgam h.le).treeGraph.dist (x₁ • γ) (baseA _) = 2 := by
    have e := dist_smul (puAmalgam h.le) x₁ γ (baseA _)
    rw [hx₁α] at e
    rw [e, hγα]
  have hZ1δ : ZM _ (x₁ • γ) ≤ Qv _ δ := by
    refine zm_le_qv_of_dist_lt _ hγ₁ ?_
    have := dist_triangle _ (x₁ • γ) (baseA _) δ
    rw [hdγ₁α, dist_eq_one_of_adj _ hαδ] at this
    omega
  have hZγδ : Zγ ≤ Qv _ δ :=
    zm_le_qv_of_dist_lt _ hγ (by rw [dist_eq_one_of_adj _ hδγ.symm]; omega)
  obtain ⟨z, hzZ, hzQ⟩ := Set.not_subset.1 hc1.2.2
  have hz2 : IsPGroup 2 ↥(Subgroup.zpowers z) :=
    (isPGroup_qv _ hyp hδ).to_le ((Subgroup.zpowers_le).2 (hZ1δ hzZ))
  have hVγst : V ≤ stab _ γ := hVQ.trans hQst
  have hUγV : S5.uSub h.le L γ ≤ V := (S5B.uSub_le_zm h.le γ).trans hZγV
  obtain ⟨hVcard', hVC⟩ :=
    S310Q.card_commutator_ge h hd hγ hVγst hUγV (hZ1V hzZ) hz2 hzQ hVcard
  set Q₀ := ⁅Q, Lt⁆ with hQ₀def
  have hQ₀Q : Q₀ ≤ Q :=
    Subgroup.le_normalizer_iff_commutator_le_left.1 (hLA.trans (stab_le_normalizer_qv _ _))
  have hAQ₀ : A ≤ Subgroup.normalizer (Q₀ : Set _) :=
    le_normalizer_commutator (stab_le_normalizer_qv _ _) hALt
  have hZB0 : ⁅Q₀, Zγ ⊓ B⁆ = ⊥ := by
    refine Subgroup.commutator_commutator_eq_bot_of_rotate ?_ ?_
    · rw [← le_bot_iff]
      have h1 : ⁅Lt, Zγ ⊓ B⁆ ≤ ZM _ (baseA (puAmalgam h.le)) := by
        rw [Subgroup.commutator_comm, Subgroup.commutator_le]
        intro w hw l hl
        exact S310.commutator_mem_zm_of_mem_bSub h hb2 hw.2 hl
      refine (Subgroup.commutator_mono h1 le_rfl).trans (le_of_eq ?_)
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 (zm_le_centralizer_qv _ hyp hα)
    · rw [← le_bot_iff]
      have h2 : ⁅Zγ ⊓ B, Q⁆ ≤ D := by
        rw [Subgroup.commutator_le]
        intro w hw q hq
        exact S5NQ.commutator_mem_dSub_baseA h hb2 hαγ hw.1 hw.2 hq
      refine (Subgroup.commutator_mono h2 le_rfl).trans (le_of_eq ?_)
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 hDC
  have hQ₀C : Q₀ ≤ Subgroup.centralizer ((Zγ ⊓ B : Subgroup _) : Set _) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 hZB0
  have hUγZ : S5.uSub h.le L γ ≤ Zγ := S5B.uSub_le_zm h.le γ
  have hZγst : Zγ ≤ stab _ γ := (zm_le_qv_self _ hγ hb0).trans (qv_le_stab _ _)
  have : Finite ↥(S5.uSub h.le L γ) :=
    Finite.of_injective _ (Subgroup.inclusion_injective (hUγZ.trans hZγst))
  have : Finite ↥Zγ := Finite.of_injective _ (Subgroup.inclusion_injective hZγst)
  have hrelB : ∀ E : Subgroup (puAmalgam h.le).Universal,
      E ≤ Subgroup.centralizer ((Zγ ⊓ B : Subgroup _) : Set _) →
      (Subgroup.centralizer (E : Set _)).relIndex (S5.uSub h.le L γ) ≤ 2 ^ k := by
    intro E hE
    have h1 : B ⊓ S5.uSub h.le L γ ≤ Subgroup.centralizer (E : Set _) := by
      rw [Subgroup.le_centralizer_iff]
      exact hE.trans (Subgroup.centralizer_le fun u hu => ⟨hUγZ hu.2, hu.1⟩)
    calc (Subgroup.centralizer (E : Set _)).relIndex (S5.uSub h.le L γ)
        ≤ (B ⊓ S5.uSub h.le L γ).relIndex (S5.uSub h.le L γ) :=
          Subgroup.relIndex_le_of_le_left h1 Subgroup.FiniteIndex.index_ne_zero
      _ = B.relIndex (S5.uSub h.le L γ) := Subgroup.inf_relIndex_right _ _
      _ ≤ B.relIndex Zγ :=
          Subgroup.relIndex_le_of_le_right hUγZ Subgroup.FiniteIndex.index_ne_zero
      _ ≤ 2 ^ k := hA1
  have : Finite ↥V := Finite.of_injective _ (Subgroup.inclusion_injective hVA)
  have hlowγ : 2 ^ k ≤ (Qv _ γ).relIndex V :=
    (S310Q.le_relIndex_zm h hd hc1' hδγ.symm hZ1δ hZγδ).trans
      (Subgroup.relIndex_le_of_le_right hZ1V Subgroup.FiniteIndex.index_ne_zero)
  have hQδ : Q ≤ Qv _ δ := qv_le_qv _ hyp hα hαδ
  have hE : Q₀ ⊔ Zγ ≤ stab _ γ := sup_le (hQ₀Q.trans hQst) hZγst
  have hE2 : IsPGroup 2 ↥(Q₀ ⊔ Zγ) :=
    (isPGroup_qv _ hyp hδ).to_le (sup_le (hQ₀Q.trans hQδ) hZγδ)
  have hVE : V ≤ Q₀ ⊔ Zγ :=
    hVsup.trans (sup_le_sup_right (Subgroup.commutator_mono hVQ le_rfl) _)
  have hZγC : Zγ ≤ Subgroup.centralizer ((Zγ ⊓ B : Subgroup _) : Set _) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hZγab).trans
      (Subgroup.centralizer_le inf_le_left)
  have hrelE := hrelB (Q₀ ⊔ Zγ) (sup_le hQ₀C hZγC)
  have hQ₀VQ : ∀ w ∈ Q₀, ∃ v ∈ V, v⁻¹ * w ∈ Qv _ γ := fun w hw =>
    S310.exists_mem_mul_qv h hd hγ hE hE2 hVE hVQγ hrelE hlowγ (Subgroup.mem_sup_left hw)
  have hα' : IsMVtx _ α' := hc.isMVtx_right _ hyp
  obtain ⟨y, hyZ, hyQ⟩ := Set.not_subset.1 hc'.2.2
  have hyδ : y ∈ Qv _ δ := zm_le_qv_of_dist_lt _ hα'
    (by rw [SimpleGraph.dist_comm, hδdef, dist_geo_right _ (by omega), hd4, hb]; norm_num) hyZ
  have hyA : y ∈ A := qv_le_stab_of_isMVtx _ hyp hα hαδ hyδ
  have hy2 : ∃ e : ℕ, y ^ 2 ^ e = 1 := by
    obtain ⟨e, he⟩ := isPGroup_qv _ hyp hδ ⟨y, hyδ⟩
    exact ⟨e, by simpa using congrArg Subtype.val he⟩
  have hyγ : y ∈ Qv _ γ := zm_le_qv_of_dist_lt _ hα'
    (by rw [SimpleGraph.dist_comm, hγdef, dist_geo_right _ (by omega), hd4, hb]; norm_num) hyZ
  have hyC : ∀ z ∈ Zγ, y * z = z * y := fun z hz =>
    Subgroup.mem_centralizer_iff.1 (zm_le_centralizer_qv _ hyp hγ hz) y hyγ
  have hZαn : A ≤ Subgroup.normalizer (ZM _ (baseA (puAmalgam h.le)) : Set _) :=
    stab_le_normalizer_zm _ _
  have hyW : ∀ w ∈ Q₀, y * w * y⁻¹ * w⁻¹ ∈ V₀ ⊔ ZM _ (baseA (puAmalgam h.le)) := by
    intro w hw
    obtain ⟨v, hv, hve⟩ := hQ₀VQ w hw
    have he : v⁻¹ * w ∈ Q ⊓ Qv _ γ :=
      Subgroup.mem_inf.2 ⟨mul_mem (inv_mem (hVQ hv)) (hQ₀Q hw), hve⟩
    have hez : ⁅v⁻¹ * w, y⁆ ∈ ZM _ (baseA (puAmalgam h.le)) :=
      S310.commutator_mem_zm h hd hb hc hγ hαγ hγμ hμα' hA2 hA3 he hyZ
    have hv' := hVsup hv
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left V₀ Zγ
      (hZγV.trans (hVA.trans hAV₀))] at hv'
    obtain ⟨v₀, hv₀, z₀, hz₀, hvv⟩ := hv'
    have hyz₀ := hyC z₀ hz₀
    have key : y * w * y⁻¹ * w⁻¹ =
        (y * v₀ * y⁻¹ * v₀⁻¹) * (v * ⁅y, v⁻¹ * w⁆ * v⁻¹) := by
      rw [← hvv]
      calc y * w * y⁻¹ * w⁻¹
          = (y * v₀ * y⁻¹ * v₀⁻¹) * (v₀ * (y * z₀) * ((v₀ * z₀)⁻¹ * w) * y⁻¹ *
              ((v₀ * z₀)⁻¹ * w)⁻¹ * z₀⁻¹ * v₀⁻¹) := by group
        _ = (y * v₀ * y⁻¹ * v₀⁻¹) * (v₀ * (z₀ * y) * ((v₀ * z₀)⁻¹ * w) * y⁻¹ *
              ((v₀ * z₀)⁻¹ * w)⁻¹ * z₀⁻¹ * v₀⁻¹) := by rw [hyz₀]
        _ = (y * v₀ * y⁻¹ * v₀⁻¹) * (v₀ * z₀ * ⁅y, (v₀ * z₀)⁻¹ * w⁆ * (v₀ * z₀)⁻¹) := by
          simp only [commutatorElement_def]
          group
    rw [key]
    refine mul_mem (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right ?_)
    · exact mul_mem ((Subgroup.mem_normalizer_iff.1 (hAV₀ hyA) v₀).1 hv₀) (inv_mem hv₀)
    · have hye : ⁅y, v⁻¹ * w⁆ ∈ ZM _ (baseA (puAmalgam h.le)) := by
        rw [← commutatorElement_inv]
        exact inv_mem hez
      exact (Subgroup.mem_normalizer_iff.1 (hZαn (hVA hv)) _).1 hye
  have hZn : A ≤ Subgroup.normalizer
      ((V₀ ⊔ ZM _ (baseA (puAmalgam h.le)) : Subgroup _) : Set _) :=
    le_normalizer_sup hAV₀ hZαn
  have hZαA : ZM _ (baseA (puAmalgam h.le)) ≤ A := (zm_le_qv_self _ hα hb0).trans hQA
  have hcore := S310.commutator_le_of_two_elt_baseA h (hQ₀Q.trans hQA)
    (sup_le (hV₀V.trans hVA) hZαA) (hLA.trans hAQ₀) (hLA.trans hZn) hyA hy2 hyQ (hZn hyA) hyW
  have hZαV : ZM _ (baseA (puAmalgam h.le)) ≤ V := S310Q.zm_le_nclStab_of_adj h hαδ hδγ
  have hUα : ⁅ZM _ (baseA (puAmalgam h.le)), Lt⁆ ≤ V₀ := Subgroup.commutator_mono hZαV le_rfl
  have hQ₀V₀ : Q₀ ≤ V₀ := by
    have h1 : ⁅Q₀, Lt⁆ ≤ V₀ :=
      S5B.commutator_le_of_perfect hperf ((hQ₀Q.trans hQA).trans hAV₀) (hLA.trans hAV₀) hcore
        (S310.commutator_sup_left_le ((hV₀V.trans hVA).trans hAV₀) (hZαA.trans hAV₀)
          (Subgroup.le_normalizer_iff_commutator_le_left.1 (hLA.trans hAV₀)) hUα)
    have hn : A ≤ Subgroup.normalizer ((⁅Q₀, Lt⁆ : Subgroup _) : Set _) :=
      le_normalizer_commutator hAQ₀ hALt
    have h2 : Q₀ ≤ ⁅Q₀, Lt⁆ :=
      S5B.commutator_le_of_perfect hperf (hQA.trans hn) (hLA.trans hn) le_rfl le_rfl
    exact h2.trans h1
  have hVVv : V ≤ Vv _ (baseA (puAmalgam h.le)) := S310Q.nclStab_le_vv h hγ hαγ
  have hvo₁ : V₀ ≤ S5.voSub h.le L (baseA _) := Subgroup.commutator_mono hVVv le_rfl
  have hvo₂ : S5.voSub h.le L (baseA _) ≤ Q₀ :=
    Subgroup.commutator_mono (S310.vv_le_qv_baseA h hb2) le_rfl
  have hvoα : S5.voSub h.le L (baseA (puAmalgam h.le)) = V₀ :=
    le_antisymm (hvo₂.trans hQ₀V₀) hvo₁
  have hQvo : ⁅Q, Lt⁆ = S5.voSub h.le L (baseA _) := le_antisymm (hQ₀V₀.trans hvo₁) hvo₂
  have hirr : ∀ X : Subgroup (puAmalgam h.le).Universal, X ≤ S5.voSub h.le L (baseA _) →
      A ≤ Subgroup.normalizer (X : Set _) → ¬ X ≤ B →
      S5.voSub h.le L (baseA _) ≤ X ⊔ (S5.voSub h.le L (baseA _) ⊓ B) := by
    intro X hX hXn hXB
    rw [hvoα] at hX ⊢
    have hXV : X ≤ V := hX.trans hV₀V
    have hXB' : ¬ X ≤ V ⊓ B := fun hle => hXB (hle.trans inf_le_right)
    intro v hv
    obtain ⟨w, hw, hwv⟩ := S310Q.exists_mem_of_not_le hs hXV hXn hXB' (βv v)
    have hwv' : w⁻¹ * v ∈ V ⊓ B := by
      refine (hs.ker _ (mul_mem (inv_mem (hXV hw)) (hV₀V hv))).1 ?_
      rw [hs.map_mul _ (inv_mem (hXV hw)) _ (hV₀V hv), hs.map_inv (hXV hw), hwv, neg_add_cancel]
    have e : v = w * (w⁻¹ * v) := by group
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left hw)
      (Subgroup.mem_sup_right (Subgroup.mem_inf.2 ⟨mul_mem (inv_mem (hX hw)) hv, hwv'.2⟩))
  have hQγvo := S310Q.commutator_qv_eq_voSub h hQvo hγ
  have hVoDγ := S310Q.commutator_voSub_le_dSub h (by rw [hvoα]; exact hV₀D) hγ
  have hirrγ : ∀ X : Subgroup (puAmalgam h.le).Universal, X ≤ S5.voSub h.le L γ →
      stab _ γ ≤ Subgroup.normalizer (X : Set _) → ¬ X ≤ S5.bSub h.le L γ →
      S5.voSub h.le L γ ≤ X ⊔ (S5.voSub h.le L γ ⊓ S5.bSub h.le L γ) :=
    fun X hX hXn hXB => S310Q.voSub_le_sup_of_not_le h hirr hγ hX hXn hXB
  have hZB : ¬ ZM _ (baseA (puAmalgam h.le)) ≤ S5.bSub h.le L γ := by
    intro hle
    obtain ⟨g, hg, hgα⟩ := hA3
    have hZ' : ZM _ α' ≤ S5.bSub h.le L γ := by
      rw [← hgα, zm_smul]
      rintro _ ⟨u, hu, rfl⟩
      exact (Subgroup.mem_normalizer_iff.1 (S310.stab_le_normalizer_bSub h γ hg) u).1 (hle hu)
    have hEC := S310Q.bSub_inf_zm_le_centralizer h hb2 hγ hα hγμ hμα' ⟨g, hg, hgα⟩
    apply ms22_ii _ hyp hb0 h.centHyp hc
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff]
    intro w hw
    exact Subgroup.centralizer_le (le_inf (zm_le_qv_self _ hα hb0)
      (zm_le_qv_of_dist_lt _ hα (by rw [hαγ, hb]; norm_num))) (hEC ⟨hZ' hw, hw⟩)
  have hQαγ : ¬ Q ≤ Qv _ γ := fun hle => hVQγ (hVQ.trans hle)
  have hvoγ := S310Q.voSub_le_commutator_nclStab h hb2 hγ hα hδγ.symm hαδ.symm hγα hirrγ hZB
  have hvoγ' : S5.voSub h.le L γ ≤ S5.nclStab _ γ (ZM _ (baseA (puAmalgam h.le))) :=
    hvoγ.trans (Subgroup.le_normalizer_iff_commutator_le_left.1
      ((puTrans_le_stab h.le L γ).trans (S310.stab_le_normalizer_nclStab _ γ _)))
  have hVγD := S310Q.commutator_nclStab_le_dSub h hb2 hγ hα hδγ.symm hαδ.symm hγα hVoDγ hQαγ
  have hQδA : Qv _ δ ≤ A := qv_le_stab_of_adj _ hαδ.symm
  have hY := S310Q.commutator_inf_qv_le_dSub h hb2 hγ hα hδγ.symm hγα hQγvo hvoγ' hVγD
    (P := V₀) (hV₀V.trans hVQ) (hQδA.trans hAV₀)
  have hV₀γ : V₀ ≤ stab _ γ := (hV₀V.trans hVQ).trans hQst
  have hV₀2 : IsPGroup 2 ↥V₀ := (isPGroup_qv _ hyp hδ).to_le ((hV₀V.trans hVQ).trans hQδ)
  have hidx : (Qv _ γ).relIndex V₀ ≤ 2 ^ k :=
    S310Q.relIndex_qv_le h hd hγ hV₀γ hV₀2 (hrelB V₀ ((hvo₁.trans hvo₂).trans hQ₀C))
  have : Finite ↥V₀ := Finite.of_injective _ (Subgroup.inclusion_injective (hV₀V.trans hVA))
  obtain ⟨u, hu, w, hw, hf⟩ := S310Q.exists_form_ne_zero hs (K := Qv _ γ) (by rw [hF]; exact hidx)
  have hcardF : Fintype.card F ≤ Nat.card ↥⁅V₀, V₀⁆ := by
    rw [hF, ← hVV₀]
    exact hVcard'
  have hne := S310Q.commutator_ne_one hs hcomm (hV₀D.trans hDC) hV₀L hcardF hu.2 hw.2 hf
  have hmemD : ⁅u, w⁆ ∈ S5.dSub h.le L γ :=
    hY (Subgroup.commutator_mem_commutator ⟨hu.2, hu.1⟩ ⟨hw.2, hw.1⟩)
  have hmemV : ⁅u, w⁆ ∈ ⁅V, V⁆ := Subgroup.commutator_mem_commutator (hV₀V hu.2) (hV₀V hw.2)
  exact hne (hVC _ hmemV hmemD.2)

theorem s310mCore_holds : S310mCore := s310mCore_of s310mQ_holds

theorem s310m_holds : S310m := s310m_of s310mCore_holds

end CFSG.Quasithin.MS93
