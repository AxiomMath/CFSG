module

public import CFSG.Quasithin.MS93.S512LNat
public import CFSG.Quasithin.MS93.S512LOff

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

namespace S512L

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem core_v₁ (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    (hV₁c : ⁅S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ (geo _ (baseA (puAmalgam h.le)) α' 2)),
        S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ (geo _ (baseA (puAmalgam h.le)) α' 2))⁆ ≤
      stabCenter _ (baseA (puAmalgam h.le))) :
    ⁅S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ (geo _ (baseA (puAmalgam h.le)) α' 2)),
        S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ (geo _ (baseA (puAmalgam h.le)) α' 2))⁆ ≤
      ⁅⁅S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ (geo _ (baseA (puAmalgam h.le)) α' 2)),
          puTrans h.le L (baseA _)⁆,
        ⁅S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ (geo _ (baseA (puAmalgam h.le)) α' 2)),
          puTrans h.le L (baseA _)⁆⁆ ∧
    ⁅⁅S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ (geo _ (baseA (puAmalgam h.le)) α' 2)),
          puTrans h.le L (baseA _)⁆,
        ⁅S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ (geo _ (baseA (puAmalgam h.le)) α' 2)),
          puTrans h.le L (baseA _)⁆ ⊓ S5.bSub h.le L (baseA _)⁆ = ⊥ ∧
    ⁅⁅S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ (geo _ (baseA (puAmalgam h.le)) α' 2)),
        puTrans h.le L (baseA _)⁆, puTrans h.le L (baseA (puAmalgam h.le))⁆ =
      ⁅S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ (geo _ (baseA (puAmalgam h.le)) α' 2)),
        puTrans h.le L (baseA _)⁆ := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have hd : (puAmalgam h.le).treeGraph.dist (baseA _) α' = critDist (puAmalgam h.le) := hc.2.1
  have hγM : IsMVtx _ (geo _ (baseA (puAmalgam h.le)) α' 2) := isMVtx_geo_two _ hyp hb0 hc
  have hdαγ : (puAmalgam h.le).treeGraph.dist (baseA _) (geo _ (baseA (puAmalgam h.le)) α' 2) =
      2 := dist_geo _ (by omega)
  have hαδ : (puAmalgam h.le).treeGraph.Adj (baseA _) (geo _ (baseA (puAmalgam h.le)) α' 1) :=
    adj_geo_one _ (by omega)
  have hδγ : (puAmalgam h.le).treeGraph.Adj (geo _ (baseA (puAmalgam h.le)) α' 1)
      (geo _ (baseA (puAmalgam h.le)) α' 2) := adj_geo _ (by omega)
  set γ := geo _ (baseA (puAmalgam h.le)) α' 2 with hγdef
  set Lt := puTrans h.le L (baseA (puAmalgam h.le)) with hLtdef
  set V₁ := S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ γ) with hV₁def
  have hV₁Q : V₁ ≤ Qv _ (baseA (puAmalgam h.le)) := S310.nclStab_le_qv h hγM hdαγ hb
  have hV₁st : V₁ ≤ stab _ (baseA (puAmalgam h.le)) := hV₁Q.trans (qv_le_stab _ _)
  have hLA : Lt ≤ stab _ (baseA (puAmalgam h.le)) := puTrans_le_stab h.le L _
  have hALt : stab _ (baseA (puAmalgam h.le)) ≤ Subgroup.normalizer (Lt : Set _) :=
    stab_le_normalizer_puTrans h.le hLn _
  have hAV₁ : stab _ (baseA (puAmalgam h.le)) ≤ Subgroup.normalizer (V₁ : Set _) :=
    S310.stab_le_normalizer_nclStab _ _ _
  set V₀ := ⁅V₁, Lt⁆ with hV₀def
  have hV₀V₁ : V₀ ≤ V₁ := commutator_le_left_of_le_normalizer (hLA.trans hAV₁)
  have hAV₀ : stab _ (baseA (puAmalgam h.le)) ≤ Subgroup.normalizer (V₀ : Set _) :=
    le_normalizer_commutator hAV₁ hALt
  have hV₀L : ⁅V₀, Lt⁆ = V₀ := by
    have hn : stab _ (baseA (puAmalgam h.le)) ≤
        Subgroup.normalizer ((⁅V₀, Lt⁆ : Subgroup _) : Set _) :=
      le_normalizer_commutator hAV₀ hALt
    exact le_antisymm (commutator_le_left_of_le_normalizer (hLA.trans hAV₀))
      (S5B.commutator_le_of_perfect (S512N.perfect_puTrans h) (hV₁st.trans hn) (hLA.trans hn)
        le_rfl le_rfl)
  have hZγV : ZM _ γ ≤ V₁ := S512R.zm_le_nclStab h γ
  have hVsup : V₁ ≤ V₀ ⊔ ZM _ γ := by
    refine iSup_le fun g => ?_
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨l, hl, t, ht, hg⟩ := S310.exists_mul_of_mem_stab h hαδ g.2
    have hz' : t * z * t⁻¹ ∈ ZM _ γ :=
      (Subgroup.mem_normalizer_iff.1 (stab_le_normalizer_zm _ _ (qv_le_stab_of_adj _ hδγ ht))
        z).1 hz
    have hc' : ⁅l, t * z * t⁻¹⁆ ∈ V₀ := by
      rw [hV₀def, Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hl (hZγV hz')
    have e : (MulAut.conj (g : (puAmalgam h.le).Universal)).toMonoidHom z =
        ⁅l, t * z * t⁻¹⁆ * (t * z * t⁻¹) := by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hg]
      simp only [commutatorElement_def]
      group
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left hc') (Subgroup.mem_sup_right hz')
  have hcen : ∀ x ∈ V₁, ∀ y ∈ V₁, ∀ z ∈ V₁, z * ⁅x, y⁆ = ⁅x, y⁆ * z := fun x hx y hy z hz =>
    S510.commute_of_mem_stabCenter (hV₁c (Subgroup.commutator_mem_commutator hx hy)) (hV₁st hz)
  have hLc : ∀ x ∈ V₁, ∀ y ∈ V₁, ∀ l ∈ Lt, l * ⁅x, y⁆ = ⁅x, y⁆ * l := fun x hx y hy l hl =>
    S510.commute_of_mem_stabCenter (hV₁c (Subgroup.commutator_mem_commutator hx hy)) (hLA hl)
  have hT1 := commutator_le_commutator_self hV₀V₁ le_rfl hV₀L.ge (hLA.trans hAV₁) (hLA.trans hAV₀)
    hcen hLc
  have hZγab : ⁅ZM _ γ, ZM _ γ⁆ = ⊥ := by
    refine Subgroup.commutator_eq_bot_iff_le_centralizer.2 ?_
    exact (zm_le_centralizer_qv _ hyp hγM).trans
      (Subgroup.centralizer_le (zm_le_qv_self _ hγM hb0))
  have hN : stab _ (baseA (puAmalgam h.le)) ≤
      Subgroup.normalizer ((⁅V₀, V₀⁆ : Subgroup _) : Set (puAmalgam h.le).Universal) :=
    le_normalizer_commutator hAV₀ hAV₀
  have hV₁' : ⁅V₁, V₁⁆ ≤ ⁅V₀, V₀⁆ :=
    (Subgroup.commutator_mono hVsup hVsup).trans (S310.commutator_sup_sup_le
      ((hV₀V₁.trans hV₁st).trans hN) ((hZγV.trans hV₁st).trans hN) le_rfl
      ((Subgroup.commutator_mono le_rfl hZγV).trans hT1) (by rw [hZγab]; exact bot_le))
  have hcomm : ⁅V₀, V₀ ⊓ S5.bSub h.le L (baseA _)⁆ = ⊥ := by
    have hZα : ⁅ZM _ (baseA (puAmalgam h.le)), V₀⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.2 ((zm_le_centralizer_qv _ hyp hα).trans
        (Subgroup.centralizer_le (hV₀V₁.trans hV₁Q)))
    have h1 : ⁅⁅Lt, V₀ ⊓ S5.bSub h.le L (baseA _)⁆, V₀⁆ = ⊥ := by
      rw [← le_bot_iff, ← hZα]
      refine Subgroup.commutator_mono ?_ le_rfl
      rw [Subgroup.commutator_comm, Subgroup.commutator_le]
      intro x hx l hl
      exact S310.commutator_mem_zm_of_mem_bSub h hb hx.2 hl
    have h2 : ⁅⁅V₀ ⊓ S5.bSub h.le L (baseA _), V₀⁆, Lt⁆ = ⊥ := by
      rw [← le_bot_iff]
      calc ⁅⁅V₀ ⊓ S5.bSub h.le L (baseA _), V₀⁆, Lt⁆ ≤ ⁅⁅V₁, V₁⁆, Lt⁆ :=
            Subgroup.commutator_mono (Subgroup.commutator_mono (inf_le_left.trans hV₀V₁) hV₀V₁)
              le_rfl
        _ = ⊥ := by
          rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
          intro x hx
          rw [Subgroup.mem_centralizer_iff]
          intro l hl
          exact S510.commute_of_mem_stabCenter (hV₁c hx) (hLA hl)
    have := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
    rwa [hV₀L] at this
  exact ⟨hV₁', hcomm, hV₀L⟩

theorem false_of_core (h14 : MS14AS) (hSQ : SQTKQuot)
    (hT : S32.TypeFacts) (h32 : S32) (h52 : S52) (h53 : S53) (h54 : S54) (h55 : S55)
    (h56 : S56) (h : PUHyp M T L) (hmin : PUMin M T L) (hb4 : critDist (puAmalgam h.le) = 4)
    (hd : S5.IsSp4Data M T L k F a) (hk2 : 2 ≤ k)
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    (hαβ : geo _ (baseA (puAmalgam h.le)) α' 1 = baseB _) {l : Submodule F (MSP.V4 F)}
    (hl : S5.Case56 h (2 ^ k) a (geo _ (baseA (puAmalgam h.le)) α' 2) l)
    {μ : Vtx (puAmalgam h.le)} {y : (puAmalgam h.le).Universal}
    (hy : y ∈ stab _ (baseA (puAmalgam h.le))) (hμy : μ = y • geo _ (baseA (puAmalgam h.le)) α' 2)
    (hcμ : IsCritical _ μ (geo _ (baseA (puAmalgam h.le)) α' 2))
    (hbad : 2 ^ k < (Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2)).relIndex (ZM _ μ))
    (hRc : ⁅ZM (puAmalgam h.le) μ, ZM (puAmalgam h.le) (geo _ (baseA (puAmalgam h.le)) α' 2)⁆ ≤
      stabCenter _ (baseA (puAmalgam h.le))) : False := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hk : 1 < 2 ^ k := Nat.one_lt_two_pow (by omega)
  have hfin := S310.finite_stab_of_isMVtx h hα
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  set γ := geo _ (baseA (puAmalgam h.le)) α' 2 with hγdef
  have hγM : IsMVtx _ γ := isMVtx_geo_two _ hyp hb0 hc
  have hdαγ : (puAmalgam h.le).treeGraph.dist (baseA _) γ = 2 :=
    dist_geo _ (by have := hc.2.1; omega)
  have hβγ : (puAmalgam h.le).treeGraph.Adj (baseB _) γ := by
    rw [← hαβ]
    exact adj_geo _ (by have := hc.2.1; omega)
  have hβα := (adj_baseA_baseB (puAmalgam h.le)).symm
  have hv := S512R.fullVQD56_holds h52 h54 h55 h56 G M T L h hmin hb4 k F _ _ a hd α' hc hαβ l
    hl μ ⟨y, hy, hμy⟩ hcμ hbad hRc
  obtain ⟨l', hl', hTl⟩ := S512R.qv_le_vPre_qLine_core h54 h hmin hb4 hd hc hy hμy hcμ hbad hRc
  obtain ⟨hμM, -, -, -, -, -, -, -, -, -, -, -⟩ := S512T.pair_facts h hb4 hcμ
  obtain ⟨hrel, -⟩ := S512T.bad_indices h hb4 hd hcμ hbad
  have hΛ : (2 ^ k) ^ 2 ≤ (Qv _ γ).relIndex (ZM _ μ) := by
    rw [S512T.relIndex_qv_zm_eq h hb4 hcμ, hrel]
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
  have hpair := S512R.commutator_nclStab_qv_le h32 h53 h hmin hd hb hl' hTl hv hβα hβγ
  have hV₁Q : S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ γ) ≤ Qv _ (baseA (puAmalgam h.le)) :=
    S310.nclStab_le_qv h hγM hdαγ hb
  have hV₁c : ⁅S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ γ),
      S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ γ)⁆ ≤ stabCenter _ (baseA (puAmalgam h.le)) :=
    ((Subgroup.commutator_mono le_rfl hV₁Q).trans hpair).trans inf_le_right
  obtain ⟨hV₁', hcomm, hV₀L⟩ := core_v₁ h hb hc hV₁c
  obtain ⟨-, hst, -, -⟩ := S512T.zm_facts h hb4 hcμ
  have hlow := S512R.relIndex_le_card_commutator h hd hcμ.1 hst
  rw [hrel] at hlow
  have hRV : ⁅S5.uSub h.le L μ, ZM _ γ⁆ ≤ ⁅S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ γ),
      S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ γ)⁆ := by
    refine Subgroup.commutator_mono ((S5B.uSub_le_zm h.le μ).trans ?_) (S512R.zm_le_nclStab h γ)
    rw [hμy]
    exact S512R.zm_smul_le_nclStab h hy _
  have hAV₁ : stab _ (baseA (puAmalgam h.le)) ≤
      Subgroup.normalizer (S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ γ) : Set _) :=
    S310.stab_le_normalizer_nclStab _ _ _
  have hAV₀ : stab _ (baseA (puAmalgam h.le)) ≤ Subgroup.normalizer
      ((⁅S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ γ), puTrans h.le L (baseA _)⁆ :
        Subgroup _) : Set _) :=
    le_normalizer_commutator hAV₁ (stab_le_normalizer_puTrans h.le hLn _)
  have hV₀o : ⁅S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ γ), puTrans h.le L (baseA _)⁆ ≤
      S5.voSub h.le L (baseA _) :=
    Subgroup.commutator_mono (S512N.nclStab_le_vv h hγM hdαγ.le) le_rfl
  have hV₀st : ⁅S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ γ), puTrans h.le L (baseA _)⁆ ≤
      stab _ (baseA (puAmalgam h.le)) :=
    hV₀o.trans ((voSub_le_vv h).trans ((S310.vv_le_qv_baseA h hb).trans (qv_le_stab _ _)))
  have hV₀'st : ⁅⁅S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ γ), puTrans h.le L (baseA _)⁆,
      ⁅S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ γ), puTrans h.le L (baseA _)⁆⁆ ≤
      stab _ (baseA (puAmalgam h.le)) := commutator_le_of_le hV₀st hV₀st
  have : Finite ↥⁅⁅S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ γ), puTrans h.le L (baseA _)⁆,
      ⁅S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ γ), puTrans h.le L (baseA _)⁆⁆ :=
    Finite.of_injective _ (Subgroup.inclusion_injective hV₀'st)
  have hcard := (Subgroup.card_le_of_le (hRV.trans hV₁')).trans' hlow
  have hV₀B : ¬ ⁅S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ γ), puTrans h.le L (baseA _)⁆ ≤
      S5.bSub h.le L (baseA _) := by
    intro hle
    have hZ : ⁅S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ γ), puTrans h.le L (baseA _)⁆ ≤
        ZM _ (baseA (puAmalgam h.le)) := by
      have h1 : ⁅⁅S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ γ), puTrans h.le L (baseA _)⁆,
          puTrans h.le L (baseA (puAmalgam h.le))⁆ ≤ ZM _ (baseA (puAmalgam h.le)) :=
        Subgroup.commutator_le.2 fun x hx l hl =>
          S310.commutator_mem_zm_of_mem_bSub h hb (hle hx) hl
      rwa [hV₀L] at h1
    have hab : ⁅⁅S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ γ), puTrans h.le L (baseA _)⁆,
        ⁅S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ γ), puTrans h.le L (baseA _)⁆⁆ = ⊥ := by
      refine Subgroup.commutator_eq_bot_iff_le_centralizer.2 (hZ.trans ?_)
      exact (zm_le_centralizer_qv _ hyp hα).trans (Subgroup.centralizer_le (hV₀o.trans
        ((voSub_le_vv h).trans (S310.vv_le_qv_baseA h hb))))
    rw [hab, Subgroup.card_bot] at hcard
    have : 1 < (2 ^ k) ^ 2 := by nlinarith
    omega
  have hsec := secHyp_voSub h hb hv hone.1
  obtain ⟨S, _, p, ρ, hs⟩ := hsec.exists_secMod
  have hirr : ∀ S₁ : Subgroup S, S₁ ≠ ⊥ → S512N.IsInv ρ S₁ → S₁ = ⊤ :=
    fun S₁ hne hS₁ => eq_top_of_isInv h hb hone le_rfl hs hne hS₁
  obtain ⟨W, E, δ, hWst, hVW, hEβ, hpairWE, hidx, hlt⟩ :=
    exists_offender h32 h53 h hmin hb4 hd hl' hTl hv hone hc hαβ hy hμy hcμ hbad
  obtain ⟨F', iF, fF, a', θ, hcardF, ha', hθ⟩ := exists_natural h14 hSQ hT h hd hk2 hb hv hl' hTl
    hsec hs hirr hWst hVW hEβ hpairWE hidx (hk.trans hlt)
  obtain ⟨βv, hSetup⟩ := exists_setup h hs hirr ha' hθ hV₀o hAV₀ hV₀B
  have : CharP F' 2 := S5B.charP_two_of_card hcardF
  have hD : ⁅⁅⁅S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ γ), puTrans h.le L (baseA _)⁆,
        puTrans h.le L (baseA (puAmalgam h.le))⁆,
      ⁅⁅S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ γ), puTrans h.le L (baseA _)⁆,
        puTrans h.le L (baseA (puAmalgam h.le))⁆⁆ ≤
      Subgroup.centralizer (puTrans h.le L (baseA (puAmalgam h.le)) : Set _) := by
    rw [hV₀L]
    intro x hx
    have hV₀V₁ : ⁅S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ γ), puTrans h.le L (baseA _)⁆ ≤
        S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ γ) :=
      commutator_le_left_of_le_normalizer ((puTrans_le_stab h.le L _).trans hAV₁)
    have hx' : x ∈ stabCenter _ (baseA (puAmalgam h.le)) :=
      hV₁c ((Subgroup.commutator_mono hV₀V₁ hV₀V₁) hx)
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact S510.commute_of_mem_stabCenter hx' (puTrans_le_stab h.le L _ hl)
  have hbound := hSetup.card_comm_le (by rw [hV₀L]; exact hcomm) hD (by rw [hV₀L, hV₀L])
  rw [hV₀L, hcardF] at hbound
  have : 2 ^ k < (2 ^ k) ^ 2 := by nlinarith
  omega

end S512L

end CFSG.Quasithin.MS93
