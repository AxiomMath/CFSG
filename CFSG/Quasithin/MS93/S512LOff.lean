module

public import CFSG.Quasithin.MS93.S512LMod
public import CFSG.Quasithin.MS93.S512RPair
public import CFSG.Quasithin.MS93.S512RLem

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

namespace S512L

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem zm_not_le_bSub (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    {ρ ρ' : Vtx (puAmalgam h.le)} (hc : IsCritical _ ρ ρ')
    (hmid : geo _ ρ ρ' 2 = baseA (puAmalgam h.le)) :
    ¬ ZM _ ρ ≤ S5.bSub h.le L (baseA _) := by
  intro hle
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hiv := ms22_iv _ hyp hb0 h.centHyp hc
  rw [hmid] at hiv
  apply hiv
  have hd : (puAmalgam h.le).treeGraph.dist ρ ρ' = critDist (puAmalgam h.le) := hc.2.1
  have hρβ : (puAmalgam h.le).treeGraph.Adj ρ (geo _ ρ ρ' 1) := adj_geo_one _ (by omega)
  have hβα : (puAmalgam h.le).treeGraph.Adj (geo _ ρ ρ' 1) (baseA (puAmalgam h.le)) := by
    have := adj_geo _ (u := ρ) (w := ρ') (i := 1) (by omega)
    rwa [hmid] at this
  have hXn : stab _ (baseA (puAmalgam h.le)) ≤
      Subgroup.normalizer (XM _ (baseA (puAmalgam h.le)) : Set (puAmalgam h.le).Universal) :=
    stab_le_normalizer_xm _ _
  have hZX : ZM _ (baseA (puAmalgam h.le)) ≤ XM _ (baseA (puAmalgam h.le)) :=
    zm_le_xm _ hyp hb0 hα
  have hLn : puTrans h.le L (baseA _) ≤ Subgroup.normalizer
      ((ZM _ ρ ⊔ XM _ (baseA (puAmalgam h.le)) : Subgroup _) : Set (puAmalgam h.le).Universal) := by
    refine le_normalizer_of_map_conj_le fun l hl => ?_
    rw [Subgroup.map_sup]
    refine sup_le ?_ ((map_conj_eq_of_mem_normalizer
      (hXn (puTrans_le_stab h.le L _ hl))).le.trans le_sup_right)
    rintro _ ⟨z, hz, rfl⟩
    have hc1 : ⁅z, l⁆ ∈ ZM _ (baseA (puAmalgam h.le)) :=
      S310.commutator_mem_zm_of_mem_bSub h hb (hle hz) hl
    have e : (MulAut.conj l).toMonoidHom z = ⁅z, l⁆⁻¹ * z := by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def]
      group
    rw [e]
    exact mul_mem (Subgroup.mem_sup_right (inv_mem (hZX hc1))) (Subgroup.mem_sup_left hz)
  have hTn : Qv _ (geo _ ρ ρ' 1) ≤ Subgroup.normalizer
      ((ZM _ ρ ⊔ XM _ (baseA (puAmalgam h.le)) : Subgroup _) : Set (puAmalgam h.le).Universal) :=
    le_normalizer_sup ((qv_le_stab_of_adj _ hρβ.symm).trans (stab_le_normalizer_zm _ _))
      ((qv_le_stab_of_adj _ hβα).trans hXn)
  intro g hg
  obtain ⟨l, hl, t, ht, rfl⟩ := S310.exists_mul_of_mem_stab h hβα.symm hg
  exact mul_mem (hLn hl) (hTn ht)

theorem relIndex_swap (h : PUHyp M T L) {γ : Vtx (puAmalgam h.le)} {φ : (puAmalgam h.le).Universal}
    (hφ : φ • baseA (puAmalgam h.le) = γ) :
    (Qv _ (φ⁻¹ • baseA (puAmalgam h.le))).relIndex
        (S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ (φ⁻¹ • baseA (puAmalgam h.le)))) =
      (Qv _ (baseA (puAmalgam h.le))).relIndex
        (S5.nclStab _ γ (ZM _ (baseA (puAmalgam h.le)))) ∧
    (Qv _ (baseA (puAmalgam h.le))).relIndex
        (S5.nclStab _ (φ⁻¹ • baseA (puAmalgam h.le)) (ZM _ (baseA (puAmalgam h.le)))) =
      (Qv _ γ).relIndex (S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ γ)) := by
  have hγα : φ⁻¹ • γ = baseA (puAmalgam h.le) := by rw [← hφ, inv_smul_smul]
  have e1 : S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ (φ⁻¹ • baseA (puAmalgam h.le))) =
      (S5.nclStab _ γ (ZM _ (baseA (puAmalgam h.le)))).map (MulAut.conj φ⁻¹).toMonoidHom := by
    rw [← S5B.nclStab_smul, ← zm_smul, hγα]
  have e3 : S5.nclStab _ (φ⁻¹ • baseA (puAmalgam h.le)) (ZM _ (baseA (puAmalgam h.le))) =
      (S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ γ)).map (MulAut.conj φ⁻¹).toMonoidHom := by
    rw [← S5B.nclStab_smul, ← zm_smul, hγα]
  have e4 : Qv _ (baseA (puAmalgam h.le)) = (Qv _ γ).map (MulAut.conj φ⁻¹).toMonoidHom := by
    rw [← qv_smul, hγα]
  constructor
  · rw [e1, qv_smul, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj φ⁻¹).injective]
  · rw [e3, e4, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj φ⁻¹).injective]

variable {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem offender_data (h32 : S32) (h53 : S53) (h : PUHyp M T L) (hmin : PUMin M T L)
    (hd : S5.IsSp4Data M T L k F a) (hb : 2 < critDist (puAmalgam h.le))
    {l : Submodule F (MSP.V4 F)} (hl : MSP.IsLine l)
    (hTl : Qv _ (baseB (puAmalgam h.le)) ≤ S5.vPre h.le a (MSP.qLine l))
    (hv : ⁅Vv _ (baseA (puAmalgam h.le)), Qv _ (baseA (puAmalgam h.le))⁆ ≤
      S5.dSub h.le L (baseA _))
    (hone : S5.OneNoncentral (stab _ (baseA (puAmalgam h.le))) (puTrans h.le L (baseA _))
      (Vv _ (baseA (puAmalgam h.le))) (ZM _ (baseA (puAmalgam h.le))))
    {δ ν : Vtx (puAmalgam h.le)} (hβδ : (puAmalgam h.le).treeGraph.Adj (baseB _) δ)
    (hc : IsCritical _ δ ν) (hmid : geo _ δ ν 2 = baseA (puAmalgam h.le)) :
    S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ δ) ≤ stab _ (baseA (puAmalgam h.le)) ∧
      S5.voSub h.le L (baseA _) ≤
        S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ δ) ⊔ S5.bSub h.le L (baseA _) ∧
      S5.nclStab _ δ (ZM _ (baseA (puAmalgam h.le))) ≤ Qv _ (baseB (puAmalgam h.le)) ∧
      ⁅S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ δ) ⊓ Qv _ δ,
          S5.nclStab _ δ (ZM _ (baseA (puAmalgam h.le)))⁆ ≤ ZM _ (baseA (puAmalgam h.le)) := by
  have hyp := h.hyp20
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hβα := (adj_baseA_baseB (puAmalgam h.le)).symm
  have hδM : IsMVtx _ δ := (isMVtx_iff_of_adj _ hβδ.symm).2 (not_isMVtx_baseB _)
  have hdαδ : (puAmalgam h.le).treeGraph.dist (baseA (puAmalgam h.le)) δ = 2 := by
    have hd : (puAmalgam h.le).treeGraph.dist δ ν = critDist (puAmalgam h.le) := hc.2.1
    rw [← hmid, tdist_comm, dist_geo _ (by omega)]
  have hWV : S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ δ) ≤ Vv _ (baseA (puAmalgam h.le)) :=
    S512N.nclStab_le_vv h hδM hdαδ.le
  have hWst : S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ δ) ≤ stab _ (baseA (puAmalgam h.le)) :=
    hWV.trans ((S310.vv_le_qv_baseA h hb).trans (qv_le_stab _ _))
  have hWB : ¬ S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ δ) ≤ S5.bSub h.le L (baseA _) :=
    fun hle => zm_not_le_bSub h hb hc hmid ((S512R.zm_le_nclStab h δ).trans hle)
  have hEδ : S5.nclStab _ δ (ZM _ (baseA (puAmalgam h.le))) ≤ Qv _ δ :=
    S310.nclStab_le_qv h hα (by rw [tdist_comm]; exact hdαδ) hb
  refine ⟨hWst, voSub_le_sup_bSub h hb hone hWV (S310.stab_le_normalizer_nclStab _ _ _) hWB,
    hEδ.trans (qv_le_qv _ hyp hδM hβδ.symm), ?_⟩
  exact S512R.commutator_inf_qv_nclStab_le h32 h53 h hmin hd hb hl hTl hv hβδ hβα _

theorem exists_offender (h32 : S32) (h53 : S53) (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb4 : critDist (puAmalgam h.le) = 4) (hd : S5.IsSp4Data M T L k F a)
    {l : Submodule F (MSP.V4 F)} (hl : MSP.IsLine l)
    (hTl : Qv _ (baseB (puAmalgam h.le)) ≤ S5.vPre h.le a (MSP.qLine l))
    (hv : ⁅Vv _ (baseA (puAmalgam h.le)), Qv _ (baseA (puAmalgam h.le))⁆ ≤
      S5.dSub h.le L (baseA _))
    (hone : S5.OneNoncentral (stab _ (baseA (puAmalgam h.le))) (puTrans h.le L (baseA _))
      (Vv _ (baseA (puAmalgam h.le))) (ZM _ (baseA (puAmalgam h.le))))
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    (hαβ : geo _ (baseA (puAmalgam h.le)) α' 1 = baseB _)
    {μ : Vtx (puAmalgam h.le)} {y : (puAmalgam h.le).Universal}
    (hy : y ∈ stab _ (baseA (puAmalgam h.le))) (hμy : μ = y • geo _ (baseA (puAmalgam h.le)) α' 2)
    (hcμ : IsCritical _ μ (geo _ (baseA (puAmalgam h.le)) α' 2))
    (hbad : 2 ^ k < (Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2)).relIndex (ZM _ μ)) :
    ∃ (W E : Subgroup (puAmalgam h.le).Universal) (δ : Vtx (puAmalgam h.le)),
      W ≤ stab _ (baseA (puAmalgam h.le)) ∧
      S5.voSub h.le L (baseA _) ≤ W ⊔ S5.bSub h.le L (baseA _) ∧
      E ≤ Qv _ (baseB (puAmalgam h.le)) ∧ ⁅W ⊓ Qv _ δ, E⁆ ≤ ZM _ (baseA (puAmalgam h.le)) ∧
      (Qv _ δ).relIndex W ≤ (Qv _ (baseA (puAmalgam h.le))).relIndex E ∧
      2 ^ k < (Qv _ (baseA (puAmalgam h.le))).relIndex E := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  have := S310.finite_stab_of_isMVtx h (isMVtx_baseA (puAmalgam h.le))
  set γ := geo _ (baseA (puAmalgam h.le)) α' 2 with hγdef
  have hγM : IsMVtx _ γ := isMVtx_geo_two _ hyp hb0 hc
  have hdαγ : (puAmalgam h.le).treeGraph.dist (baseA _) γ = 2 :=
    dist_geo _ (by have := hc.2.1; omega)
  have hβγ : (puAmalgam h.le).treeGraph.Adj (baseB _) γ := by
    rw [← hαβ]
    exact adj_geo _ (by have := hc.2.1; omega)
  have hβα := (adj_baseA_baseB (puAmalgam h.le)).symm
  obtain ⟨hμM, -, -, hd4, -, -, -, -, -, -, -, -⟩ := S512T.pair_facts h hb4 hcμ
  have hdαμ : (puAmalgam h.le).treeGraph.dist (baseA _) μ = 2 := by
    have := dist_smul _ y (baseA (puAmalgam h.le)) γ
    rw [(mem_stab _).1 hy, ← hμy] at this
    rw [this, hdαγ]
  have hmid : geo _ μ γ 2 = baseA (puAmalgam h.le) := by
    symm
    refine eq_geo_of_dist _ (by rw [tdist_comm]; exact hdαμ) ?_
    rw [tdist_comm, hdαμ, hdαγ, hd4]
  have hcγμ : IsCritical _ γ μ := ms22_iii _ hyp hb0 h.centHyp hcμ
  have hmid' : geo _ γ μ 2 = baseA (puAmalgam h.le) := by
    have e : geo _ γ μ 2 = geo _ μ γ 2 := by
      have := geo_symm _ (show 2 ≤ (puAmalgam h.le).treeGraph.dist μ γ by omega)
      rwa [hd4] at this
    rw [e, hmid]
  have hZV : ZM _ μ ≤ S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ γ) := by
    rw [hμy]
    exact S512R.zm_smul_le_nclStab h hy γ
  have hVst : S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ γ) ≤ stab _ (baseA (puAmalgam h.le)) :=
    (S310.nclStab_le_qv h hγM hdαγ hb).trans (qv_le_stab _ _)
  have hlow : 2 ^ k < (Qv _ γ).relIndex (S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ γ)) :=
    hbad.trans_le (Subgroup.relIndex_le_of_le_right hZV (relIndex_ne_zero_of_le hVst))
  by_cases hcase : (Qv _ γ).relIndex (S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ γ)) ≤
      (Qv _ (baseA (puAmalgam h.le))).relIndex (S5.nclStab _ γ (ZM _ (baseA (puAmalgam h.le))))
  · obtain ⟨h1, h2, h3, h4⟩ := offender_data h32 h53 h hmin hd hb hl hTl hv hone hβγ hcγμ hmid'
    exact ⟨_, _, γ, h1, h2, h3, h4, hcase, hlow.trans_le hcase⟩
  · push Not at hcase
    obtain ⟨φ, hφ, hφα⟩ := exists_mem_stab_smul _ hβα hβγ
    have hφβ : φ⁻¹ • baseB (puAmalgam h.le) = baseB _ := (mem_stab _).1 (inv_mem hφ)
    have hβδ : (puAmalgam h.le).treeGraph.Adj (baseB _) (φ⁻¹ • baseA (puAmalgam h.le)) := by
      have := (adj_smul _ φ⁻¹ _ _).2 hβα
      rwa [hφβ] at this
    have hγα : φ⁻¹ • γ = baseA (puAmalgam h.le) := by rw [← hφα, inv_smul_smul]
    have hcδ : IsCritical _ (φ⁻¹ • baseA (puAmalgam h.le)) (φ⁻¹ • α') :=
      (isCritical_smul _ φ⁻¹ _ _).2 hc
    have hmidδ : geo _ (φ⁻¹ • baseA (puAmalgam h.le)) (φ⁻¹ • α') 2 = baseA (puAmalgam h.le) := by
      rw [geo_smul, ← hγdef, hγα]
    obtain ⟨e1, e2⟩ := relIndex_swap h hφα
    obtain ⟨h1, h2, h3, h4⟩ := offender_data h32 h53 h hmin hd hb hl hTl hv hone hβδ hcδ hmidδ
    refine ⟨_, _, φ⁻¹ • baseA (puAmalgam h.le), h1, h2, h3, h4, ?_, ?_⟩
    · rw [e1, e2]
      exact hcase.le
    · rw [e2]
      exact hlow

end S512L

end CFSG.Quasithin.MS93
