module

public import CFSG.Quasithin.MS93.Burnside.Sp4AG2
import CFSG.Quasithin.MS93.S33LamW
public import CFSG.Quasithin.MS93.Burnside.Sp4ALam
public import CFSG.Quasithin.MS93.Burnside.Sp4ATheoD
public import CFSG.Quasithin.MS93.S34F461

public section

namespace CFSG.Quasithin.MS93.S4L

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem burnsideSp4H_map_zstar_le (h : PUHyp M T L) (g : (puAmalgam h.le).Universal)
    (μ : Vtx (puAmalgam h.le)) :
    (burnsideSp4A_zstar h μ).map (MulAut.conj g).toMonoidHom ≤ burnsideSp4A_zstar h (g • μ) := by
  rw [burnsideSp4A_zstar, Subgroup.map_sup]
  refine sup_le ?_ ?_
  · rw [← zm_smul]
    exact le_sup_left
  rw [Subgroup.map_iSup]
  refine iSup_le fun γ => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hγ => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun δ => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hδ => ?_
  rw [← burnsideSp4A_psub_smul]
  exact burnsideSp4A_psub_le_zstar h ((adj_smul (puAmalgam h.le) g μ γ).mpr hγ)
    ((adj_smul (puAmalgam h.le) g γ δ).mpr hδ)

theorem burnsideSp4H_zstar_smul (h : PUHyp M T L) (g : (puAmalgam h.le).Universal)
    (μ : Vtx (puAmalgam h.le)) :
    burnsideSp4A_zstar h (g • μ) = (burnsideSp4A_zstar h μ).map (MulAut.conj g).toMonoidHom := by
  refine le_antisymm ?_ (burnsideSp4H_map_zstar_le h g μ)
  have h1 := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom)
    (burnsideSp4H_map_zstar_le h g⁻¹ (g • μ))
  rw [inv_smul_smul, Subgroup.map_map] at h1
  refine le_trans (le_of_eq ?_) h1
  have : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom = MonoidHom.id _ := by
    refine MonoidHom.ext fun y => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
      MonoidHom.id_apply]
    group
  rw [this, Subgroup.map_id]

theorem burnsideSp4H_zstar_le_centralizer (h : PUHyp M T L) (hU : S34F.IsSp4UEven M T L)
    (hb : 2 < critDist (puAmalgam h.le)) {μ : Vtx (puAmalgam h.le)} (hμ : IsMVtx _ μ) :
    burnsideSp4A_zstar h μ ≤
      Subgroup.centralizer (burnsideSp4A_zstar h μ : Set (puAmalgam h.le).Universal) := by
  have h20 := h.hyp20
  have hb0 : 0 < critDist (puAmalgam h.le) := by omega
  have hb4 : 4 ≤ critDist (puAmalgam h.le) := by
    obtain ⟨m, hm⟩ := h.critDist_even
    omega
  have hnb : ∀ γ, (puAmalgam h.le).treeGraph.Adj μ γ → ∀ δ,
      (puAmalgam h.le).treeGraph.Adj γ δ → IsMVtx _ δ ∧
        (puAmalgam h.le).treeGraph.dist μ δ ≤ 2 := by
    intro γ hγ δ hδ
    refine ⟨?_, ?_⟩
    · have h1 := (isMVtx_iff_of_adj _ hγ).mp hμ
      have h2 := isMVtx_iff_of_adj _ hδ
      tauto
    · have := dist_triangle (puAmalgam h.le) μ γ δ
      rw [dist_eq_one_of_adj _ hγ, dist_eq_one_of_adj _ hδ] at this
      exact this
  have hZμ : ∀ γ, (puAmalgam h.le).treeGraph.Adj μ γ → ∀ δ,
      (puAmalgam h.le).treeGraph.Adj γ δ →
        ZM (puAmalgam h.le) μ ≤ Qv _ γ ⊓ S34F.flat h δ := by
    intro γ hγ δ hδ
    obtain ⟨hδM, hμδ⟩ := hnb γ hγ δ hδ
    refine le_inf (zm_le_qv_of_dist_lt _ hμ (by rw [dist_eq_one_of_adj _ hγ]; omega)) ?_
    exact (zm_le_qv_of_dist_lt _ hμ (by omega)).trans (S43F.qv_le_flat h hδM)
  have hZδ : ∀ γ, (puAmalgam h.le).treeGraph.Adj μ γ → ∀ δ,
      (puAmalgam h.le).treeGraph.Adj γ δ → ∀ γ', (puAmalgam h.le).treeGraph.Adj μ γ' → ∀ δ',
        (puAmalgam h.le).treeGraph.Adj γ' δ' →
          ZM (puAmalgam h.le) δ' ≤ Qv _ γ ⊓ S34F.flat h δ := by
    intro γ hγ δ hδ γ' hγ' δ' hδ'
    obtain ⟨hδM, hμδ⟩ := hnb γ hγ δ hδ
    obtain ⟨hδ'M, hμδ'⟩ := hnb γ' hγ' δ' hδ'
    have hδ'γ : (puAmalgam h.le).treeGraph.dist δ' γ ≤ 3 := by
      have := dist_triangle (puAmalgam h.le) δ' μ γ
      rw [dist_eq_one_of_adj _ hγ, tdist_comm _ δ' μ] at this
      omega
    have hδ'δ : (puAmalgam h.le).treeGraph.dist δ' δ ≤ 4 := by
      have := dist_triangle (puAmalgam h.le) δ' μ δ
      rw [tdist_comm _ δ' μ] at this
      omega
    refine le_inf (zm_le_qv_of_dist_lt _ hδ'M (by omega)) ?_
    by_cases hZ : ZM (puAmalgam h.le) δ' ≤ Qv _ δ
    · exact hZ.trans (S43F.qv_le_flat h hδM)
    · have hd : (puAmalgam h.le).treeGraph.dist δ' δ = critDist (puAmalgam h.le) := by
        by_contra hne
        exact hZ (zm_le_qv_of_dist_lt _ hδ'M (by omega))
      exact zm_le_flat_sp h hU ⟨hδ'M, hd, hZ⟩
  have hPZ : ∀ γ, (puAmalgam h.le).treeGraph.Adj μ γ → ∀ δ,
      (puAmalgam h.le).treeGraph.Adj γ δ →
        burnsideSp4A_psub h γ δ ≤ Subgroup.centralizer (ZM (puAmalgam h.le) μ : Set _) :=
    fun γ hγ δ hδ => inf_le_right.trans (Subgroup.centralizer_le (hZμ γ hγ δ hδ))
  have hPP : ∀ γ, (puAmalgam h.le).treeGraph.Adj μ γ → ∀ δ,
      (puAmalgam h.le).treeGraph.Adj γ δ → ∀ γ', (puAmalgam h.le).treeGraph.Adj μ γ' → ∀ δ',
        (puAmalgam h.le).treeGraph.Adj γ' δ' →
          burnsideSp4A_psub h γ δ ≤ Subgroup.centralizer (burnsideSp4A_psub h γ' δ' : Set _) := by
    intro γ hγ δ hδ γ' hγ' δ' hδ'
    obtain ⟨hδ'M, -⟩ := hnb γ' hγ' δ' hδ'
    refine inf_le_right.trans (Subgroup.centralizer_le ?_)
    exact inf_le_left.trans ((S34F.uloc_le_zm' h hδ'M).trans (hZδ γ hγ δ hδ γ' hγ' δ' hδ'))
  have hZZ : ZM (puAmalgam h.le) μ ≤ Subgroup.centralizer (ZM (puAmalgam h.le) μ : Set _) :=
    (Subgroup.le_centralizer_iff_isMulCommutative).mpr (isElemAbelian_zm _ h20 hb0 hμ).1
  have hgenZ : burnsideSp4A_zstar h μ ≤
      Subgroup.centralizer (ZM (puAmalgam h.le) μ : Set _) :=
    sup_le hZZ (iSup₂_le fun γ hγ => iSup₂_le fun δ hδ => hPZ γ hγ δ hδ)
  have hgenP : ∀ γ', (puAmalgam h.le).treeGraph.Adj μ γ' → ∀ δ',
      (puAmalgam h.le).treeGraph.Adj γ' δ' → burnsideSp4A_zstar h μ ≤
        Subgroup.centralizer (burnsideSp4A_psub h γ' δ' : Set _) := by
    intro γ' hγ' δ' hδ'
    refine sup_le ?_ (iSup₂_le fun γ hγ => iSup₂_le fun δ hδ => hPP γ hγ δ hδ γ' hγ' δ' hδ')
    rw [Subgroup.le_centralizer_iff]
    exact hPZ γ' hγ' δ' hδ'
  refine sup_le ?_ (iSup₂_le fun γ hγ => iSup₂_le fun δ hδ => ?_)
  · rw [Subgroup.le_centralizer_iff]
    exact hgenZ
  · rw [Subgroup.le_centralizer_iff]
    exact hgenP γ hγ δ hδ

theorem burnsideSp4H_zstar_comm (h : PUHyp M T L) (hU : S34F.IsSp4UEven M T L)
    (hb : 2 < critDist (puAmalgam h.le)) {μ : Vtx (puAmalgam h.le)} (hμ : IsMVtx _ μ) :
    ∀ x ∈ burnsideSp4A_zstar h μ, ∀ y ∈ burnsideSp4A_zstar h μ, x * y = y * x :=
  fun x hx _ hy =>
    Subgroup.mem_centralizer_iff.mp (burnsideSp4H_zstar_le_centralizer h hU hb hμ hy) x hx

theorem burnsideSp4H_zstar_le_qv (h : PUHyp M T L) (hU : S34F.IsSp4UEven M T L)
    (hb : 2 < critDist (puAmalgam h.le)) {μ ν : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) μ ν) :
    burnsideSp4A_zstar h μ ≤ Qv (puAmalgam h.le) (geo _ ν μ 2) := by
  have h20 := h.hyp20
  have hb0 : 0 < critDist (puAmalgam h.le) := by omega
  set ε := geo (puAmalgam h.le) ν μ 2 with hε
  have hd : (puAmalgam h.le).treeGraph.dist ν μ = critDist (puAmalgam h.le) := by
    rw [tdist_comm]
    exact hc.2.1
  have hεμ : (puAmalgam h.le).treeGraph.dist ε μ = critDist (puAmalgam h.le) - 2 := by
    rw [hε, dist_geo_right _ (by omega), hd]
  have hνM : IsMVtx _ ν := hc.isMVtx_right _ h20
  have hεM : IsMVtx _ ε := by
    rw [hε, isMVtx_geo _ (by omega)]
    exact ⟨fun _ => even_two, fun _ => hνM⟩
  refine sup_le (zm_le_qv_of_dist_lt _ hc.1 (by rw [tdist_comm, hεμ]; omega)) ?_
  refine iSup₂_le fun γ hγ => iSup₂_le fun δ hδ => ?_
  have hμγ : (puAmalgam h.le).treeGraph.Adj μ γ := hγ
  have hγδ : (puAmalgam h.le).treeGraph.Adj γ δ := hδ
  have hδM : IsMVtx _ δ := by
    have h1 := (isMVtx_iff_of_adj _ hμγ).mp hc.1
    have h2 := isMVtx_iff_of_adj _ hγδ
    tauto
  have hεγ : (puAmalgam h.le).treeGraph.dist ε γ ≤ critDist (puAmalgam h.le) - 1 := by
    have := dist_triangle (puAmalgam h.le) ε μ γ
    rw [hεμ, dist_eq_one_of_adj _ hμγ] at this
    omega
  have hδε : (puAmalgam h.le).treeGraph.dist δ ε ≤ critDist (puAmalgam h.le) := by
    have := dist_triangle (puAmalgam h.le) δ γ ε
    rw [tdist_comm _ δ γ, dist_eq_one_of_adj _ hγδ, tdist_comm _ γ ε] at this
    omega
  by_cases hZ : ZM (puAmalgam h.le) δ ≤ Qv _ ε
  · exact inf_le_left.trans ((S34F.uloc_le_zm' h hδM).trans hZ)
  · have hdδε : (puAmalgam h.le).treeGraph.dist δ ε = critDist (puAmalgam h.le) := by
      by_contra hne
      exact hZ (zm_le_qv_of_dist_lt _ hδM (by omega))
    have hcε := ms22_iii _ h20 hb0 h.centHyp (show IsCritical (puAmalgam h.le) δ ε from
      ⟨hδM, hdδε, hZ⟩)
    have hεδ : (puAmalgam h.le).treeGraph.dist ε δ = critDist (puAmalgam h.le) := by
      rw [tdist_comm]
      exact hdδε
    have hερ : (puAmalgam h.le).treeGraph.Adj ε (geo _ ε δ 1) := adj_geo_one _ (by omega)
    have hδρ : ZM (puAmalgam h.le) δ ≤ Qv _ (geo _ ε δ 1) := by
      refine zm_le_qv_of_dist_lt _ hδM ?_
      rw [tdist_comm, dist_geo_right _ (by omega), hεδ]
      omega
    have hZε : ZM (puAmalgam h.le) ε ≤ Qv _ γ ⊓ S34F.flat h δ :=
      le_inf (zm_le_qv_of_dist_lt _ hεM (by omega)) (zm_le_flat_sp h hU hcε)
    rw [← S33.qv_inf_centralizer_puTrans h hεM hερ]
    refine le_inf (inf_le_left.trans ((S34F.uloc_le_zm' h hδM).trans hδρ)) ?_
    exact inf_le_right.trans (Subgroup.centralizer_le ((S34F.uloc_le_zm' h hεM).trans hZε))

theorem burnsideSp4H_zstar_le_qv_baseB (h : PUHyp M T L) (hU : S34F.IsSp4UEven M T L)
    (hb : 2 < critDist (puAmalgam h.le)) {μ : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) μ (baseA _))
    (hμβ : geo (puAmalgam h.le) (baseA _) μ 1 = baseB _) :
    burnsideSp4A_zstar h μ ≤ Qv (puAmalgam h.le) (baseB _) := by
  have h20 := h.hyp20
  have hd : (puAmalgam h.le).treeGraph.dist (baseA _) μ = critDist (puAmalgam h.le) := by
    rw [tdist_comm]
    exact hc.2.1
  have hεM : IsMVtx _ (geo (puAmalgam h.le) (baseA _) μ 2) := by
    rw [isMVtx_geo _ (by omega)]
    exact ⟨fun _ => even_two, fun _ => PU.isMVtx_baseA _⟩
  have hadj : (puAmalgam h.le).treeGraph.Adj (geo (puAmalgam h.le) (baseA _) μ 1)
      (geo (puAmalgam h.le) (baseA _) μ 2) := adj_geo _ (i := 1) (by omega)
  refine (burnsideSp4H_zstar_le_qv h hU hb hc).trans ?_
  rw [← hμβ]
  exact qv_le_qv _ h20 hεM hadj.symm

theorem burnsideSp4H_critR_le_zstar (h : PUHyp M T L) {μ α : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) μ α) :
    critR (puAmalgam h.le) μ α ≤ burnsideSp4A_zstar h μ := by
  refine le_trans ?_ (le_sup_left : ZM (puAmalgam h.le) μ ≤ burnsideSp4A_zstar h μ)
  exact Subgroup.le_normalizer_iff_commutator_le_left.mp
    ((zm_le_stab_of_isCritical _ h.hyp20 h.critDist_pos hc).trans (stab_le_normalizer_zm _ μ))

theorem burnsideSp4H_zstar_le_flat (h : PUHyp M T L) (hU : S34F.IsSp4UEven M T L)
    (hb : 2 < critDist (puAmalgam h.le)) {μ : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) μ (baseA _))
    (hμβ : geo (puAmalgam h.le) (baseA _) μ 1 = baseB _) :
    burnsideSp4A_zstar h μ ≤ S34F.flat h (baseA _) := by
  refine (le_inf (burnsideSp4H_zstar_le_qv_baseB h hU hb hc hμβ) ?_).trans
    (qv_inf_centralizer_critR_le_flat_base_sp h hU hc hμβ)
  exact (burnsideSp4H_zstar_le_centralizer h hU hb hc.1).trans
    (Subgroup.centralizer_le (burnsideSp4H_critR_le_zstar h hc))

theorem burnsideSp4H_pre_zstar (h : PUHyp M T L) (hU : S34F.IsSp4UEven M T L)
    (hb : 2 < critDist (puAmalgam h.le)) {μ : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) μ (baseA _))
    (hμβ : geo (puAmalgam h.le) (baseA _) μ 1 = baseB _) :
    S33.pre h.le (burnsideSp4A_zstar h μ) ≤ L ⊔ pCoreOf 2 M ∧
    (∀ x ∈ S33.pre h.le (burnsideSp4A_zstar h μ),
      ∀ y ∈ S33.pre h.le (burnsideSp4A_zstar h μ), x * y = y * x) ∧
    ⁅Uq M T L, S33.pre h.le (burnsideSp4A_zstar h μ)⁆ ≤ S33.pre h.le (burnsideSp4A_zstar h μ) ∧
    S33.pre h.le (ZM _ μ) ≤ S33.pre h.le (burnsideSp4A_zstar h μ) ∧
    imM h.le (S33.pre h.le (burnsideSp4A_zstar h μ)) = burnsideSp4A_zstar h μ := by
  have hb0 : 0 < critDist (puAmalgam h.le) := by omega
  have hKM : L ⊔ pCoreOf 2 M ≤ M := sup_le h.L_le (pCoreOf_le' M)
  have hUM : Uq M T L ≤ M := Uq_le h.L_le
  have hZK : burnsideSp4A_zstar h μ ≤ imM h.le (L ⊔ pCoreOf 2 M) := by
    have := burnsideSp4H_zstar_le_flat h hU hb hc hμβ
    rwa [S34F.flat, puTrans_baseA h.le (S34F.flat_subgroupOf_normal h)] at this
  have hWim : imM h.le (S33.pre h.le (burnsideSp4A_zstar h μ)) = burnsideSp4A_zstar h μ :=
    S33.imM_pre h.le (hZK.trans (imM_mono h.le hKM))
  refine ⟨S33.pre_le_of_le_imM h hZK, S33.pre_comm h.le (burnsideSp4H_zstar_comm h hU hb hc.1),
    ?_, ?_, hWim⟩
  · rw [← imM_le_imM_iff h.le (commutator_le_of_le hUM (S33.pre_le h.le _)),
      S33.imM_commutator h.le hUM (S33.pre_le h.le _), hWim]
    refine (Subgroup.commutator_mono (imM_mono h.le (Uq_le_Z0q h.L_le)) le_rfl).trans ?_
    rw [← puAmalgam.zm_baseA, Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((zm_le_stab_of_isCritical _ h.hyp20 hb0 hc).trans
        (burnsideSp4A_stab_le_normalizer_zstar h μ))
  · intro x hx
    obtain ⟨m, hm, rfl⟩ := (S33.mem_pre_iff' h.le).1 hx
    exact (S33.mem_pre_iff' h.le).2 ⟨m, (le_sup_left : ZM _ μ ≤ burnsideSp4A_zstar h μ) hm, rfl⟩

theorem burnsideSp4H_comm_zstar_le_of_commSp_le (h : PUHyp M T L)
    (hU : S34F.IsSp4UEven M T L) (hb : 2 < critDist (puAmalgam h.le)) {μ : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) μ (baseA _))
    (hμβ : geo (puAmalgam h.le) (baseA _) μ 1 = baseB _)
    {k : ℕ} {F : Type} [Field F] [Fintype F] [CharP F 2] (hcard : Fintype.card F = 2 ^ k)
    (hk : 2 ≤ k) {φ : ↥(L ⊔ pCoreOf 2 M) →* ↥(StatedSp 2 F)} (hφs : Function.Surjective φ)
    (hφ : IsSumOfNaturalModulesVia (L ⊔ pCoreOf 2 M) (Uq M T L)
      (Uq M T L ⊓ Subgroup.centralizer (L : Set G)) φ false 1)
    (hle : MSP.commSp
        (((S33.pre h.le (burnsideSp4A_zstar h μ)).subgroupOf (L ⊔ pCoreOf 2 M)).map φ) ≤
      MSP.commSp (((S33.pre h.le (ZM _ μ)).subgroupOf (L ⊔ pCoreOf 2 M)).map φ)) :
    ⁅burnsideSp4A_zstar h μ, ZM _ (baseA _)⁆ ≤ ZM _ μ := by
  have hKM : L ⊔ pCoreOf 2 M ≤ M := sup_le h.L_le (pCoreOf_le' M)
  have hUM : Uq M T L ≤ M := Uq_le h.L_le
  have hμK := pre_zm_le_flat_sp h hU hc hμβ
  obtain ⟨hWK, -, -, -, hWim⟩ := burnsideSp4H_pre_zstar h hU hb hc hμβ
  obtain ⟨-, -, hUE, -, hEim⟩ := S33.pre_zm_props h hc
  have hφ' : IsSumOfNaturalModulesVia (L ⊔ pCoreOf 2 M) (Uq M T L) (Uq M T L ⊓ Zq M L) φ
      false 1 := by
    rw [h.Uq_inf_Zq]
    exact hφ
  obtain ⟨-, -, β, hβ, hβker, hβα⟩ := hφ'
  have hAβ := S33.isCoordAct_of_natSp hβα
  have hD := burnsideSp4A_uq_inf_le_comm h hcard hk hφs hφ hc hμK
  have hUWE := burnsideSp4A_lam_commutator_le_of_commSp_le h hKM hβ hβker hAβ hWK hμK hD hle
  have hUloc : Uloc h.le L (baseA _) = imM h.le (Uq M T L) :=
    puTrans_baseA h.le (S4A.Uq_normal h)
  have hUN : ⁅Uloc h.le L (baseA _), burnsideSp4A_zstar h μ⁆ ≤ ZM _ μ := by
    have e1 : ⁅Uloc h.le L (baseA _), burnsideSp4A_zstar h μ⁆ =
        imM h.le ⁅Uq M T L, S33.pre h.le (burnsideSp4A_zstar h μ)⁆ := by
      rw [hUloc, S33.imM_commutator h.le hUM (S33.pre_le h.le _), hWim]
    rw [e1, ← hEim]
    exact imM_mono h.le (hUWE.trans hUE)
  rw [Subgroup.commutator_comm,
    S34F.commutator_zm_eq_commutator_uloc_of_le_qv h (PU.isMVtx_baseA _) (adj_baseA_baseB _)
      (burnsideSp4H_zstar_le_qv_baseB h hU hb hc hμβ)]
  exact hUN

end CFSG.Quasithin.MS93.S4L
