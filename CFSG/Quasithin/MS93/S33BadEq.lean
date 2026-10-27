module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.MS93.S33LamW
public import CFSG.Quasithin.MS93.S38PU

public section

namespace CFSG.Quasithin.MS93.S33

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

section Amalgam

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B)

@[expose] def OffEqAt (γ ρ : Vtx X) : Prop :=
  ∀ F : Subgroup X.Universal, IsOffAt X γ ρ F →
    (Subgroup.centralizer (F : Set X.Universal)).relIndex (XM X γ) = (Qv X γ).relIndex F

variable {X}

theorem OffEqAt.smul {γ ρ : Vtx X} (hO : OffEqAt X γ ρ) (g : X.Universal) :
    OffEqAt X (g • γ) (g • ρ) := by
  have back : ∀ K : Subgroup X.Universal,
      (K.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = K := fun K => by
    rw [map_conj_map_conj, mul_inv_cancel, map_conj_one]
  intro F hF
  have h := hO _ ((isOffAt_smul_iff X g).mp hF)
  rw [← back F, ← centralizer_map_mulEquiv, xm_smul, qv_smul,
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective,
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
  exact h

theorem offEqAt_of_edge {α β : Vtx X} (hα : IsMVtx X α) (hαβ : X.treeGraph.Adj α β)
    (hO : OffEqAt X α β) {γ ρ : Vtx X} (hγ : IsMVtx X γ) (hγρ : X.treeGraph.Adj γ ρ) :
    OffEqAt X γ ρ := by
  obtain ⟨g, rfl, rfl⟩ := exists_smul_edge_of_isMVtx X hα hαβ hγ hγρ
  exact hO.smul g

private theorem relIndex_ne_zero_of_le'' {H K P : Subgroup X.Universal} (hKP : K ≤ P)
    [Finite P] : H.relIndex K ≠ 0 := by
  have : Finite K := Finite.of_injective _ (Subgroup.inclusion_injective hKP)
  exact Subgroup.index_ne_zero_of_finite

private theorem relIndex_centralizer_le'' {Q V E P : Subgroup X.Universal} (hEP : E ≤ P)
    [Finite P] (hQV : Q ≤ Subgroup.centralizer (V : Set X.Universal)) :
    (Subgroup.centralizer (V : Set X.Universal)).relIndex E ≤ Q.relIndex E := by
  rw [← Subgroup.inf_relIndex_right, ← Subgroup.inf_relIndex_right (H := Q)]
  exact Subgroup.relIndex_le_of_le_left (inf_le_inf_right _ hQV)
    (relIndex_ne_zero_of_le'' hEP)

variable (h : Hyp20 X) (hb : 0 < critDist X) (hC : CentHyp X)
include h hb hC

theorem isOffAt_xm_of_eq {α α' : Vtx X} (hc : IsCritical X α α')
    (hO : OffEqAt X α (geo X α α' 1)) (hO' : OffEqAt X α' (geo X α' α 1)) :
    IsOffAt X α (geo X α α' 1) (XM X α') ∧ IsOffAt X α' (geo X α' α 1) (XM X α) := by
  have hc' := ms22_iii X h hb hC hc
  have hα := hc.1
  have hα' := hc.isMVtx_right X h
  have hαβ : X.treeGraph.Adj α (geo X α α' 1) := adj_geo_one_of_isCritical X hb hc
  have hα'γ : X.treeGraph.Adj α' (geo X α' α 1) := adj_geo_one_of_isCritical X hb hc'
  have : Finite (Qv X (geo X α α' 1)) := finite_qv X h ((isMVtx_iff_of_adj X hαβ).mp hα)
  have : Finite (Qv X (geo X α' α 1)) := finite_qv X h ((isMVtx_iff_of_adj X hα'γ).mp hα')
  have hXβ : XM X α' ≤ Qv X (geo X α α' 1) := xm_le_qv_geo_one X h hb hC hc
  have hXγ : XM X α ≤ Qv X (geo X α' α 1) := xm_le_qv_geo_one X h hb hC hc'
  have hn : ¬ XM X α' ≤ Qv X α := xm_not_le_qv_of_isCritical h hb hC hc
  have hn' : ¬ XM X α ≤ Qv X α' := xm_not_le_qv_of_isCritical h hb hC hc'
  have hca : (Subgroup.centralizer (XM X α' : Set X.Universal)).relIndex (XM X α) ≤
      (Qv X α').relIndex (XM X α) := relIndex_centralizer_le'' hXγ (qv_le_centralizer_xm X α')
  have hca' : (Subgroup.centralizer (XM X α : Set X.Universal)).relIndex (XM X α') ≤
      (Qv X α).relIndex (XM X α') := relIndex_centralizer_le'' hXβ (qv_le_centralizer_xm X α)
  rcases le_or_gt ((Qv X α').relIndex (XM X α)) ((Qv X α).relIndex (XM X α')) with hle | hlt
  · have h1 : IsOffAt X α (geo X α α' 1) (XM X α') :=
      ⟨hXβ, isElemAbelian_xm X α', hn, hca.trans hle⟩
    have he := hO _ h1
    refine ⟨h1, hXγ, isElemAbelian_xm X α, hn', ?_⟩
    omega
  · exfalso
    have h1 : IsOffAt X α' (geo X α' α 1) (XM X α) :=
      ⟨hXγ, isElemAbelian_xm X α, hn', hca'.trans hlt.le⟩
    have he := hO' _ h1
    omega

end Amalgam

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem offEqAt_base (h : PUHyp M T L)
    (hEq : ∀ F : Subgroup G, IsXOff M T F →
      (Subgroup.centralizer (F : Set G)).relIndex (Xq M) = (pCoreOf 2 M).relIndex F) :
    OffEqAt (puAmalgam h.le) (baseA _) (baseB _) := by
  have hQ : Qv (puAmalgam h.le) (baseA _) = imM h.le (pCoreOf 2 M) :=
    puAmalgam.qv_baseA_eq_pCoreOf h.le h.isPGroup h.pCore_le
  intro F' hF'
  have hF'T : F' ≤ imM h.le T := by
    have := hF'.1
    rwa [puAmalgam.qv_baseB] at this
  obtain ⟨F, hFT, rfl⟩ := exists_imM_eq_of_le h.le hF'T
  have hF := (h.isOffAt_base_iff hFT).mp hF'
  rw [h.xm_baseA_eq, hQ, relIndex_centralizer_imM_eq h.le (Xq_le M) (hFT.trans h.le),
    imM_relIndex' h.le _ (hFT.trans h.le)]
  exact hEq F hF

theorem offEqAt_pu (h : PUHyp M T L)
    (hEq : ∀ F : Subgroup G, IsXOff M T F →
      (Subgroup.centralizer (F : Set G)).relIndex (Xq M) = (pCoreOf 2 M).relIndex F)
    {γ ρ : Vtx (puAmalgam h.le)} (hγ : IsMVtx _ γ)
    (hγρ : (puAmalgam h.le).treeGraph.Adj γ ρ) : OffEqAt (puAmalgam h.le) γ ρ :=
  offEqAt_of_edge (PU.isMVtx_baseA _) (adj_baseA_baseB _) (offEqAt_base h hEq) hγ hγρ

theorem commutator_le_of_offEq (h : PUHyp M T L)
    (hEq : ∀ F : Subgroup G, IsXOff M T F →
      (Subgroup.centralizer (F : Set G)).relIndex (Xq M) = (pCoreOf 2 M).relIndex F)
    (hC : ∀ F : Subgroup G, IsXOff M T F → ∀ E : Subgroup G, E ≤ F → ¬ E ≤ pCoreOf 2 M →
      ∀ y ∈ T, y ∈ Subgroup.centralizer (F : Set G) →
        y ∈ Subgroup.centralizer ((⁅Uq M T L, E⁆ : Subgroup G) : Set G) →
          y ∈ F ⊔ pCoreOf 2 M)
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) (baseA _) α')
    {Y : Subgroup (puAmalgam h.le).Universal} (hY : Y ≤ Qv _ (geo _ α' (baseA _) 1))
    (hYR : Y ≤ Subgroup.centralizer (critR _ (baseA _) α' : Set (puAmalgam h.le).Universal))
    (hYX : Y ≤ Subgroup.centralizer (XM (puAmalgam h.le) (baseA _) :
      Set (puAmalgam h.le).Universal)) :
    ⁅ZM (puAmalgam h.le) α', Y⁆ ≤ ⁅XM (puAmalgam h.le) (baseA _), XM (puAmalgam h.le) α'⁆ := by
  have h20 := h.hyp20
  have hb := h.critDist_pos
  have hCH := h.centHyp
  obtain ⟨g, hgα, hgβ, hμ, hgeo⟩ := exists_conj_of_isCritical _ h20 hb hc
  have hgμ : g • (g⁻¹ • baseA (puAmalgam h.le)) = baseA (puAmalgam h.le) := smul_inv_smul g _
  have hμ' := ms22_iii _ h20 hb hCH hμ
  have hYY' : Y = (Y.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.map_map]
    conv_lhs => rw [← Subgroup.map_id Y]
    congr 1
    ext x
    simp
  have hY'T : Y.map (MulAut.conj g⁻¹).toMonoidHom ≤ imM h.le T := by
    intro y hy
    have hy' : (MulAut.conj g).toMonoidHom y ∈ Qv _ (geo _ α' (baseA (puAmalgam h.le)) 1) := by
      rw [hYY'] at hY
      exact hY ⟨y, hy, rfl⟩
    rw [← hgβ, qv_smul, puAmalgam.qv_baseB] at hy'
    exact (Subgroup.mem_map_iff_mem (MulAut.conj g).injective).1 hy'
  have hYqT : pre h.le (Y.map (MulAut.conj g⁻¹).toMonoidHom) ≤ T := pre_le_of_le_imM h hY'T
  have hY'im : imM h.le (pre h.le (Y.map (MulAut.conj g⁻¹).toMonoidHom)) =
      Y.map (MulAut.conj g⁻¹).toMonoidHom :=
    imM_pre h.le (hY'T.trans (imM_mono h.le h.le))
  have hET : pre h.le (ZM _ (g⁻¹ • baseA (puAmalgam h.le))) ≤ T :=
    pre_le_of_le_imM h (zm_le_imM_T h hμ hgeo)
  have hXμT : XM (puAmalgam h.le) (g⁻¹ • baseA _) ≤ imM h.le T := by
    have := xm_le_qv_geo_one _ h20 hb hCH hμ'
    rwa [hgeo, puAmalgam.qv_baseB] at this
  have hFT : pre h.le (XM (puAmalgam h.le) (g⁻¹ • baseA _)) ≤ T := pre_le_of_le_imM h hXμT
  have hFim : imM h.le (pre h.le (XM (puAmalgam h.le) (g⁻¹ • baseA _))) =
      XM (puAmalgam h.le) (g⁻¹ • baseA _) :=
    imM_pre h.le (hXμT.trans (imM_mono h.le h.le))
  obtain ⟨-, -, -, -, hEim⟩ := pre_zm_props h hμ
  have hEF : pre h.le (ZM _ (g⁻¹ • baseA (puAmalgam h.le))) ≤
      pre h.le (XM (puAmalgam h.le) (g⁻¹ • baseA _)) :=
    Subgroup.map_mono (Subgroup.comap_mono (zm_le_xm _ h20 hb hμ.1))
  have hEQ : ¬ pre h.le (ZM _ (g⁻¹ • baseA (puAmalgam h.le))) ≤ pCoreOf 2 M := by
    intro hle
    apply hμ.2.2
    rw [← hEim, puAmalgam.qv_baseA_eq_pCoreOf h.le h.isPGroup h.pCore_le]
    exact imM_mono h.le hle
  have hO := offEqAt_pu h hEq (PU.isMVtx_baseA _) (adj_geo_one_of_isCritical _ hb hμ')
  have hO' := offEqAt_pu h hEq hμ.1 (adj_geo_one_of_isCritical _ hb hμ)
  have hoff := (isOffAt_xm_of_eq h20 hb hCH hμ' hO hO').1
  rw [hgeo, ← hFim] at hoff
  have hFoff : IsXOff M T (pre h.le (XM (puAmalgam h.le) (g⁻¹ • baseA _))) :=
    (h.isOffAt_base_iff hFT).1 hoff
  have hYqF : pre h.le (Y.map (MulAut.conj g⁻¹).toMonoidHom) ≤
      Subgroup.centralizer (pre h.le (XM (puAmalgam h.le) (g⁻¹ • baseA _)) : Set G) := by
    refine pre_le_centralizer h.le (hFT.trans h.le) ?_
    rw [hFim]
    intro y hy
    have hy' : (MulAut.conj g).toMonoidHom y ∈
        Subgroup.centralizer (XM (puAmalgam h.le) (baseA _) : Set _) := by
      rw [hYY'] at hYX
      exact hYX ⟨y, hy, rfl⟩
    rw [← hgμ, xm_smul, PU.centralizer_map_mulEquiv] at hy'
    exact (Subgroup.mem_map_iff_mem (MulAut.conj g).injective).1 hy'
  have hcomm := imM_commutator_pre h hμ hET
  have hR : critR (puAmalgam h.le) (baseA _) α' =
      (critR (puAmalgam h.le) (g⁻¹ • baseA _) (baseA _)).map (MulAut.conj g).toMonoidHom := by
    rw [critR, critR, Subgroup.map_commutator, ← zm_smul, ← zm_smul, hgμ, hgα]
  have hYqR : pre h.le (Y.map (MulAut.conj g⁻¹).toMonoidHom) ≤ Subgroup.centralizer
      ((⁅Uq M T L, pre h.le (ZM _ (g⁻¹ • baseA (puAmalgam h.le)))⁆ : Subgroup G) : Set G) := by
    refine pre_le_centralizer h.le ((commutator_le_left_of_le_normalizer
      ((pre_le h.le _).trans (le_normalizer_Uq h.le_normalizer))).trans
        ((Uq_le_Z0q h.L_le).trans (Z0q_le M T))) ?_
    rw [hcomm]
    intro y hy
    have hy' : (MulAut.conj g).toMonoidHom y ∈
        Subgroup.centralizer (critR (puAmalgam h.le) (baseA _) α' : Set _) := by
      rw [hYY'] at hYR
      exact hYR ⟨y, hy, rfl⟩
    rw [hR, PU.centralizer_map_mulEquiv] at hy'
    exact (Subgroup.mem_map_iff_mem (MulAut.conj g).injective).1 hy'
  have hYqle : pre h.le (Y.map (MulAut.conj g⁻¹).toMonoidHom) ≤
      pre h.le (XM (puAmalgam h.le) (g⁻¹ • baseA _)) ⊔ pCoreOf 2 M := fun y hy =>
    hC _ hFoff _ hEF hEQ y (hYqT hy) (hYqF hy) (hYqR hy)
  have hFn : pre h.le (XM (puAmalgam h.le) (g⁻¹ • baseA _)) ≤
      Subgroup.normalizer (Xq M : Set G) := hFT.trans (h.le.trans (le_normalizer_Xq M))
  have hQ : pCoreOf 2 M ≤ Subgroup.centralizer (Xq M : Set G) := by
    rw [← Subgroup.le_centralizer_iff]
    exact (PU.omegaOneCenterOf_le_centerOf _).trans inf_le_right
  have h1 : ⁅Z0q M T, pre h.le (Y.map (MulAut.conj g⁻¹).toMonoidHom)⁆ ≤
      ⁅Xq M, pre h.le (XM (puAmalgam h.le) (g⁻¹ • baseA _))⁆ :=
    calc ⁅Z0q M T, pre h.le (Y.map (MulAut.conj g⁻¹).toMonoidHom)⁆
        ≤ ⁅Xq M, pre h.le (XM (puAmalgam h.le) (g⁻¹ • baseA _)) ⊔ pCoreOf 2 M⁆ :=
          Subgroup.commutator_mono h.Z0q_le_Xq hYqle
      _ = ⁅Xq M, pre h.le (XM (puAmalgam h.le) (g⁻¹ • baseA _))⁆ :=
          commutator_sup_eq_of_le_centralizer hFn hQ
  have hZ : ZM (puAmalgam h.le) (baseA _) = imM h.le (Z0q M T) := puAmalgam.zm_baseA h.le
  have h2 : ⁅ZM (puAmalgam h.le) (baseA _), Y.map (MulAut.conj g⁻¹).toMonoidHom⁆ ≤
      ⁅XM (puAmalgam h.le) (baseA _), XM (puAmalgam h.le) (g⁻¹ • baseA _)⁆ := by
    rw [hZ, ← hY'im, ← imM_commutator h.le (Z0q_le M T) (pre_le h.le _), h.xm_baseA_eq, ← hFim,
      ← imM_commutator h.le (Xq_le M) (hFT.trans h.le)]
    exact imM_mono h.le h1
  have h3 : ⁅ZM (puAmalgam h.le) α', Y⁆ =
      ⁅ZM (puAmalgam h.le) (baseA _), Y.map (MulAut.conj g⁻¹).toMonoidHom⁆.map
        (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.map_commutator, ← hYY', ← zm_smul, hgα]
  have h4 : ⁅XM (puAmalgam h.le) (baseA _), XM (puAmalgam h.le) (g⁻¹ • baseA _)⁆.map
      (MulAut.conj g).toMonoidHom =
        ⁅XM (puAmalgam h.le) α', XM (puAmalgam h.le) (baseA _)⁆ := by
    rw [Subgroup.map_commutator, ← xm_smul, ← xm_smul, hgα, hgμ]
  rw [h3]
  refine (Subgroup.map_mono h2).trans ?_
  rw [h4, Subgroup.commutator_comm]

end CFSG.Quasithin.MS93.S33
