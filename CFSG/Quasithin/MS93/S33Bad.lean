module

public import CFSG.Quasithin.MS93.S33LamW
public import CFSG.Quasithin.MS93.S38OffDbl

public section

namespace CFSG.Quasithin.MS93.S33

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem commutator_le_of_offData (h : PUHyp M T L) (hD : XOffData M T)
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
  have hO := h.offDataAt hD (PU.isMVtx_baseA _) (adj_geo_one_of_isCritical _ hb hμ')
  have hO' := h.offDataAt hD hμ.1 (adj_geo_one_of_isCritical _ hb hμ)
  have hoff := (isOffAt_xm h20 hb hCH hμ' hO hO').1
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

theorem xOffData_of_isDoubleSL3U' (h : PUHyp M T L) (hX : IsDoubleSL3U M T L) :
    XOffData M T := by
  obtain ⟨-, -, n, K, _, _, α, hK, hα, hnat⟩ := hX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_of_card_eq_prime_pow hK
  obtain ⟨β, hβ⟩ := S38D.exists_isDblCoord hnat
  refine XOffData.of_cent h h.centralizer_Z0q (fun F₁ F₂ h₁ h₂ => ?_) (fun F hF => ?_)
    (fun F hF y hy hyC => S38D.mem_sup_of_mem_centralizer h hβ hα hF hy hyC)
  · exact le_antisymm (sup_le (S38D.le_sup_of_isXOff h hβ hα h₂ h₁) le_sup_right)
      (sup_le (S38D.le_sup_of_isXOff h hβ hα h₁ h₂) le_sup_right)
  · exact (S38D.offImg_of_isXOff h hβ hα hF).1

theorem not_hyp_of_cent (h : PUHyp M T L) (hD : XOffData M T)
    (hC : ∀ F : Subgroup G, IsXOff M T F → T ⊓ Subgroup.centralizer (F : Set G) ≤
      F ⊔ pCoreOf 2 M)
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) (baseA _) α')
    {Y : Subgroup (puAmalgam h.le).Universal} (hY : Y ≤ Qv _ (geo _ α' (baseA _) 1))
    (hYR : Y ≤ Subgroup.centralizer (critR _ (baseA _) α' : Set (puAmalgam h.le).Universal))
    (hYX : Y ≤ Subgroup.centralizer (XM (puAmalgam h.le) (baseA _) :
      Set (puAmalgam h.le).Universal))
    (hn : ¬ ⁅ZM (puAmalgam h.le) α', Y⁆ ≤
      ⁅XM (puAmalgam h.le) (baseA _), XM (puAmalgam h.le) α'⁆ ⊔
        ⁅critA (puAmalgam h.le) (baseA _) α', Y⁆) : False :=
  hn ((commutator_le_of_offData h hD (fun F hF _ _ _ _y hyT hyF _ => hC F hF ⟨hyT, hyF⟩) hc hY
    hYR hYX).trans le_sup_left)

end CFSG.Quasithin.MS93.S33
