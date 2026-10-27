module

public import CFSG.Quasithin.Background.RonanE628RLocal
public import CFSG.Quasithin.Background.RonanE628RBlock
public import CFSG.Quasithin.Background.GoldschmidtE23FourL2
public import CFSG.Quasithin.Vol2.Ch3n317
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellBlockCentrality
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3TabBlock
public import CFSG.Quasithin.Background.C126A5Extract
public import CFSG.Quasithin.Background.C126A5Lift10
public import CFSG.Quasithin.Background.C126RadFree
public import CFSG.Quasithin.Background.GoldschmidtE23FourBlk
public import CFSG.Quasithin.Background.RonanE628

public section

namespace CFSG.Quasithin.RonanE628

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.E6
open Equiv
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem conjClosure_eq_iSup (T L : Subgroup G) :
    conjClosure L T = ⨆ i : ↥(conjSubgroupsBy T L), (i : Subgroup G) := by
  apply le_antisymm
  · refine conjClosure_le fun t ht z hz => ?_
    have hmem : L.map (MulAut.conj t).toMonoidHom ∈ conjSubgroupsBy T L := ⟨t, ht, rfl⟩
    exact le_iSup (fun i : ↥(conjSubgroupsBy T L) => (i : Subgroup G)) ⟨_, hmem⟩
      ⟨z, hz, by simp [MulAut.conj_apply]⟩
  · refine iSup_le fun i => ?_
    obtain ⟨i, t, ht, rfl⟩ := i
    rintro _ ⟨z, hz, rfl⟩
    exact mem_conjClosure ht hz

theorem isBlock2_of_mem_conjSubgroupsBy {H T L : Subgroup G} (hTH : T ≤ H) (hL : IsBlock2 H L)
    {X : Subgroup G} (hX : X ∈ conjSubgroupsBy T L) : IsBlock2 H X := by
  obtain ⟨t, ht, rfl⟩ := hX
  have h := Setup.Campbell.isBlock2_map_conj hL t
  have e : Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj t)) H = H :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (Subgroup.le_normalizer (hTH ht))
  rwa [e] at h

theorem isQuasisimple_quot_of_isAltType_five {B : Subgroup G} (h : IsAltType B 5) :
    CFSG.IsQuasisimple (↥B ⧸ CFSG.pCore 2 ↥B) := by
  obtain ⟨α, hα, hαk, -⟩ := h
  exact C126.A5.isQuasisimple_of_alt_five
    ((QuotientGroup.quotientMulEquivOfEq hαk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hα))

theorem V_le_pCoreOf (hKer : Ker317A5) {T M V : Subgroup G} (h : HypE61 T M V)
    (hJ : thompsonJ T ≤ T ⊓ Subgroup.centralizer (V : Set G))
    (hC : ∀ U : Subgroup G, U ≤ V → U ≠ ⊥ →
      Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (V : Set G))
    {H : Subgroup G} (hH : IsHStar T M H)
    (hS : ¬ IsSylowTwoOf (baum T) (twoResidual H ⊔ baum T))
    {L : Subgroup G} (hL : IsBlock2 H L) (hL5 : IsAltType L 5)
    (hgen : H = T ⊔ conjClosure L T) : V ≤ pCoreOf 2 H := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF := isHStar_charTwo h hH
  have hsyl := isHStar_sylow h hH
  have hTH : T ≤ H := hH.1.1
  have hmin := isHStar_minParabolic h hJ hH
  have hred : IsTwoReducedIn H (VZ T H) := C1GN.isTwoReducedIn_VZ hF hsyl
  have hSQ : SQTKGroup ↥H := ⟨(isHStar_sqtk h hH).2, (isHStar_sqtk h hH).1⟩
  have hJZ := not_thompsonJ_le_centralizer_VZ h hJ hC hH
  have hns : ¬ Group.IsSolvable ↥H := by
    intro hsolv
    exact A5.G3.not_isSolvable_of_isAltType_five hL5
      (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hL.2.1)
        (Subgroup.inclusion_injective hL.2.1))
  have hker := hKer G H T (H ⊓ M) (VZ T H) hmin hSQ hF hred hJZ hns hS
  set K : Subgroup G := conjClosure L T with hKdef
  have hKiSup : K = ⨆ i : ↥(conjSubgroupsBy T L), (i : Subgroup G) := conjClosure_eq_iSup T L
  have hBblock : ∀ i : ↥(conjSubgroupsBy T L), IsBlock2 H i.1 := fun i =>
    isBlock2_of_mem_conjSubgroupsBy hTH hL i.2
  have hBalt : ∀ i : ↥(conjSubgroupsBy T L), IsAltType i.1 5 := by
    intro i
    obtain ⟨t, ht, hi⟩ := i.2
    rw [hi]
    exact L238.IsAltType.map_equiv hL5 (MulAut.conj t)
  have hBcomm : ∀ i j : ↥(conjSubgroupsBy T L), i ≠ j → ⁅i.1, j.1⁆ = ⊥ := fun i j hij =>
    C1Pack.commutator_eq_bot_of_quasisimple (hBblock i)
      (isQuasisimple_quot_of_isAltType_five (hBalt i)) (hBblock j) (fun h => hij (Subtype.ext h))
  have hKH : K ≤ H := by
    rw [hKiSup]
    exact iSup_le fun i => (hBblock i).2.1
  have hTN : T ≤ Subgroup.normalizer (K : Set G) := le_normalizer_conjClosure L T
  have hprod : ∀ x ∈ H, ∃ k ∈ K, ∃ s ∈ T, x = k * s := by
    intro x hx
    rw [hgen, sup_comm] at hx
    exact (F1.mem_sup_iff_exists_mul_of_normalizes hTN).1 hx
  have h111 := asc111Statement_holds G H K T ↥(conjSubgroupsBy T L) (fun i => i.1) inferInstance
    hBblock hBcomm hKiSup hKH hsyl hprod
  have hHK : H ≤ Subgroup.normalizer (K : Set G) := by
    rw [hgen]
    exact sup_le hTN Subgroup.le_normalizer
  have hKres : K ≤ twoResidual H := by
    rw [F6.twoResidual_eq_oTwoUpper, hKiSup]
    refine iSup_le fun i => ?_
    exact ((C1Pack.isShort2_eq_oTwoUpper (hBblock i).1).le).trans
      (oTwoUpper_mono (hBblock i).2.1)
  have hO2K : pCoreOf 2 K ≤ baum T := by
    refine le_trans ?_ hker
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hKres) ?_
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
    exact (twoResidual_le H).trans (hHK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
  have hcommle : ⁅pCoreOf 2 K, K⁆ ≤ pCoreOf 2 K := by
    refine Subgroup.commutator_le.2 fun q hq k hk => ?_
    have h1 : k * q⁻¹ * k⁻¹ ∈ pCoreOf 2 K :=
      (Subgroup.mem_normalizer_iff.1 (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K hk) q⁻¹).1
        (inv_mem hq)
    have : ⁅q, k⁆ = q * (k * q⁻¹ * k⁻¹) := by rw [commutatorElement_def]; group
    rw [this]
    exact mul_mem hq h1
  rw [← h111]
  intro v hv
  refine ⟨hTH (h.le hv), Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
  have hyc : y ∈ Subgroup.centralizer (V : Set G) :=
    (baum_le_Q h hJ (hO2K (hcommle hy))).2
  exact (Subgroup.mem_centralizer_iff.1 hyc v hv).symm


theorem exists_alt5Block (h129 : ASC129Statement G) {H T M V : Subgroup G}
    (hV : IsElemAbelian 2 V) (hmin : MinParabolic H T M) (hSQ : IsSQTKTC H) (hF : CharTwo H)
    (hred : IsTwoReducedIn H V) (hVZ : V = VZ T H)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G))
    (hRad : twoResidual H ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 H)
    (hA5 : C126.A5Case H T V hV)
    (hPU : ∀ C : Subgroup G, C ≤ baum T → C ≠ ⊥ → (C.subgroupOf (baum T)).Characteristic →
      ¬ H ≤ Subgroup.normalizer (C : Set G)) :
    ∃ L : Subgroup G, IsBlock2 H L ∧ IsAltType L 5 ∧ H = T ⊔ conjClosure L T := by
  obtain ⟨Y, s, ⟨d⟩⟩ := C126.A5.exists_setting_data hV hmin hSQ hF hred hVZ hJ hRad hA5
  obtain ⟨hY, hA3⟩ := E2.isShort2_and_isAltType_three_Y h129 s hPU
  obtain ⟨x, hxY, hx3, hxL, hxth⟩ := C126.A5.Lift.exists_x (s := s) (d := d)
  have hx : C126.A5.Lift.XData s d x := ⟨hxY, hx3, hxL, hxth⟩
  exact ⟨_, hx.isBlock2 hY hA3 hRad, hx.isAltType_five hY hA3 hRad, hx.gen_eq⟩


theorem four_le_card_of_one_lt_rParam {T M V : Subgroup G} (h : HypE61 T M V)
    (hr : 1 < E3.rParam V) : 4 ≤ Nat.card V := by
  have hV2 : Nat.card V = 2 ^ E3.mQuot V ⊥ := by
    have := E3.card_eq_two_pow_mul h.isPGroup_V (bot_le : (⊥ : Subgroup G) ≤ V)
    simpa using this
  have hc : 2 ≤ E3.mQuot V ⊥ := by
    have h1 : (1 : ℕ∞) < (E3.mQuot V ⊥ : ℕ∞) := lt_of_lt_of_le hr (rParam_le_mQuot_bot h)
    have h2 : 1 < E3.mQuot V ⊥ := by exact_mod_cast h1
    omega
  rw [hV2]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ E3.mQuot V ⊥ := Nat.pow_le_pow_right (by norm_num) hc

theorem false_of_not_sylow_baum (h129 : ∀ (G : Type) [Group G] [Finite G], ASC129Statement G)
    (hRF : C126.RadFreeStmt) (hKer : Ker317A5) (he23 : E2.E23Statement)
    {T M V : Subgroup G} (h : HypE61 T M V) (hr : 1 < E3.rParam V)
    (hJ : thompsonJ T ≤ T ⊓ Subgroup.centralizer (V : Set G))
    (hC : ∀ U : Subgroup G, U ≤ V → U ≠ ⊥ →
      Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (V : Set G))
    {H : Subgroup G} (hH : IsHStar T M H)
    (hS : ¬ IsSylowTwoOf (baum T) (twoResidual H ⊔ baum T)) : False := by
  have hF := isHStar_charTwo h hH
  have hsyl := isHStar_sylow h hH
  have hTH : T ≤ H := hH.1.1
  have hmin := isHStar_minParabolic h hJ hH
  have hred : IsTwoReducedIn H (VZ T H) := C1GN.isTwoReducedIn_VZ hF hsyl
  have hVel : IsElemAbelian 2 (VZ T H) := hred.2.2.1
  have hSQ : IsSQTKTC H := isHStar_sqtk h hH
  have hJZ := not_thompsonJ_le_centralizer_VZ h hJ hC hH
  have hc := he23 G H T (H ⊓ M) (VZ T H) hVel hmin ⟨hSQ.2, hSQ.1⟩ hF hred hJZ
  have hA5 : C126.A5Case H T (VZ T H) hVel := (E2.sylow_baum_or_a5Case hVel hc).resolve_left hS
  have hPU : ∀ C : Subgroup G, C ≤ baum T → C ≠ ⊥ → (C.subgroupOf (baum T)).Characteristic →
      ¬ H ≤ Subgroup.normalizer (C : Set G) := fun C hCS hC0 hchar hHC =>
    hH.2.1 (hHC.trans (normalizer_char_le_M h hJ hCS hC0 hchar))
  have hRad := hRF G H T (H ⊓ M) (VZ T H) hVel hmin hSQ hF hred rfl hJZ (Or.inr hA5)
  obtain ⟨L, hL, hL5, hgen⟩ := exists_alt5Block (h129 G) hVel hmin hSQ hF hred rfl hJZ hRad hA5 hPU
  have hVO := V_le_pCoreOf hKer h hJ hC hH hS hL hL5 hgen
  have hLM : ¬ L ≤ M := by
    intro hLM
    apply hH.2.1
    rw [hgen]
    refine sup_le h.inM.2 (conjClosure_le fun t ht z hz => ?_)
    exact M.mul_mem (M.mul_mem (h.inM.2 ht) (hLM hz)) (M.inv_mem (h.inM.2 ht))
  exact false_of_alt5Block hsyl hL hL5 h.inM.2 hLM h.isElemAbelian
    (by have := four_le_card_of_one_lt_rParam h hr; omega) h.le hVO
    (fun v hv hv1 x hx => mem_M_of_commute h hC hv hv1 hx)

end CFSG.Quasithin.RonanE628
