module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCFourteenSixCalW
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCFourteenSixBBound
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCFourteenSixMBound
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCFourteenSixWClos
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCFourteenSixShape
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HeJ2Local17
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SU3NaturalModuleAltTwoHolds
public import CFSG.LocalAnalysis.UniquenessCase.UCKPSyl3
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81 CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem uc2_14_6_paraThree_le_of_weakClosure
    {D : Data G} {Y V H : Subgroup G} {n : ℕ} (hY : Y ∈ calC D.M)
    (hV : IsElemAbelian 2 V) (hW : InCalW D.M D.T V) (hU : IsElemAbelian 2 D.U)
    (hXY : UC22.conjClosure D.M Y = Y) (hUY : UniqueMax D.M (Y ⊔ D.T))
    (hY1 : barSub ⊥ D.U hU Y ≠ ⊥) (hm : 2 * n ≤ mBar D.M ⊥ V hV)
    (hb : bBar (UC22.conjClosure D.M Y) D.M ⊥ D.U hU ≤ n) (hn : 3 ≤ n)
    (hE : E1.InE 1 (H ⊔ D.T)) : H ≤ D.M := by
  have hMV : D.M ≤ normalizer (V : Set G) := hW.1.1.2.2.1
  have h111 : W3Thm111 G := w3Thm111_unconditional
  have hbot : D.M ≤ normalizer ((⊥ : Subgroup G) : Set G) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hm2 : MBarGT D.M ⊥ V 2 :=
    (mBarGT_iff_lt_mBar D.M ⊥ V hV bot_le hMV hbot 2).2 (by omega)
  have hmb : MBarGT D.M ⊥ V (1 + bBar (UC22.conjClosure D.M Y) D.M ⊥ D.U hU) :=
    (mBarGT_iff_lt_mBar D.M ⊥ V hV bot_le hMV hbot _).2 (by omega)
  have hm1 : MBarGT D.M ⊥ V (0 + 1) :=
    (mBarGT_iff_lt_mBar D.M ⊥ V hV bot_le hMV hbot _).2 (by omega)
  have hlt : 1 + bBar (UC22.conjClosure D.M Y) D.M ⊥ D.U hU < E3.sParam hV :=
    TwelveShort.lt_sParam_of_mBarGT D h111 hW.1 hm2 hmb
  have hrk : 1 < rk ↥V := by
    have h1 := mBar_le_rk (M := D.M) (V₀ := ⊥) hV bot_le
    omega
  have hPU : pCoreOf 2 D.M ≤ centralizer (D.U : Set G) :=
    Subgroup.le_centralizer_iff.mp ((uc22p22c_U_facts D).1.trans inf_le_right)
  obtain ⟨hNW, hCC⟩ :=
    normalizer_wClos_le_of_bBar_add_lt D hW.1.1 hV hU (uc22p22e_inCalV_U D).2.2.1 hPU hY.1
      hY.2.2 hY1 (by rw [hXY]; exact hUY) (i := 1) hrk hlt
  have h21 := twelve_twentyOne_three D h111 hW.1 hm2
    (TwelveShort.isSylowIn_of_le D (le_sup_right : D.T ≤ H ⊔ D.T)) (i := 0) (j := 1) hE hm1
  have hHTM : H ⊔ D.T ≤ D.M := by
    rw [← h21]
    refine sup_le ?_ ?_
    · exact inf_le_right.trans (hCC 0 (Nat.zero_le _))
    · exact inf_le_right.trans (hNW 0 (by omega))
  exact le_sup_left.trans hHTM

theorem uc2_14_6_paraThree
    {D : Data G} (h869 : F08.R869 D) (h128 : W4Lem12_8) (h36 : W4Lem3_6) (h416 : W4Lem4_16)
    (hgr : CFSG.Open.GriessAllModelsStatement) {Y : Subgroup G} {n : ℕ} (hY : Y ∈ calC D.M)
    (hMY : D.M ≤ normalizer (Y : Set G)) (hSU : IsSU3 (Bar2 Y) n) (hn : 3 ≤ n)
    (hYZ : ⁅Y, D.Z⁆ ≠ ⊥) {H : Subgroup G} (hTH : D.T ≤ normalizer (H : Set G))
    (hcase : Group.IsSolvable ↥H ∨
      (IsSimpleGroup (UC22.BarInf H) ∧
        ((∃ p e : ℕ, p.Prime ∧ p ≠ 2 ∧ 5 < p ^ e ∧ F6.IsL2 p e (UC22.BarInf H)) ∨
          ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧
            (LieModel (UC22.BarInf H) .PSL 3 p f ∨ LieModel (UC22.BarInf H) .PSU 3 p f)))) :
    H ≤ D.M := by
  classical
  have hTM : D.T ≤ D.M := D.sylowM.le
  have hYM : Y ≤ D.M := hY.1.le
  have hYn : (Y.subgroupOf D.M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYM).2 hMY
  have hXY : UC22.conjClosure D.M Y = Y := conjClosure_eq_self_of_normal hYM hYn
  have hUY : UniqueMax D.M (Y ⊔ D.T) :=
    uniqueMax_sup_T_of_not_thin h869 hY
      (S17.not_thin_of_isSU3 (UCK.u3Syl_of_griess hgr) hSU)
  obtain ⟨V, hV, hVU, hMV, hYV, hmin, hW, -, -, -⟩ :=
    exists_inCalW_min_of_normal hY hMY hUY hYZ
  have hm : 2 * n ≤ mBar D.M ⊥ V hV :=
    two_mul_le_mBar_of_min (k_SU3NaturalModule_of_w4_holds h128 h36) hV hY hMY hSU hn
      hVU hMV hYV hmin hW.2.2
  have hU : IsElemAbelian 2 D.U := (uc22p22e_inCalV_U D).2.2.2
  have hMU : D.M ≤ normalizer (D.U : Set G) := (uc22p22e_inCalV_U D).2.2.1
  have hZU : D.Z ≤ D.U := uc22p22e_omegaOneCenterIn_le_uCore D.M D.T
  have hZT : D.Z ≤ centralizer (D.T : Set G) := fun z hz =>
    Subgroup.mem_centralizer_iff.2 fun t ht =>
      (CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff.1 hz).2.1 t ht
  have hMS : D.M ≤ stabTil ⊥ D.U :=
    le_stabTil hMU (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  have h2M : barSub ⊥ D.U hU (pCoreOf 2 D.M) = ⊥ := by
    have hcent : pCoreOf 2 D.M ≤ centralizer (D.U : Set G) :=
      Subgroup.le_centralizer_iff.mp ((uc22p22c_U_facts D).1.trans inf_le_right)
    rw [TwelveTwentyThree.barSub_bot_eq_map_autI,
      show autI hU (pCoreOf 2 D.M) = ⊥ from
        (autI_eq_bot_iff hU
          ((CFSG.LieType.BorelTits.pCoreOf_le 2 D.M).trans hMU)).2 hcent,
      Subgroup.map_bot]
  have h2Y : barSub ⊥ D.U hU (pCoreOf 2 Y) = ⊥ :=
    TwelveTwentyThree.barSub_pCoreOf_eq_bot_of_isSubnormal hU hY.1 h2M
  have hY1 : barSub ⊥ D.U hU Y ≠ ⊥ := by
    intro h0
    have hYC : Y ≤ centralizer (D.U : Set G) := by
      intro y hy
      have hys : y ∈ stabTil ⊥ D.U := hMS (hYM hy)
      have hmem : actTil ⊥ D.U hU ⟨y, hys⟩ ∈ barSub ⊥ D.U hU Y :=
        actTil_mem_barSub ⊥ D.U hU hy hys
      rw [h0, Subgroup.mem_bot] at hmem
      exact (TwelveTwentyThree.actTil_bot_eq_one_iff D.U hU ⟨y, hys⟩).1 hmem
    exact hYZ (Subgroup.commutator_eq_bot_iff_le_centralizer.2
      (hYC.trans (Subgroup.centralizer_le hZU)))
  have hSUb : IsSU3 ↥(barSub ⊥ D.U hU Y) n :=
    UC22.isSU3_barSub hU (hYM.trans hMS) h2Y hY1 hSU
  have hodd : Odd (Nat.card (Subgroup.center ↥(barSub ⊥ D.U hU Y))) :=
    Odd.of_dvd_nat (by norm_num) (UCK.u3Center_of_griess hgr _ n hSUb)
  have hT : ¬ D.U ⊓ centralizer (D.T : Set G) ≤ centralizer (Y : Set G) := by
    intro h
    have hZY : D.Z ≤ centralizer (Y : Set G) := fun z hz => h ⟨hZU hz, hZT hz⟩
    exact hYZ (Subgroup.commutator_eq_bot_iff_le_centralizer.2
      (Subgroup.le_centralizer_iff.mp hZY))
  have hb : bBar Y D.M ⊥ D.U hU ≤ n :=
    bBar_le_of_not_inf_centralizer_le h416 hU hMU hY hMY h2Y hY1 hSUb hodd hT
  have hb' : bBar (UC22.conjClosure D.M Y) D.M ⊥ D.U hU ≤ n := by
    rwa [hXY]
  have hT2 : IsPGroup 2 D.T := (TwelveShort.isSylowIn_of_le D hTM).isPGroup
  have hE : E1.InE 1 (H ⊔ D.T) := inE_one_sup_of_shape hTH hT2 hcase
  exact uc2_14_6_paraThree_le_of_weakClosure hY hV hW hU hXY hUY hY1 hm hb' hn hE

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
