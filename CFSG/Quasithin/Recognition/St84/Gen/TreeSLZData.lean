module

public import CFSG.Quasithin.Recognition.St84.Gen.TreeZDataGlue
public import CFSG.Quasithin.Recognition.St84.Gen.MixedCentralZData
import CFSG.Quasithin.Recognition.St84.Gen.Sec5Mixed
import CFSG.Quasithin.Recognition.St84.Gen.TreeSLBase
import CFSG.Quasithin.Recognition.St84.Gen.TreeSLCent
import CFSG.Quasithin.Recognition.St84.Gen.L2RankOne
import CFSG.Quasithin.Recognition.St84.Gen.TreeEOdd

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.Quasithin.St84
  CFSG.Quasithin.Fan86 CFSG.Quasithin.Fan86.Univ CFSG.GH74.QTGen4.DSGen4
open scoped Pointwise commutatorElement

theorem zDataS3L8_of_treeCentralZData (h : TreeCentralZData) : ZDataS3L8 := by
  intro G _ _ L1 L2 S hF h1 h2
  have hR : Hyp111R L1 L2 S :=
    hyp111R_of_isL2Quot (m := 1) (n := 3) (by norm_num) (by norm_num) hF.1
      (isL2Quot_of_VS3 h1) h2
  obtain ⟨Y, hY0, hY1, hZ⟩ := h G L1 L2 S 3 hF h1 le_rfl h2
  have hZD : S3L2ZData L1 L2 S (centerOf (pCoreOf 2 (f112saK L1 L2 S))) :=
    f112_s3L2ZData_of_centralZData_of_hyp111R hF hR
      (f112sl_oTwoRes_le_oTwoPrime_P2' (by norm_num) h2)
      (f112_EOdd_inf_ofA_range_of_hyp111R hF.toW hR)
      (f112_EOdd_inf_ofB_range_of_hyp111R hF.toW hR)
      (f112_EOdd_inf_ofA_range_inf_ofB_range_of_hyp111R hF.toW hR)
      Y hY0 hY1 hZ
  refine ⟨_, hZD, ?_⟩
  intro u hu hu2 huS
  have hZ' : L2 ≤ Subgroup.centralizer (centerOf (S ⊓ f112saK L1 L2 S) : Set G) := by
    simpa only [← f112sl_pCoreOf_K_eq hF h1 (by norm_num) h2] using hZD.L2_cent
  rw [f112sl_pCoreOf_K_eq hF h1 (by norm_num) h2]
  exact f112sl_mem_centerOf_of_commute_of_hyp111R hF hR hZ' hu hu2 huS

theorem idS3L8_of_treeCentralZData
    (hR1b : F112R1bLocStatement) (h : TreeCentralZData) : IdS3L8 :=
  idS3L8_of_zData hR1b (zDataS3L8_of_treeCentralZData h)

theorem treeCentralZData_of_st84Mixed
    (h : St84MixedCentralZData) : TreeCentralZData := by
  intro G _ _ L1 L2 S n hF h1 h3 h2
  obtain ⟨Y, hY0, hY1⟩ := f112sl_exists_setup_baseEdge_swap hF h1 (by omega) h2
  have hn0 : Y.n 0 = n := by
    show nOf (f112Gold L1 L2 S).treeGraph (Y.vert 0) = n
    rw [hY0]
    simpa using f112sa_nOf_beta hF h1 (by omega) h2
      (1 : (f112Gold L1 L2 S).Universal)
  have hn1 : Y.n 1 = 1 := by
    show nOf (f112Gold L1 L2 S).treeGraph (Y.vert 1) = 1
    rw [hY1]
    simpa using f112sa_nOf_alpha hF h1 (by omega) h2
      (1 : (f112Gold L1 L2 S).Universal)
  have hY3 : 3 ≤ Y.n 0 := hn0.symm ▸ h3
  exact ⟨Y, hY0, hY1,
    h (V := Vtx (f112Gold L1 L2 S)) (G := ↥(f112EOdd L1 L2 S))
      (f112Gold L1 L2 S).treeGraph (f112sl_hyp30 hF h1 (by omega) h2)
      (f112sa_charTwoStab hF h1 (by omega) h2) Y hY3 hn1⟩

theorem noS3L2Big_of_st84Mixed
    (h : St84MixedCentralZData) : NoS3L2Big :=
  noS3L2Big_of_treeCentralZData (treeCentralZData_of_st84Mixed h)

theorem idS3L8_of_st84Mixed
    (hR1b : F112R1bLocStatement) (h : St84MixedCentralZData) : IdS3L8 :=
  idS3L8_of_treeCentralZData hR1b (treeCentralZData_of_st84Mixed h)

theorem noS3L2Big_holds : NoS3L2Big :=
  noS3L2Big_of_st84Mixed st84MixedCentralZData_holds

theorem idS3L8_of_f112R1bLoc (hR1b : F112R1bLocStatement) : IdS3L8 :=
  idS3L8_of_st84Mixed hR1b st84MixedCentralZData_holds

end CFSG.Quasithin.F112R.St84
