module

public import CFSG.Quasithin.Recognition.St84.Gen.TreeZData
import CFSG.Quasithin.Recognition.St84.Gen.OTwoPrimeL2
import CFSG.Quasithin.Recognition.SzR1cHolds
import CFSG.Quasithin.Recognition.St84.Gen.L2RankOne
import CFSG.Quasithin.Recognition.St84.Gen.TreeEOdd

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.Quasithin.St84
  CFSG.Quasithin.Fan86 CFSG.Quasithin.Fan86.Univ CFSG.GH74.QTGen4.DSGen4
open scoped Pointwise commutatorElement

variable {H : Type} [Group H] [Finite H]

theorem f112sl_oTwoRes_le_oTwoPrime_P2' {L1 L2 S : Subgroup H} {n : ℕ} (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    oTwoRes L2 ≤ oTwoPrime (f112saP2' L1 L2 S) := by
  have hq : IsL2Quot n (oTwoQuot ↥(oTwoRes L2)) := f112sl_oTwoRes_quot hn h2
  exact le_oTwoPrime_of_isL2Quot_of_two_le hn le_sup_left hq

@[expose] def TreeCentralZData : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G) (n : ℕ),
    F112Hyp L1 L2 S → VS3 L1 → 3 ≤ n → IsL2Quot n (oTwoQuot ↥L2) →
      ∃ Y : Setup (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S),
        Y.vert 0 = baseB (f112Gold L1 L2 S) ∧ Y.vert 1 = baseA (f112Gold L1 L2 S) ∧
          Y.CentralZData

theorem zDataS3L2_of_treeCentralZData (h : TreeCentralZData) : ZDataS3L2 := by
  intro G _ _ L1 L2 S n hF h1 h4 h2
  have hR : Hyp111R L1 L2 S :=
    hyp111R_of_isL2Quot (m := 1) (n := n) (by norm_num) (by omega) hF.1
      (isL2Quot_of_VS3 h1) h2
  obtain ⟨Y, hY0, hY1, hZ⟩ := h G L1 L2 S n hF h1 (by omega) h2
  exact ⟨centerOf (pCoreOf 2 (f112saK L1 L2 S)),
    f112_s3L2ZData_of_centralZData_of_hyp111R hF hR
      (f112sl_oTwoRes_le_oTwoPrime_P2' (by omega) h2)
      (f112_EOdd_inf_ofA_range_of_hyp111R hF.toW hR)
      (f112_EOdd_inf_ofB_range_of_hyp111R hF.toW hR)
      (f112_EOdd_inf_ofA_range_inf_ofB_range_of_hyp111R hF.toW hR)
      Y hY0 hY1 hZ⟩

theorem noS3L2Big_of_treeCentralZData (h : TreeCentralZData) :
    NoS3L2Big :=
  noS3L2Big_of_zData f112R1c_holds (zDataS3L2_of_treeCentralZData h)

end CFSG.Quasithin.F112R.St84
