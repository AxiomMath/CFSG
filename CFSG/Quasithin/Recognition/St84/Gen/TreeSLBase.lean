module

public import CFSG.Quasithin.Recognition.St84.TreeBase
import CFSG.Quasithin.Recognition.St84.Gen.TreeLLBase
import CFSG.Quasithin.Recognition.St84.Gen.L2RankOne

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.Quasithin.St84
  CFSG.Quasithin.Fan86 CFSG.Quasithin.Fan86.Univ CFSG.GH74.QTGen4.DSGen4
open scoped Pointwise commutatorElement

variable {H : Type} [Group H] [Finite H]

theorem f112sl_exists_setup_baseEdge {L1 L2 S : Subgroup H}
    {n : ℕ} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    ∃ X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S),
      X.vert 0 = baseA (f112Gold L1 L2 S) ∧ X.vert 1 = baseB (f112Gold L1 L2 S) :=
  (f112sl_hyp30 hF h1 hn h2).exists_setup' (adj_baseA_baseB (f112Gold L1 L2 S))

theorem f112sl_pCoreOf_K_eq {L1 L2 S : Subgroup H}
    {n : ℕ} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    pCoreOf 2 (f112saK L1 L2 S) = S ⊓ f112saK L1 L2 S := by
  have hR : Hyp111R L1 L2 S :=
    hyp111R_of_isL2Quot (m := 1) (n := n) (by norm_num) (by omega) hF.1
      (isL2Quot_of_VS3 h1) h2
  obtain ⟨X, hX0, hX1⟩ := f112sl_exists_setup_baseEdge hF h1 hn h2
  exact eq_pCoreOf_of_isSylowTwoOf (f112sa_T_sylow_K_of_hyp111R hF.toW hR)
    (f112EOddBaseEdgeData hF.toW hR X hX0 hX1).isSylowTwoOf_pCoreOf

theorem f112sl_exists_setup_baseEdge_swap {L1 L2 S : Subgroup H}
    {n : ℕ} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    ∃ Y : Setup (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S),
      Y.vert 0 = baseB (f112Gold L1 L2 S) ∧
        Y.vert 1 = baseA (f112Gold L1 L2 S) :=
  (f112sl_hyp30 hF h1 hn h2).exists_setup'
    (adj_baseA_baseB (f112Gold L1 L2 S)).symm

end CFSG.Quasithin.F112R.St84
