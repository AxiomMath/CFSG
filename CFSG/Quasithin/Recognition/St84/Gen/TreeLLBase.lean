module

public import CFSG.Quasithin.Recognition.St84.TreeBase
public import CFSG.Quasithin.Recognition.St84.Gen.TreeEOdd
public import CFSG.Quasithin.Recognition.St84.Gen.TreeLLHyp

import CFSG.Quasithin.Recognition.St84.Gen.L2RankOne

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.Quasithin.St84
  CFSG.Quasithin.Fan86 CFSG.Quasithin.Fan86.Univ

variable {H : Type} [Group H] [Finite H]

@[expose] noncomputable def f112EOddBaseEdgeData {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (hR : Hyp111R L1 L2 S)
    (X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S))
    (hX0 : X.vert 0 = baseA (f112Gold L1 L2 S))
    (hX1 : X.vert 1 = baseB (f112Gold L1 L2 S)) :
    BaseEdgeData H :=
  { L1 := L1, L2 := L2, S := S, E := f112EOdd L1 L2 S
    Pα := f112saP1' L1 L2 S, Pβ := f112saP2' L1 L2 S, Ke := f112saK L1 L2 S
    le_Pα := f112sa_P1'_le_P1 hF
    le_Pβ := f112sa_P2'_le_P2 hF
    le_Ke := by rw [f112_inf_eq_bigB_of_hyp111R hR]; exact f112sa_K_le_bigB L1 L2 S
    ofA_eq := f112_EOdd_inf_ofA_range_of_hyp111R hF hR
    ofB_eq := f112_EOdd_inf_ofB_range_of_hyp111R hF hR
    ofA_inf_ofB_eq := f112_EOdd_inf_ofA_range_inf_ofB_range_of_hyp111R hF hR
    X := X, X_zero := hX0, X_one := hX1 }

theorem f112ll_exists_setup_baseEdge {L1 L2 S : Subgroup H} {m n : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    ∃ X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S),
      X.vert 0 = baseA (f112Gold L1 L2 S) ∧ X.vert 1 = baseB (f112Gold L1 L2 S) :=
  (f112ll_hyp30 hF hm hn h1 h2).exists_setup' (adj_baseA_baseB (f112Gold L1 L2 S))

theorem f112ll_exists_setup_baseEdge_swap {L1 L2 S : Subgroup H} {m n : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    ∃ Y : Setup (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S),
      Y.vert 0 = baseB (f112Gold L1 L2 S) ∧ Y.vert 1 = baseA (f112Gold L1 L2 S) :=
  (f112ll_hyp30 hF hm hn h1 h2).exists_setup'
    (adj_baseA_baseB (f112Gold L1 L2 S)).symm

theorem f112ll_pCoreOf_K_eq {L1 L2 S : Subgroup H} {m n : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    pCoreOf 2 (f112saK L1 L2 S) = S ⊓ f112saK L1 L2 S := by
  have hR : Hyp111R L1 L2 S :=
    hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2
  obtain ⟨X, hX0, hX1⟩ := f112ll_exists_setup_baseEdge hF hm hn h1 h2
  exact eq_pCoreOf_of_isSylowTwoOf (f112sa_T_sylow_K_of_hyp111R hF hR)
    (f112EOddBaseEdgeData hF hR X hX0 hX1).isSylowTwoOf_pCoreOf

theorem f112ll_pCoreOf_sup_eq {L1 L2 S : Subgroup H} {m n : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    pCoreOf 2 (f112saP1' L1 L2 S) ⊔ pCoreOf 2 (f112saP2' L1 L2 S) =
      S ⊓ f112saK L1 L2 S := by
  have hR : Hyp111R L1 L2 S :=
    hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2
  obtain ⟨X, hX0, hX1⟩ := f112ll_exists_setup_baseEdge hF hm hn h1 h2
  rw [← f112ll_pCoreOf_K_eq hF hm hn h1 h2]
  exact (f112EOddBaseEdgeData hF hR X hX0 hX1).sup_pCoreOf_eq_pCoreOf
    (f112ll_charTwoStab hF hm hn h1 h2)

theorem f112ll_isL2Quot_oTwoPrime_P1' {L1 L2 S : Subgroup H} {m n : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    IsL2Quot m (oTwoQuot ↥(oTwoPrime (f112saP1' L1 L2 S))) := by
  have hR : Hyp111R L1 L2 S :=
    hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2
  obtain ⟨X, hX0, hX1⟩ := f112ll_exists_setup_baseEdge hF hm hn h1 h2
  have h := (f112EOddBaseEdgeData hF hR X hX0 hX1).isL2Quot_oTwoPrime_ofA
  have hnα : nOf (f112Gold L1 L2 S).treeGraph (baseA (f112Gold L1 L2 S)) = m := by
    simpa using f112_nOf_alpha_of_isL2Quot hR (by omega) h1
      (1 : (f112Gold L1 L2 S).Universal)
  exact hnα ▸ h

theorem f112ll_isL2Quot_oTwoPrime_P2' {L1 L2 S : Subgroup H} {m n : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    IsL2Quot n (oTwoQuot ↥(oTwoPrime (f112saP2' L1 L2 S))) := by
  have hR : Hyp111R L1 L2 S :=
    hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2
  obtain ⟨X, hX0, hX1⟩ := f112ll_exists_setup_baseEdge hF hm hn h1 h2
  have h := (f112EOddBaseEdgeData hF hR X hX0 hX1).isL2Quot_oTwoPrime_ofB
  have hnβ : nOf (f112Gold L1 L2 S).treeGraph (baseB (f112Gold L1 L2 S)) = n := by
    simpa using f112_nOf_beta_of_isL2Quot hR (by omega) h2
      (1 : (f112Gold L1 L2 S).Universal)
  exact hnβ ▸ h

end CFSG.Quasithin.F112R.St84
