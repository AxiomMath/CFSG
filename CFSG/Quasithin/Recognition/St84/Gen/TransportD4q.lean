module

public import CFSG.Quasithin.Recognition.St84.Gen.TreeLLBase

import CFSG.Quasithin.Recognition.St84.Gen.TransferD4q
import CFSG.Quasithin.Recognition.St84.Gen.TransportTreeEquiv
import CFSG.Quasithin.Recognition.St84.Gen.TransportTreeLL
import CFSG.Quasithin.Recognition.St84.Gen.L2RankOne
import CFSG.Quasithin.Recognition.St84.Gen.D4qAmalMap
public import CFSG.Quasithin.Recognition.St84.Gen.D4qAmalDefs

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.Quasithin.St84
  CFSG.Quasithin.Fan86 CFSG.Quasithin.Fan86.Univ

variable {H : Type} [Group H] [Finite H]

theorem f112ll_d4qLocalData_oTwoPrime_of_tree {L1 L2 S : Subgroup H} {m n f : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2))
    {X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S)}
    (hX0 : X.vert 0 = baseA (f112Gold L1 L2 S)) (hX1 : X.vert 1 = baseB (f112Gold L1 L2 S))
    (hd : D4qLocalData (X.L 0) (X.L 1) X.S f) :
    D4qLocalData (oTwoPrime (f112saP1' L1 L2 S)) (oTwoPrime (f112saP2' L1 L2 S))
      (S ⊓ f112saK L1 L2 S) f := by
  have hR : Hyp111R L1 L2 S := hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2
  let D := f112EOddBaseEdgeData hF hR X hX0 hX1
  have hdD : D4qLocalData (D.X.L 0) (D.X.L 1) D.X.S f := hd
  change D4qLocalData (oTwoPrime D.Pα) (oTwoPrime D.Pβ) (D.S ⊓ D.Ke) f
  exact D4qLocalData.of_mulEquiv (BaseEdgeData.equivOfA D).symm (BaseEdgeData.equivOfB D).symm
    (f112ll_card_S_inf_K_of_tree hF hm hn h1 h2 hX0 hX1) hdD

theorem f112ll_d4qLocalData_oTwoPrime_of_tree_swap {L1 L2 S : Subgroup H} {m n f : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2))
    {X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S)}
    (hX0 : X.vert 0 = baseA (f112Gold L1 L2 S)) (hX1 : X.vert 1 = baseB (f112Gold L1 L2 S))
    (hd : D4qLocalData (X.L 1) (X.L 0) X.S f) :
    D4qLocalData (oTwoPrime (f112saP2' L1 L2 S)) (oTwoPrime (f112saP1' L1 L2 S))
      (S ⊓ f112saK L1 L2 S) f := by
  have hR : Hyp111R L1 L2 S := hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2
  let D := f112EOddBaseEdgeData hF hR X hX0 hX1
  have hdD : D4qLocalData (D.X.L 1) (D.X.L 0) D.X.S f := hd
  change D4qLocalData (oTwoPrime D.Pβ) (oTwoPrime D.Pα) (D.S ⊓ D.Ke) f
  exact D4qLocalData.of_mulEquiv (BaseEdgeData.equivOfB D).symm (BaseEdgeData.equivOfA D).symm
    (f112ll_card_S_inf_K_of_tree hF hm hn h1 h2 hX0 hX1) hdD

theorem f112ll_d4qLocalData_of_tree {L1 L2 S : Subgroup H} {m n f : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2))
    {X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S)}
    (hX0 : X.vert 0 = baseA (f112Gold L1 L2 S)) (hX1 : X.vert 1 = baseB (f112Gold L1 L2 S))
    (hd : D4qLocalData (X.L 0) (X.L 1) X.S f) : m = 3 * n ∧ D4qLocalData L1 L2 S n :=
  f112ll_d4qLocalData_of_edgeData hF hm hn h1 h2
    (f112ll_d4qLocalData_oTwoPrime_of_tree hF hm hn h1 h2 hX0 hX1 hd)

theorem f112ll_d4qLocalData_of_tree_swap {L1 L2 S : Subgroup H} {m n f : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2))
    {X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S)}
    (hX0 : X.vert 0 = baseA (f112Gold L1 L2 S)) (hX1 : X.vert 1 = baseB (f112Gold L1 L2 S))
    (hd : D4qLocalData (X.L 1) (X.L 0) X.S f) : n = 3 * m ∧ D4qLocalData L2 L1 S m :=
  f112ll_d4qLocalData_of_edgeData_swap hF hm hn h1 h2
    (f112ll_d4qLocalData_oTwoPrime_of_tree_swap hF hm hn h1 h2 hX0 hX1 hd)

end CFSG.Quasithin.F112R.St84

end
