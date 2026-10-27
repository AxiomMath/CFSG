module

public import CFSG.Quasithin.Recognition.St84.Gen.TreeLLBase
public import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalDefs

import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalMap
import CFSG.Quasithin.Recognition.St84.Gen.L2RankOne
import CFSG.Quasithin.Recognition.St84.Gen.TransportTreeEquiv
import CFSG.Quasithin.Recognition.St84.Gen.TransportTreeLL

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Quasithin CFSG.Quasithin.St84 CFSG.Quasithin.Fan86.Univ

variable {H : Type} [Group H] [Finite H]

theorem f112ll_g2qLocalData_oTwoPrime_of_tree {L1 L2 S : Subgroup H} {m n f : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2))
    {X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S)}
    (hX0 : X.vert 0 = baseA (f112Gold L1 L2 S)) (hX1 : X.vert 1 = baseB (f112Gold L1 L2 S))
    (hd : G2qLocalData (X.L 0) (X.L 1) X.S f) :
    G2qLocalData (oTwoPrime (f112saP1' L1 L2 S)) (oTwoPrime (f112saP2' L1 L2 S))
      (S ⊓ f112saK L1 L2 S) f := by
  have hR : Hyp111R L1 L2 S := hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2
  let D := f112EOddBaseEdgeData hF hR X hX0 hX1
  have hD : G2qLocalData (D.X.L 0) (D.X.L 1) D.X.S f := hd
  change G2qLocalData (oTwoPrime D.Pα) (oTwoPrime D.Pβ) (D.S ⊓ D.Ke) f
  exact G2qLocalData.of_mulEquiv
    (L1 := oTwoPrime D.Pα) (L2 := oTwoPrime D.Pβ) (S := D.S ⊓ D.Ke)
    (L1' := D.X.L 0) (L2' := D.X.L 1) (S' := D.X.S)
    (BaseEdgeData.equivOfA D).symm (BaseEdgeData.equivOfB D).symm
    (f112ll_card_S_inf_K_of_tree hF hm hn h1 h2 hX0 hX1)
    (f112ll_card_pCoreOf_inf_of_tree hF hm hn h1 h2 hX0 hX1) hD

end CFSG.Quasithin.F112R.St84

end
