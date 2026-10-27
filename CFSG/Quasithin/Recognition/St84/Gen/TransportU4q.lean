module

public import CFSG.Quasithin.Recognition.St84.Gen.TransferU4qBasic
public import CFSG.Quasithin.Recognition.St84.Gen.TreeLLBase

import CFSG.Quasithin.Recognition.St84.Gen.TransferU4q
import CFSG.Quasithin.Recognition.St84.Gen.L2RankOne
import CFSG.Quasithin.Recognition.St84.Gen.TransportTreeLL
import CFSG.Quasithin.Recognition.St84.Gen.TransportTreeEquiv
import CFSG.Quasithin.Recognition.St84.Gen.TwoNatMap
import CFSG.Quasithin.Recognition.St84.Gen.U4qModel
public import CFSG.Quasithin.Recognition.F112RShapes
public import CFSG.Quasithin.Recognition.GoldschmidtF112RTransport

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.Quasithin.St84
  CFSG.Quasithin.Fan86 CFSG.Quasithin.Fan86.Univ

variable {H : Type} [Group H] [Finite H]

theorem f112ll_u4qLocalData_oTwoPrime_of_tree {L1 L2 S : Subgroup H} {m n f : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2))
    {X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S)}
    (hX0 : X.vert 0 = baseA (f112Gold L1 L2 S)) (hX1 : X.vert 1 = baseB (f112Gold L1 L2 S))
    (hd : U4qLocalData (X.L 0) (X.L 1) X.S f) :
    U4qEdgeData L1 L2 S f := by
  have hR : Hyp111R L1 L2 S := hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2
  let D := f112EOddBaseEdgeData hF hR X hX0 hX1
  have hD : U4qLocalData (D.X.L 0) (D.X.L 1) D.X.S f := hd
  change U4qLocalData (oTwoPrime D.Pα) (oTwoPrime D.Pβ) (D.S ⊓ D.Ke) f
  refine
    { card_S := (f112ll_card_S_inf_K_of_tree hF hm hn h1 h2 hX0 hX1).symm ▸ hd.card_S
      special_left := CFSG.Quasithin.IsSpecialPow.of_mulEquiv
        (pCoreOfMulEquiv (BaseEdgeData.equivOfA D) 2) hD.special_left
      center_left := le_centralizer_centerOf_pCoreOf_of_mulEquiv
        (BaseEdgeData.equivOfA D).symm hD.center_left
      twoNat_left := IsTwoNatType.of_mulEquiv (BaseEdgeData.equivOfA D).symm hD.twoNat_left
      card_right :=
        (f112ll_card_pCoreOf_P2'_of_tree hF hm hn h1 h2 hX0 hX1).trans hd.card_right
      omega_right := CFSG.Quasithin.IsOmega4MinusType.of_mulEquiv
        (BaseEdgeData.equivOfB D).symm hD.omega_right
      card_inf :=
        (f112ll_card_pCoreOf_inf_of_tree hF hm hn h1 h2 hX0 hX1).trans hd.card_inf }

theorem f112ll_u4qLocalData_oTwoPrime_of_tree_swap {L1 L2 S : Subgroup H} {m n f : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2))
    {X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S)}
    (hX0 : X.vert 0 = baseA (f112Gold L1 L2 S)) (hX1 : X.vert 1 = baseB (f112Gold L1 L2 S))
    (hd : U4qLocalData (X.L 1) (X.L 0) X.S f) :
    U4qLocalData (oTwoPrime (f112saP2' L1 L2 S)) (oTwoPrime (f112saP1' L1 L2 S))
      (S ⊓ f112saK L1 L2 S) f := by
  have hR : Hyp111R L1 L2 S := hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2
  let D := f112EOddBaseEdgeData hF hR X hX0 hX1
  have hD : U4qLocalData (D.X.L 1) (D.X.L 0) D.X.S f := hd
  change U4qLocalData (oTwoPrime D.Pβ) (oTwoPrime D.Pα) (D.S ⊓ D.Ke) f
  refine
    { card_S := (f112ll_card_S_inf_K_of_tree hF hm hn h1 h2 hX0 hX1).symm ▸ hd.card_S
      special_left := CFSG.Quasithin.IsSpecialPow.of_mulEquiv
        (pCoreOfMulEquiv (BaseEdgeData.equivOfB D) 2) hD.special_left
      center_left := le_centralizer_centerOf_pCoreOf_of_mulEquiv
        (BaseEdgeData.equivOfB D).symm hD.center_left
      twoNat_left := IsTwoNatType.of_mulEquiv (BaseEdgeData.equivOfB D).symm hD.twoNat_left
      card_right :=
        (f112ll_card_pCoreOf_P1'_of_tree hF hm hn h1 h2 hX0 hX1).trans hd.card_right
      omega_right := CFSG.Quasithin.IsOmega4MinusType.of_mulEquiv
        (BaseEdgeData.equivOfA D).symm hD.omega_right
      card_inf :=
        calc Nat.card ↥(pCoreOf 2 (oTwoPrime D.Pβ) ⊓ pCoreOf 2 (oTwoPrime D.Pα))
            = Nat.card ↥(pCoreOf 2 (oTwoPrime D.Pα) ⊓ pCoreOf 2 (oTwoPrime D.Pβ)) :=
              Nat.card_congr (MulEquiv.subgroupCongr (inf_comm _ _)).toEquiv
          _ = Nat.card ↥(pCoreOf 2 (X.L 0) ⊓ pCoreOf 2 (X.L 1)) :=
              f112ll_card_pCoreOf_inf_of_tree hF hm hn h1 h2 hX0 hX1
          _ = Nat.card ↥(pCoreOf 2 (X.L 1) ⊓ pCoreOf 2 (X.L 0)) :=
              Nat.card_congr (MulEquiv.subgroupCongr (inf_comm _ _)).toEquiv
          _ = 2 ^ (3 * f) := hd.card_inf }

theorem f112ll_u4qLocalData_of_tree {L1 L2 S : Subgroup H} {m n f : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2))
    {X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S)}
    (hX0 : X.vert 0 = baseA (f112Gold L1 L2 S)) (hX1 : X.vert 1 = baseB (f112Gold L1 L2 S))
    (hd : U4qLocalData (X.L 0) (X.L 1) X.S f) :
    n = 2 * m ∧ U4qLocalData L1 L2 S m :=
  f112ll_u4qLocalData_of_edgeData hF hm hn h1 h2
    (f112ll_u4qLocalData_oTwoPrime_of_tree hF hm hn h1 h2 hX0 hX1 hd)

theorem f112ll_u4qLocalData_of_tree_swap {L1 L2 S : Subgroup H} {m n f : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2))
    {X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S)}
    (hX0 : X.vert 0 = baseA (f112Gold L1 L2 S)) (hX1 : X.vert 1 = baseB (f112Gold L1 L2 S))
    (hd : U4qLocalData (X.L 1) (X.L 0) X.S f) :
    m = 2 * n ∧ U4qLocalData L2 L1 S n :=
  f112ll_u4qLocalData_of_edgeData_swap hF hm hn h1 h2
    (f112ll_u4qLocalData_oTwoPrime_of_tree_swap hF hm hn h1 h2 hX0 hX1 hd)

end CFSG.Quasithin.F112R.St84

end
