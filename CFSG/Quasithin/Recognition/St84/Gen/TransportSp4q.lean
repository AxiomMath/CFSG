module

public import CFSG.Quasithin.Recognition.St84.Gen.TreeLLBase
public import CFSG.Quasithin.Recognition.St84.Gen.TransferLL
public import CFSG.Quasithin.Recognition.St84.Gen.Sp4qAmalDefs

import CFSG.Quasithin.Recognition.St84.Gen.TransportTreeLL
public import CFSG.CGT.PushingUpLit.BHS.OffenderInternal
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldNaturalAction
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftBaumannDelOrigData
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDelBlockTools
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDelH0
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceCommon
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathGate5
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathGate6
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points
public import CFSG.Quasithin.Background.C1GNA7
public import CFSG.Quasithin.Background.C1PackBasic
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModPack28Proof
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModS5Irr
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModSecIrred
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.Steps
public import CFSG.Quasithin.EmptyFaithful.SzF53BasE
public import CFSG.Quasithin.EmptyFaithful.SzF53MSecB
public import CFSG.Quasithin.H13.GoldschmidtC137BaumMain
public import CFSG.Quasithin.H13.GoldschmidtC137Data
public import CFSG.Quasithin.H13.GoldschmidtC137U33Hyp
public import CFSG.Quasithin.H13.GoldschmidtC137U33S2Over
public import CFSG.Quasithin.H13.GoldschmidtC137U33S2Self
public import CFSG.Quasithin.H13.LinearOrders
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Defs
public import CFSG.Quasithin.Recognition.GoldschmidtFan86TArcEven
public import CFSG.Quasithin.Recognition.St84.AppTreeSAP1
public import CFSG.Quasithin.Recognition.St84.PushUp
public import CFSG.RankThree.PartTwo.Sec15.Item153PushProofTools
public import Certificates.Kernel.J4Count.Prim

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.Quasithin.St84
  CFSG.Quasithin.Fan86 CFSG.Quasithin.Fan86.Univ

variable {H : Type} [Group H] [Finite H]

theorem f112ll_sp4qLocalData_oTwoPrime_of_tree {L1 L2 S : Subgroup H} {m n f : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2))
    {X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S)}
    (hX0 : X.vert 0 = baseA (f112Gold L1 L2 S)) (hX1 : X.vert 1 = baseB (f112Gold L1 L2 S))
    (hd : Sp4qLocalData (X.L 0) (X.L 1) X.S f) :
    Sp4qLocalData (oTwoPrime (f112saP1' L1 L2 S)) (oTwoPrime (f112saP2' L1 L2 S))
      (S ⊓ f112saK L1 L2 S) f := by
  refine
    { card_S := (f112ll_card_S_inf_K_of_tree hF hm hn h1 h2 hX0 hX1).trans hd.card_S
      card_left := (f112ll_card_pCoreOf_P1'_of_tree hF hm hn h1 h2 hX0 hX1).trans hd.card_left
      elem_left := f112ll_isElemAbelian_pCoreOf_P1'_of_tree hF hm hn h1 h2 hX0 hX1 hd.elem_left
      lin_left := f112ll_isLin2Type_oTwoPrime_P1'_of_tree hF hm hn h1 h2 hX0 hX1 hd.lin_left
      indec_left :=
        f112ll_commutator_pCoreOf_P1'_of_tree hF hm hn h1 h2 hX0 hX1 hd.indec_left
      card_right := (f112ll_card_pCoreOf_P2'_of_tree hF hm hn h1 h2 hX0 hX1).trans hd.card_right
      elem_right := f112ll_isElemAbelian_pCoreOf_P2'_of_tree hF hm hn h1 h2 hX0 hX1 hd.elem_right
      lin_right := f112ll_isLin2Type_oTwoPrime_P2'_of_tree hF hm hn h1 h2 hX0 hX1 hd.lin_right
      indec_right :=
        f112ll_commutator_pCoreOf_P2'_of_tree hF hm hn h1 h2 hX0 hX1 hd.indec_right
      card_inf := (f112ll_card_pCoreOf_inf_of_tree hF hm hn h1 h2 hX0 hX1).trans hd.card_inf }

theorem f112ll_sp4qLocalData_of_tree {L1 L2 S : Subgroup H} {m n f : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2))
    {X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S)}
    (hX0 : X.vert 0 = baseA (f112Gold L1 L2 S)) (hX1 : X.vert 1 = baseB (f112Gold L1 L2 S))
    (hf : 2 ≤ f) (hd : Sp4qLocalData (X.L 0) (X.L 1) X.S f) :
    m = n ∧ Sp4qLocalData L1 L2 S n := by
  have hd' := f112ll_sp4qLocalData_oTwoPrime_of_tree hF hm hn h1 h2 hX0 hX1 hd
  have hfm : f = m := f112ll_eq_of_isLin2Type_oTwoPrime_P1' hF hm hn h1 h2 hf hd'.lin_left
  have hfn : f = n := f112ll_eq_of_isLin2Type_oTwoPrime_P2' hF hm hn h1 h2 hf hd'.lin_right
  subst hfm
  subst hfn
  have hV1 : TransferVertexLin (f112saP1' L1 L2 S) f :=
    { lin := hd'.lin_left
      abelian := by
        have h := hd'.elem_left.1
        rwa [pCoreOf_oTwoPrime] at h
      indec := by
        have h := hd'.indec_left
        rwa [pCoreOf_oTwoPrime] at h }
  have hV2 : TransferVertexLin (f112saP2' L1 L2 S) f :=
    { lin := hd'.lin_right
      abelian := by
        have h := hd'.elem_right.1
        rwa [pCoreOf_oTwoPrime] at h
      indec := by
        have h := hd'.indec_right
        rwa [pCoreOf_oTwoPrime] at h }
  have hT : S ⊓ f112saK L1 L2 S =
      pCoreOf 2 (f112saP1' L1 L2 S) ⊔ pCoreOf 2 (f112saP2' L1 L2 S) :=
    (f112ll_pCoreOf_sup_eq hF hm hn h1 h2).symm
  obtain ⟨hSK, hL1, hL2⟩ :=
    f112ll_le_K_and_eq_oTwoPrime_of_vertexLin hF hm hn h1 h2 hV1 hV2 hT
  refine ⟨rfl, ?_⟩
  rw [← hL1, ← hL2, inf_eq_left.mpr hSK] at hd'
  exact hd'

end CFSG.Quasithin.F112R.St84
