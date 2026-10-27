module

public import CFSG.Quasithin.Recognition.St84.Gen.G2qVertexData
public import CFSG.Quasithin.Recognition.St84.Gen.TreeLLBase
public import CFSG.Quasithin.Recognition.St84.Gen.TransferLL
public import Certificates.Certificate3951
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117

import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalIndec
import CFSG.Quasithin.Recognition.St84.Gen.TransportG2q
import CFSG.Quasithin.Recognition.St84.Gen.TransferG2q
import CFSG.Quasithin.Recognition.St84.Gen.TransferEdgeHyp
import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalVertexTwo
import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalVertexOneTransport
import CFSG.Quasithin.Recognition.St84.Gen.TransportG2qSwap
import CFSG.Quasithin.Recognition.St84.TransferNormality
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

theorem f112ll_g2qLocalData_of_vertexData {L1 L2 S : Subgroup H} {m n f : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n) (hmn : ¬ (m = 2 ∧ n = 2))
    (h1 : IsL2Quot m (oTwoQuot ↥L1)) (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (hd : G2qVertexData (oTwoPrime (f112saP1' L1 L2 S)) (oTwoPrime (f112saP2' L1 L2 S))
      (S ⊓ f112saK L1 L2 S) f) : m = n ∧ G2qLocalData L1 L2 S n := by
  obtain ⟨hfm, hfn⟩ := f112ll_g2q_eq_of_localData hF hm hn h1 h2 hd.toG2qLocalData
  have h1' : IsL2Quot f (oTwoQuot ↥(oTwoPrime (f112saP1' L1 L2 S))) := by
    rw [hfm]
    exact f112ll_isL2Quot_oTwoPrime_P1' hF hm hn h1 h2
  have h2' : IsL2Quot f (oTwoQuot ↥(oTwoPrime (f112saP2' L1 L2 S))) := by
    rw [hfn]
    exact f112ll_isL2Quot_oTwoPrime_P2' hF hm hn h1 h2
  have hf3 : 3 ≤ f := by
    have hf2 : f ≠ 2 := fun h => hmn ⟨by omega, by omega⟩
    omega
  have hH : Hyp111 (oTwoPrime (f112saP1' L1 L2 S)) (oTwoPrime (f112saP2' L1 L2 S))
      (S ⊓ f112saK L1 L2 S) := f112ll_hyp111_edge hF hm hn h1 h2
  obtain ⟨K, hField, hFinite, hCharP, hK, ψ₂, hψ₂S, hψ₂Q⟩ :=
    hd.toG2qLocalData.exists_mulEquiv_vertexTwo hf3 hH h1' h2'
      (hd.toG2qLocalData.commutator_pCoreOf_right hf3 hH h1' h2')
  letI : Field K := hField
  letI : Finite K := hFinite
  letI : CharP K 2 := hCharP
  obtain ⟨J, hJ⟩ := hd.toG2qLocalData.exists_torus_left_of_vertexTwo (by omega) hH
    h1' h2' hK ψ₂ hψ₂S hψ₂Q
  exact f112ll_g2qLocalData_of_edgeData hF hm hn h1 h2
    (G2qEdgeData.of_vertexData hf3 hH h1' h2' hd ⟨J, hJ⟩)

theorem f112ll_g2qLocalData_of_tree {L1 L2 S : Subgroup H} {m n f : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n) (hmn : ¬ (m = 2 ∧ n = 2))
    (h1 : IsL2Quot m (oTwoQuot ↥L1)) (h2 : IsL2Quot n (oTwoQuot ↥L2))
    {X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S)}
    (hX0 : X.vert 0 = baseA (f112Gold L1 L2 S)) (hX1 : X.vert 1 = baseB (f112Gold L1 L2 S))
    (hd : G2qVertexData (X.L 0) (X.L 1) X.S f) : m = n ∧ G2qLocalData L1 L2 S n :=
  f112ll_g2qLocalData_of_vertexData hF hm hn hmn h1 h2
    (f112ll_g2qVertexData_oTwoPrime_of_tree hF hm hn h1 h2 hX0 hX1 hd)

theorem f112ll_g2qLocalData_of_vertexData_swap {L1 L2 S : Subgroup H} {m n f : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n) (hmn : ¬ (m = 2 ∧ n = 2))
    (h1 : IsL2Quot m (oTwoQuot ↥L1)) (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (hd : G2qVertexData (oTwoPrime (f112saP2' L1 L2 S)) (oTwoPrime (f112saP1' L1 L2 S))
      (S ⊓ f112saK L1 L2 S) f) : m = n ∧ G2qLocalData L2 L1 S n := by
  have hd' : G2qVertexData (oTwoPrime (f112saP1' L2 L1 S)) (oTwoPrime (f112saP2' L2 L1 S))
      (S ⊓ f112saK L2 L1 S) f := by
    rw [f112saP1'_eq_P2'_swap L2 L1 S, f112saP2'_eq_P1'_swap L2 L1 S,
      f112saK_comm L1 L2 S]
    exact hd
  obtain ⟨hnm, hloc⟩ := f112ll_g2qLocalData_of_vertexData hF.symm hn hm
    (by rintro ⟨hn2, hm2⟩; exact hmn ⟨hm2, hn2⟩) h2 h1 hd'
  refine ⟨hnm.symm, ?_⟩
  rwa [← hnm] at hloc

theorem f112ll_g2qLocalData_of_tree_swap {L1 L2 S : Subgroup H} {m n f : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n) (hmn : ¬ (m = 2 ∧ n = 2))
    (h1 : IsL2Quot m (oTwoQuot ↥L1)) (h2 : IsL2Quot n (oTwoQuot ↥L2))
    {X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S)}
    (hX0 : X.vert 0 = baseA (f112Gold L1 L2 S)) (hX1 : X.vert 1 = baseB (f112Gold L1 L2 S))
    (hd : G2qVertexData (X.L 1) (X.L 0) X.S f) : m = n ∧ G2qLocalData L2 L1 S n :=
  f112ll_g2qLocalData_of_vertexData_swap hF hm hn hmn h1 h2
    (f112ll_g2qVertexData_oTwoPrime_of_tree_swap hF hm hn h1 h2 hX0 hX1 hd)

end CFSG.Quasithin.F112R.St84

end
