module

public import CFSG.Quasithin.Recognition.St84.Gen.TreeLLBase
public import CFSG.Quasithin.Recognition.St84.Gen.TransferLL
public import CFSG.Quasithin.Recognition.St84.Gen.L3qAmalDefs

import CFSG.Quasithin.Recognition.St84.Gen.L2RankOne
import CFSG.Quasithin.Recognition.St84.Gen.Sec7EvenGen
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

theorem TransferVertexLin.of_isLin2Type_of_card {E : Subgroup H} {f : ℕ}
    (hL : IsLin2Type (oTwoPrime E) f) (hc : Nat.card (pCoreOf 2 E) = 2 ^ (2 * f)) :
    TransferVertexLin E f := by
  classical
  have hlin : IsLin2Type (oTwoPrime E) f := hL
  obtain ⟨F, hFld, hFt, hFcard, -, -, -, β, hβs, -, -⟩ := hL
  letI := hFld
  letI := hFt
  have hFcard' : Nat.card F = 2 ^ f := by
    rw [Nat.card_eq_fintype_card, hFcard]
  have hcod : Nat.card (Multiplicative (Fin 2 → F)) = 2 ^ (2 * f) := by
    change Nat.card (Fin 2 → F) = 2 ^ (2 * f)
    rw [Nat.card_fun, hFcard', Nat.card_fin, ← pow_mul]
    congr 1
    omega
  have hsurjcard : 2 ^ (2 * f) ≤ Nat.card ↥(blockU (oTwoPrime E)) := by
    rw [← hcod]
    exact Nat.card_le_card_of_surjective β hβs
  have hUle : blockU (oTwoPrime E) ≤ pCoreOf 2 E := by
    have h := (Subgroup.le_normalizer_iff_commutator_le_left
      (K := pCoreOf 2 (oTwoPrime E))).mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (oTwoPrime E))
    simpa [blockU, blockQ, pCoreOf_oTwoPrime E] using h
  have hUQ : blockU (oTwoPrime E) = pCoreOf 2 E := by
    refine Subgroup.eq_of_le_of_card_ge hUle ?_
    rw [hc]
    exact hsurjcard
  have hindec : ⁅pCoreOf 2 E, oTwoPrime E⁆ = pCoreOf 2 E := by
    simpa [blockU, blockQ, pCoreOf_oTwoPrime E] using hUQ
  have habel : IsMulCommutative ↥(pCoreOf 2 E) := by
    have hcard : Nat.card ↥(blockU (oTwoPrime E)) =
        Nat.card (Multiplicative (Fin 2 → F)) := by
      rw [hUQ, hc, hcod]
    have hβinj : Function.Injective β :=
      Function.Surjective.injective_of_finite (Finite.card_eq.mp hcard).some hβs
    let eQ : ↥(blockU (oTwoPrime E)) ≃* ↥(pCoreOf 2 E) := MulEquiv.subgroupCongr hUQ
    let φ : ↥(pCoreOf 2 E) →* Multiplicative (Fin 2 → F) := β.comp eQ.symm.toMonoidHom
    have hφinj : Function.Injective φ := hβinj.comp eQ.symm.injective
    exact IsMulCommutative.of_comm fun x y => hφinj (by rw [map_mul, map_mul, mul_comm])
  exact ⟨hlin, habel, hindec⟩

theorem f112ll_l3qLocalData_oTwoPrime_of_tree {L1 L2 S : Subgroup H} {m n f : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2))
    {X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S)}
    (hX0 : X.vert 0 = baseA (f112Gold L1 L2 S))
    (hX1 : X.vert 1 = baseB (f112Gold L1 L2 S))
    (hd : L3qLocalData (X.L 0) (X.L 1) X.S f) :
    L3qLocalData (oTwoPrime (f112saP1' L1 L2 S)) (oTwoPrime (f112saP2' L1 L2 S))
      (S ⊓ f112saK L1 L2 S) f :=
  { card_S := (f112ll_card_S_inf_K_of_tree hF hm hn h1 h2 hX0 hX1).trans hd.card_S
    card_left := (f112ll_card_pCoreOf_P1'_of_tree hF hm hn h1 h2 hX0 hX1).trans hd.card_left
    lin_left := f112ll_isLin2Type_oTwoPrime_P1'_of_tree hF hm hn h1 h2 hX0 hX1 hd.lin_left
    card_right := (f112ll_card_pCoreOf_P2'_of_tree hF hm hn h1 h2 hX0 hX1).trans hd.card_right
    lin_right := f112ll_isLin2Type_oTwoPrime_P2'_of_tree hF hm hn h1 h2 hX0 hX1 hd.lin_right
    card_inf := (f112ll_card_pCoreOf_inf_of_tree hF hm hn h1 h2 hX0 hX1).trans hd.card_inf }

theorem f112ll_transferVertexLin_of_tree {L1 L2 S : Subgroup H} {m n f : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2))
    {X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S)}
    (hX0 : X.vert 0 = baseA (f112Gold L1 L2 S))
    (hX1 : X.vert 1 = baseB (f112Gold L1 L2 S))
    (hd : L3qLocalData (X.L 0) (X.L 1) X.S f) :
    TransferVertexLin (f112saP1' L1 L2 S) f ∧ TransferVertexLin (f112saP2' L1 L2 S) f ∧
      S ⊓ f112saK L1 L2 S =
        pCoreOf 2 (f112saP1' L1 L2 S) ⊔ pCoreOf 2 (f112saP2' L1 L2 S) := by
  have hd' := f112ll_l3qLocalData_oTwoPrime_of_tree hF hm hn h1 h2 hX0 hX1 hd
  refine ⟨?_, ?_, ?_⟩
  · exact TransferVertexLin.of_isLin2Type_of_card hd'.lin_left (by
      rw [← pCoreOf_oTwoPrime (f112saP1' L1 L2 S)]
      exact hd'.card_left)
  · exact TransferVertexLin.of_isLin2Type_of_card hd'.lin_right (by
      rw [← pCoreOf_oTwoPrime (f112saP2' L1 L2 S)]
      exact hd'.card_right)
  · exact (f112ll_pCoreOf_sup_eq hF hm hn h1 h2).symm

theorem f112ll_l3qLocalData_of_tree {L1 L2 S : Subgroup H} {m n f : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2))
    {X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S)}
    (hX0 : X.vert 0 = baseA (f112Gold L1 L2 S)) (hX1 : X.vert 1 = baseB (f112Gold L1 L2 S))
    (hf : 2 ≤ f) (hd : L3qLocalData (X.L 0) (X.L 1) X.S f) :
    m = n ∧ L3qLocalData L1 L2 S n := by
  have hd' := f112ll_l3qLocalData_oTwoPrime_of_tree hF hm hn h1 h2 hX0 hX1 hd
  have hfm : f = m := f112ll_eq_of_isLin2Type_oTwoPrime_P1' hF hm hn h1 h2 hf hd'.lin_left
  have hfn : f = n := f112ll_eq_of_isLin2Type_oTwoPrime_P2' hF hm hn h1 h2 hf hd'.lin_right
  subst hfm
  subst hfn
  obtain ⟨hV1, hV2, hT⟩ := f112ll_transferVertexLin_of_tree hF hm hn h1 h2 hX0 hX1 hd
  obtain ⟨hSK, hL1, hL2⟩ :=
    f112ll_le_K_and_eq_oTwoPrime_of_vertexLin hF hm hn h1 h2 hV1 hV2 hT
  refine ⟨rfl, ?_⟩
  rw [← hL1, ← hL2, inf_eq_left.mpr hSK] at hd'
  exact hd'

theorem f112ll_l3qLocalData_of_even_singularity {L1 L2 S : Subgroup H} {m n s : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (hs : IsSingularity (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S) s) (hev : Even s) :
    m = n ∧ L3qLocalData L1 L2 S n := by
  have hR : Hyp111R L1 L2 S := hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2
  obtain ⟨X, hX0, hX1⟩ := f112ll_exists_setup_baseEdge hF hm hn h1 h2
  have hX0n : X.n 0 = m := by
    rw [Setup.n, hX0]
    simpa using f112_nOf_alpha_of_isL2Quot hR (by omega) h1 (1 : (f112Gold L1 L2 S).Universal)
  obtain ⟨-, -, hd⟩ :=
    X.even_singularity_gen (f112ll_charTwoStab hF hm hn h1 h2) hs hev (hX0n ▸ hm)
  rw [hX0n] at hd
  exact f112ll_l3qLocalData_of_tree hF hm hn h1 h2 hX0 hX1 hm hd

end CFSG.Quasithin.F112R.St84
