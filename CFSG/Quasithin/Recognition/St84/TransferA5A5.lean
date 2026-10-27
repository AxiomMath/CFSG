module

public import CFSG.Quasithin.Recognition.St84.TransferSetup
public import CFSG.Quasithin.Recognition.St84.TransferInner
public import CFSG.Quasithin.Recognition.St84.TransferNormality
public import CFSG.Quasithin.Recognition.St84.TransferModule
public import CFSG.Quasithin.Recognition.St84.TransferVertex
public import CFSG.GroupTheory.CentralizerSup

import CFSG.Quasithin.Recognition.St84.Gen.TransferLL
public import CFSG.Dihedral.Glauberman.DicksonMaxB
public import CFSG.Quasithin.Background.C2
public import CFSG.Quasithin.Background.C2Bridge
public import CFSG.Quasithin.Background.C2Seven
public import CFSG.Quasithin.Background.C48Asm
public import CFSG.Quasithin.Background.E2Statements
public import CFSG.Quasithin.Recognition.Kleidman.F204.W2FFA5
public import CFSG.Quasithin.Recognition.St84.AppTreeL2
public import CFSG.Quasithin.Recognition.St84.AppTreeSAP2
public import CFSG.Quasithin.Vol2.Ch1Sec3A5Gen
public import CFSG.Quasithin.Vol2.KGFact3312A5
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.StronglyEmbedded.MatrixGroups.PSL2

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.GH74.QTGen4.DSGen4
open scoped Pointwise commutatorElement

variable {H : Type} [Group H] [Finite H]

theorem f112sa_pCoreOf_inf_centralizer_le_centralizer_oTwoRes_P1'
    {L1 L2 S : Subgroup H}
    (ho1 : oTwoRes L1 ≤ oTwoPrime (f112saP1' L1 L2 S))
    (hnat : NatSec (oTwoPrime (f112saP1' L1 L2 S))
      (pCoreOf 2 (f112saP1' L1 L2 S) ⊓
        Subgroup.centralizer (oTwoPrime (f112saP1' L1 L2 S) : Set H))
      (pCoreOf 2 (f112saP1' L1 L2 S)))
    {k : H} (hkX : k ∈ f112saX1 L1 L2 S) (hk3 : orderOf k = 3) :
    pCoreOf 2 (f112saP1' L1 L2 S) ⊓ Subgroup.centralizer ({k} : Set H) ≤
      Subgroup.centralizer (oTwoRes L1 : Set H) := by
  intro v hv
  obtain ⟨hvQ, hvC⟩ := Subgroup.mem_inf.mp hv
  have hkL : k ∈ oTwoPrime (f112saP1' L1 L2 S) :=
    ho1 (f112sa_X1_le_oTwoRes L1 L2 S hkX)
  have hcomm : ⁅v, k⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_centralizer_iff.mp hvC k (Set.mem_singleton k)).symm
  have hmemK : ⁅v, k⁆ ∈ pCoreOf 2 (f112saP1' L1 L2 S) ⊓
      Subgroup.centralizer (oTwoPrime (f112saP1' L1 L2 S) : Set H) := by
    rw [hcomm]
    exact Subgroup.one_mem _
  have hvcent : v ∈ Subgroup.centralizer
      (oTwoPrime (f112saP1' L1 L2 S) : Set H) :=
    (hnat k hkL hk3 v hvQ hmemK).2
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  exact Subgroup.mem_centralizer_iff.mp hvcent a (ho1 ha)

theorem f112sa_pCoreOf_inf_centralizer_le_centralizer_oTwoRes_P2'
    {L1 L2 S : Subgroup H}
    (ho2 : oTwoRes L2 ≤ oTwoPrime (f112saP2' L1 L2 S))
    (hnat : NatSec (oTwoPrime (f112saP2' L1 L2 S))
      (pCoreOf 2 (f112saP2' L1 L2 S) ⊓
        Subgroup.centralizer (oTwoPrime (f112saP2' L1 L2 S) : Set H))
      (pCoreOf 2 (f112saP2' L1 L2 S)))
    {k : H} (hkX : k ∈ f112saX2 L1 L2 S) (hk3 : orderOf k = 3) :
    pCoreOf 2 (f112saP2' L1 L2 S) ⊓ Subgroup.centralizer ({k} : Set H) ≤
      Subgroup.centralizer (oTwoRes L2 : Set H) := by
  have hX : k ∈ f112saX1 L2 L1 S := by
    simpa [f112saX1, f112saX2, bigB_comm] using hkX
  have ho2' : oTwoRes L2 ≤ oTwoPrime (f112saP1' L2 L1 S) := by
    simpa [f112saP1', f112saP2', f112saX1, f112saX2, bigB_comm] using ho2
  have hnat' : NatSec (oTwoPrime (f112saP1' L2 L1 S))
      (pCoreOf 2 (f112saP1' L2 L1 S) ⊓
        Subgroup.centralizer (oTwoPrime (f112saP1' L2 L1 S) : Set H))
      (pCoreOf 2 (f112saP1' L2 L1 S)) := by
    simpa [f112saP1', f112saP2', f112saX1, f112saX2, bigB_comm] using hnat
  have h := f112sa_pCoreOf_inf_centralizer_le_centralizer_oTwoRes_P1'
    (L1 := L2) (L2 := L1) ho2' hnat' hX hk3
  simpa [f112saP1', f112saP2', f112saX1, f112saX2, bigB_comm] using h

theorem f112saW_eq_bot_of_natSec {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2)
    (ho1 : oTwoRes L1 ≤ oTwoPrime (f112saP1' L1 L2 S))
    (ho2 : oTwoRes L2 ≤ oTwoPrime (f112saP2' L1 L2 S))
    (hnat1 : NatSec (oTwoPrime (f112saP1' L1 L2 S))
      (pCoreOf 2 (f112saP1' L1 L2 S) ⊓
        Subgroup.centralizer (oTwoPrime (f112saP1' L1 L2 S) : Set H))
      (pCoreOf 2 (f112saP1' L1 L2 S)))
    (hnat2 : NatSec (oTwoPrime (f112saP2' L1 L2 S))
      (pCoreOf 2 (f112saP2' L1 L2 S) ⊓
        Subgroup.centralizer (oTwoPrime (f112saP2' L1 L2 S) : Set H))
      (pCoreOf 2 (f112saP2' L1 L2 S))) :
    f112saW L1 L2 S = ⊥ := by
  obtain ⟨k1, hk1X, -, hk13, -⟩ := f112_exists_orderThree_X1 hF h1
  obtain ⟨k2, hk2X', -, hk23, -⟩ :=
    f112_exists_orderThree_X1 (L1 := L2) (L2 := L1) hF.symm h2
  have hk2X : k2 ∈ f112saX2 L1 L2 S := by
    simpa [f112saX1, f112saX2, bigB_comm] using hk2X'
  refine f112saW_eq_bot_of_centerOf_inf_centralizer_le hF
    (Subgroup.mem_sup_left hk1X) (Subgroup.mem_sup_right hk2X) ?_ ?_
  · exact f112sa_centerOf_inf_centralizer_le_of_pCoreOf_P1' hF
      (f112sa_pCoreOf_inf_centralizer_le_centralizer_oTwoRes_P1' ho1 hnat1 hk1X hk13)
  · exact f112sa_centerOf_inf_centralizer_le_of_pCoreOf_P2' hF
      (f112sa_pCoreOf_inf_centralizer_le_centralizer_oTwoRes_P2' ho2 hnat2 hk2X hk23)

theorem f112sa_mem_K_of_local {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S)
    (hW : f112saW L1 L2 S = ⊥)
    {e1 : oTwoQuot ↥(oTwoPrime (f112saP1' L1 L2 S)) ≃* alternatingGroup (Fin 5)}
    {e2 : oTwoQuot ↥(oTwoPrime (f112saP2' L1 L2 S)) ≃* alternatingGroup (Fin 5)}
    (hQ1ab : IsMulCommutative ↥(pCoreOf 2 (f112saP1' L1 L2 S)))
    (hQ1ind : ⁅pCoreOf 2 (f112saP1' L1 L2 S),
      oTwoPrime (f112saP1' L1 L2 S)⁆ = pCoreOf 2 (f112saP1' L1 L2 S))
    (hQ1index : (pCoreOf 2 (f112saP1' L1 L2 S) ⊓
      Subgroup.centralizer (oTwoPrime (f112saP1' L1 L2 S) : Set H)).relIndex
        (pCoreOf 2 (f112saP1' L1 L2 S)) = 16)
    (hQ1nat : NatSec (oTwoPrime (f112saP1' L1 L2 S))
      (pCoreOf 2 (f112saP1' L1 L2 S) ⊓
        Subgroup.centralizer (oTwoPrime (f112saP1' L1 L2 S) : Set H))
      (pCoreOf 2 (f112saP1' L1 L2 S)))
    (hQ2ab : IsMulCommutative ↥(pCoreOf 2 (f112saP2' L1 L2 S)))
    (hQ2ind : ⁅pCoreOf 2 (f112saP2' L1 L2 S),
      oTwoPrime (f112saP2' L1 L2 S)⁆ = pCoreOf 2 (f112saP2' L1 L2 S))
    (hQ2index : (pCoreOf 2 (f112saP2' L1 L2 S) ⊓
      Subgroup.centralizer (oTwoPrime (f112saP2' L1 L2 S) : Set H)).relIndex
        (pCoreOf 2 (f112saP2' L1 L2 S)) = 16)
    (hQ2nat : NatSec (oTwoPrime (f112saP2' L1 L2 S))
      (pCoreOf 2 (f112saP2' L1 L2 S) ⊓
        Subgroup.centralizer (oTwoPrime (f112saP2' L1 L2 S) : Set H))
      (pCoreOf 2 (f112saP2' L1 L2 S)))
    (hQ1le : pCoreOf 2 (f112saP1' L1 L2 S) ≤ oTwoPrime (f112saP1' L1 L2 S))
    (hQ2le : pCoreOf 2 (f112saP2' L1 L2 S) ≤ oTwoPrime (f112saP2' L1 L2 S))
    (hpCore2 : pCoreOf 2 (oTwoPrime (f112saP2' L1 L2 S)) =
      pCoreOf 2 (f112saP2' L1 L2 S))
    (hTsyl : IsSylowTwoOf (S ⊓ f112saK L1 L2 S) (oTwoPrime (f112saP2' L1 L2 S)))
    (hT : S ⊓ f112saK L1 L2 S = pCoreOf 2 (f112saP1' L1 L2 S) ⊔
      pCoreOf 2 (f112saP2' L1 L2 S))
    {c : H} (hcS : c ∈ S)
    (hcQ1 : ∀ l ∈ oTwoPrime (f112saP1' L1 L2 S),
      ⁅c, l⁆ ∈ pCoreOf 2 (f112saP1' L1 L2 S)) :
    c ∈ f112saK L1 L2 S := by
  classical
  have hSNα : S ≤ Subgroup.normalizer (f112saP1' L1 L2 S : Set H) := fun s hs =>
    f112sa_P1_le_normalizer_P1' hF ((le_sup_right : bigB L1 L2 S ≤ f112P1 L1 L2 S)
      ((le_sup_right : S ≤ bigB L1 L2 S) hs))
  have hSNβ : S ≤ Subgroup.normalizer (f112saP2' L1 L2 S : Set H) := fun s hs =>
    f112sa_P2_le_normalizer_P2' hF ((le_sup_right : bigB L1 L2 S ≤ f112P2 L1 L2 S)
      ((le_sup_right : S ≤ bigB L1 L2 S) hs))
  have hS2 : ∀ s ∈ S, ∃ m, s ^ 2 ^ m = 1 := fun s hs => by
    obtain ⟨m, hm⟩ := hF.1.h1.pgroup ⟨s, hs⟩
    exact ⟨m, by simpa using congrArg (fun x : ↥S => (x : H)) hm⟩
  have hAleT : pCoreOf 2 (f112saP1' L1 L2 S) ≤ S ⊓ f112saK L1 L2 S := hT ▸ le_sup_left
  refine f112sa_mem_K_of_steps hF (Hyp111R.of_hyp111 rankOneListedFacts hF.1) hW hT
    (fun s hs hsL => ?_) (fun s hs hsQ => ?_) (fun s hs hsL => ?_) hcS hcQ1
  · exact centralizes_of_twoPow_of_natSec e1 hQ1le
      ((oTwoPrime_le _).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)) hQ1ab hQ1ind
      hQ1index hQ1nat (hS2 s hs) (mem_normalizer_oTwoPrime (hSNα hs))
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ (hSNα hs)) hsL
  · obtain ⟨a, haQ, ha⟩ := exists_mul_inv_commutator_mem_pCore e2
      (mem_normalizer_oTwoPrime (hSNβ hs)) hTsyl hAleT (by rw [hpCore2, ← hT])
      (fun q hq => commutatorElement_eq_one_iff_mul_comm.mp (hsQ q hq))
    refine ⟨a, hAleT haQ, fun q hq => ?_, fun l hl => hpCore2 ▸ ha l hl⟩
    haveI : IsMulCommutative ↥(pCoreOf 2 (f112saP1' L1 L2 S)) := hQ1ab
    have hsC : s ∈ Subgroup.centralizer (pCoreOf 2 (f112saP1' L1 L2 S) : Set H) :=
      Subgroup.mem_centralizer_iff.mpr fun q hq =>
        (commutatorElement_eq_one_iff_mul_comm.mp (hsQ q hq)).symm
    have hsaC := (Subgroup.centralizer _).mul_mem hsC
      ((Subgroup.centralizer _).inv_mem (Subgroup.le_centralizer _ haQ))
    exact commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_centralizer_iff.mp hsaC q hq).symm
  · exact centralizes_of_twoPow_of_natSec e2 hQ2le
      ((oTwoPrime_le _).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)) hQ2ab hQ2ind
      hQ2index hQ2nat (hS2 s hs) (mem_normalizer_oTwoPrime (hSNβ hs))
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ (hSNβ hs)) hsL

theorem f112saW_eq_bot_of_transfer {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2)
    (hV1 : TransferVertexData (f112saP1' L1 L2 S))
    (hV2 : TransferVertexData (f112saP2' L1 L2 S)) :
    f112saW L1 L2 S = ⊥ :=
  f112saW_eq_bot_of_natSec hF h1 h2
    (f112sa_oTwoRes_le_oTwoPrime_P1' hF h1)
    (f112sa_oTwoRes_le_oTwoPrime_P2' hF h2) hV1.nat hV2.nat

theorem f112sa_mem_K_of_local_P2 {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S)
    (hW : f112saW L1 L2 S = ⊥)
    {e1 : oTwoQuot ↥(oTwoPrime (f112saP1' L1 L2 S)) ≃* alternatingGroup (Fin 5)}
    {e2 : oTwoQuot ↥(oTwoPrime (f112saP2' L1 L2 S)) ≃* alternatingGroup (Fin 5)}
    (hQ1ab : IsMulCommutative ↥(pCoreOf 2 (f112saP1' L1 L2 S)))
    (hQ1ind : ⁅pCoreOf 2 (f112saP1' L1 L2 S),
      oTwoPrime (f112saP1' L1 L2 S)⁆ = pCoreOf 2 (f112saP1' L1 L2 S))
    (hQ1index : (pCoreOf 2 (f112saP1' L1 L2 S) ⊓
      Subgroup.centralizer (oTwoPrime (f112saP1' L1 L2 S) : Set H)).relIndex
        (pCoreOf 2 (f112saP1' L1 L2 S)) = 16)
    (hQ1nat : NatSec (oTwoPrime (f112saP1' L1 L2 S))
      (pCoreOf 2 (f112saP1' L1 L2 S) ⊓
        Subgroup.centralizer (oTwoPrime (f112saP1' L1 L2 S) : Set H))
      (pCoreOf 2 (f112saP1' L1 L2 S)))
    (hQ2ab : IsMulCommutative ↥(pCoreOf 2 (f112saP2' L1 L2 S)))
    (hQ2ind : ⁅pCoreOf 2 (f112saP2' L1 L2 S),
      oTwoPrime (f112saP2' L1 L2 S)⁆ = pCoreOf 2 (f112saP2' L1 L2 S))
    (hQ2index : (pCoreOf 2 (f112saP2' L1 L2 S) ⊓
      Subgroup.centralizer (oTwoPrime (f112saP2' L1 L2 S) : Set H)).relIndex
        (pCoreOf 2 (f112saP2' L1 L2 S)) = 16)
    (hQ2nat : NatSec (oTwoPrime (f112saP2' L1 L2 S))
      (pCoreOf 2 (f112saP2' L1 L2 S) ⊓
        Subgroup.centralizer (oTwoPrime (f112saP2' L1 L2 S) : Set H))
      (pCoreOf 2 (f112saP2' L1 L2 S)))
    (hQ1le : pCoreOf 2 (f112saP1' L1 L2 S) ≤ oTwoPrime (f112saP1' L1 L2 S))
    (hQ2le : pCoreOf 2 (f112saP2' L1 L2 S) ≤ oTwoPrime (f112saP2' L1 L2 S))
    (hpCore1 : pCoreOf 2 (oTwoPrime (f112saP1' L1 L2 S)) =
      pCoreOf 2 (f112saP1' L1 L2 S))
    (hTsyl : IsSylowTwoOf (S ⊓ f112saK L1 L2 S) (oTwoPrime (f112saP1' L1 L2 S)))
    (hT : S ⊓ f112saK L1 L2 S = pCoreOf 2 (f112saP1' L1 L2 S) ⊔
      pCoreOf 2 (f112saP2' L1 L2 S))
    {c : H} (hcS : c ∈ S)
    (hcQ2 : ∀ l ∈ oTwoPrime (f112saP2' L1 L2 S),
      ⁅c, l⁆ ∈ pCoreOf 2 (f112saP2' L1 L2 S)) :
    c ∈ f112saK L1 L2 S := by
  have hW' : f112saW L2 L1 S = ⊥ := by
    rwa [show f112saW L2 L1 S = f112saW L1 L2 S from by
      simp only [f112saW, f112saK_comm]]
  have hK : f112saK L2 L1 S = f112saK L1 L2 S := f112saK_comm L1 L2 S
  have hT' : S ⊓ f112saK L2 L1 S =
      pCoreOf 2 (f112saP1' L2 L1 S) ⊔ pCoreOf 2 (f112saP2' L2 L1 S) := by
    rw [f112saK_comm L1 L2 S, ← f112saP2'_eq_P1'_swap L1 L2 S,
      f112saP2'_eq_P1'_swap L2 L1 S, sup_comm]
    exact hT
  have hTsyl' : IsSylowTwoOf (S ⊓ f112saK L2 L1 S)
      (oTwoPrime (f112saP2' L2 L1 S)) := by
    simpa [f112saK_comm L1 L2 S, f112saP2'_eq_P1'_swap L2 L1 S] using hTsyl
  have e1' : oTwoQuot ↥(oTwoPrime (f112saP1' L2 L1 S)) ≃* alternatingGroup (Fin 5) := by
    rw [← f112saP2'_eq_P1'_swap L1 L2 S]
    exact e2
  have e2' : oTwoQuot ↥(oTwoPrime (f112saP2' L2 L1 S)) ≃* alternatingGroup (Fin 5) := by
    rw [f112saP2'_eq_P1'_swap L2 L1 S]
    exact e1
  have hQ2ab' : IsMulCommutative ↥(pCoreOf 2 (f112saP1' L2 L1 S)) := by
    rw [show f112saP1' L2 L1 S = f112saP2' L1 L2 S from
      (f112saP2'_eq_P1'_swap L1 L2 S).symm]
    exact hQ2ab
  have hQ2ind' : ⁅pCoreOf 2 (f112saP1' L2 L1 S),
      oTwoPrime (f112saP1' L2 L1 S)⁆ = pCoreOf 2 (f112saP1' L2 L1 S) := by
    rw [show f112saP1' L2 L1 S = f112saP2' L1 L2 S from
      (f112saP2'_eq_P1'_swap L1 L2 S).symm]
    exact hQ2ind
  have hQ2index' : (pCoreOf 2 (f112saP1' L2 L1 S) ⊓
      Subgroup.centralizer (oTwoPrime (f112saP1' L2 L1 S) : Set H)).relIndex
        (pCoreOf 2 (f112saP1' L2 L1 S)) = 16 := by
    rw [show f112saP1' L2 L1 S = f112saP2' L1 L2 S from
      (f112saP2'_eq_P1'_swap L1 L2 S).symm]
    exact hQ2index
  have hQ2nat' : NatSec (oTwoPrime (f112saP1' L2 L1 S))
      (pCoreOf 2 (f112saP1' L2 L1 S) ⊓
        Subgroup.centralizer (oTwoPrime (f112saP1' L2 L1 S) : Set H))
      (pCoreOf 2 (f112saP1' L2 L1 S)) := by
    rw [show f112saP1' L2 L1 S = f112saP2' L1 L2 S from
      (f112saP2'_eq_P1'_swap L1 L2 S).symm]
    exact hQ2nat
  have hQ1ab' : IsMulCommutative ↥(pCoreOf 2 (f112saP2' L2 L1 S)) := by
    rw [show f112saP2' L2 L1 S = f112saP1' L1 L2 S from f112saP2'_eq_P1'_swap L2 L1 S]
    exact hQ1ab
  have hQ1ind' : ⁅pCoreOf 2 (f112saP2' L2 L1 S),
      oTwoPrime (f112saP2' L2 L1 S)⁆ = pCoreOf 2 (f112saP2' L2 L1 S) := by
    rw [show f112saP2' L2 L1 S = f112saP1' L1 L2 S from f112saP2'_eq_P1'_swap L2 L1 S]
    exact hQ1ind
  have hQ1index' : (pCoreOf 2 (f112saP2' L2 L1 S) ⊓
      Subgroup.centralizer (oTwoPrime (f112saP2' L2 L1 S) : Set H)).relIndex
        (pCoreOf 2 (f112saP2' L2 L1 S)) = 16 := by
    rw [show f112saP2' L2 L1 S = f112saP1' L1 L2 S from f112saP2'_eq_P1'_swap L2 L1 S]
    exact hQ1index
  have hQ1nat' : NatSec (oTwoPrime (f112saP2' L2 L1 S))
      (pCoreOf 2 (f112saP2' L2 L1 S) ⊓
        Subgroup.centralizer (oTwoPrime (f112saP2' L2 L1 S) : Set H))
      (pCoreOf 2 (f112saP2' L2 L1 S)) := by
    rw [show f112saP2' L2 L1 S = f112saP1' L1 L2 S from f112saP2'_eq_P1'_swap L2 L1 S]
    exact hQ1nat
  have hQ2le' : pCoreOf 2 (f112saP1' L2 L1 S) ≤ oTwoPrime (f112saP1' L2 L1 S) := by
    rw [show f112saP1' L2 L1 S = f112saP2' L1 L2 S from
      (f112saP2'_eq_P1'_swap L1 L2 S).symm]
    exact hQ2le
  have hQ1le' : pCoreOf 2 (f112saP2' L2 L1 S) ≤ oTwoPrime (f112saP2' L2 L1 S) := by
    rw [show f112saP2' L2 L1 S = f112saP1' L1 L2 S from f112saP2'_eq_P1'_swap L2 L1 S]
    exact hQ1le
  have hpCore1' : pCoreOf 2 (oTwoPrime (f112saP2' L2 L1 S)) =
      pCoreOf 2 (f112saP2' L2 L1 S) := by
    rw [show f112saP2' L2 L1 S = f112saP1' L1 L2 S from f112saP2'_eq_P1'_swap L2 L1 S]
    exact hpCore1
  have hcQ2' : ∀ l ∈ oTwoPrime (f112saP1' L2 L1 S),
      ⁅c, l⁆ ∈ pCoreOf 2 (f112saP1' L2 L1 S) := by
    rw [show f112saP1' L2 L1 S = f112saP2' L1 L2 S from
      (f112saP2'_eq_P1'_swap L1 L2 S).symm]
    exact hcQ2
  have h := f112sa_mem_K_of_local (L1 := L2) (L2 := L1) hF.symm hW'
    (e1 := e1') (e2 := e2') hQ2ab' hQ2ind' hQ2index' hQ2nat'
    hQ1ab' hQ1ind' hQ1index' hQ1nat' hQ2le' hQ1le' hpCore1'
    hTsyl' hT' hcS hcQ2'
  rwa [hK] at h

theorem f112sa_le_K_of_core_steps {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2)
    (hq1 : IsL2Quot 2 (oTwoQuot ↥(oTwoPrime (f112saP1' L1 L2 S))))
    (hq2 : IsL2Quot 2 (oTwoQuot ↥(oTwoPrime (f112saP2' L1 L2 S))))
    (hstep1 : ∀ c ∈ S, (∀ l ∈ oTwoPrime (f112saP1' L1 L2 S),
      ⁅c, l⁆ ∈ pCoreOf 2 (f112saP1' L1 L2 S)) → c ∈ f112saK L1 L2 S)
    (hstep2 : ∀ c ∈ S, (∀ l ∈ oTwoPrime (f112saP2' L1 L2 S),
      ⁅c, l⁆ ∈ pCoreOf 2 (f112saP2' L1 L2 S)) → c ∈ f112saK L1 L2 S) :
    S ≤ f112saK L1 L2 S :=
  f112sa_le_K_of_core_steps_of_isL2Quot hF le_rfl le_rfl h1 h2 le_rfl hq1 le_rfl hq2 hstep1 hstep2

theorem f112sa_le_K_of_transfer {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2)
    (hV1 : TransferVertexData (f112saP1' L1 L2 S))
    (hV2 : TransferVertexData (f112saP2' L1 L2 S))
    (hT : S ⊓ f112saK L1 L2 S =
      pCoreOf 2 (f112saP1' L1 L2 S) ⊔ pCoreOf 2 (f112saP2' L1 L2 S)) :
    S ≤ f112saK L1 L2 S := by
  classical
  have hW := f112saW_eq_bot_of_transfer hF h1 h2 hV1 hV2
  have hQ1le : pCoreOf 2 (f112saP1' L1 L2 S) ≤ oTwoPrime (f112saP1' L1 L2 S) := by
    rw [f112sa_oTwoPrime_eq_oTwoRes_sup_pCoreOf_P1' hF h1 hV1.quot]
    exact le_sup_right
  have hQ2le : pCoreOf 2 (f112saP2' L1 L2 S) ≤ oTwoPrime (f112saP2' L1 L2 S) := by
    rw [f112sa_oTwoPrime_eq_oTwoRes_sup_pCoreOf_P2' hF h2 hV2.quot]
    exact le_sup_right
  have hpCore1 := pCoreOf_oTwoPrime (f112saP1' L1 L2 S)
  have hpCore2 := pCoreOf_oTwoPrime (f112saP2' L1 L2 S)
  obtain ⟨e1a⟩ := hV1.quot
  obtain ⟨e1b⟩ := CFSG.Quasithin.F112J2.nonempty_psl_four_equiv_alt5
  obtain ⟨e2a⟩ := hV2.quot
  obtain ⟨e2b⟩ := CFSG.Quasithin.F112J2.nonempty_psl_four_equiv_alt5
  refine f112sa_le_K_of_core_steps hF h1 h2 hV1.quot hV2.quot ?_ ?_
  · intro c hcS hcQ
    exact f112sa_mem_K_of_local hF hW
      (e1 := e1a.trans e1b) (e2 := e2a.trans e2b)
      hV1.abelian hV1.indec hV1.index hV1.nat
      hV2.abelian hV2.indec hV2.index hV2.nat
      hQ1le hQ2le hpCore2 (f112sa_T_sylow_oTwoPrime_P2' hF) hT hcS hcQ
  · intro c hcS hcQ
    exact f112sa_mem_K_of_local_P2 hF hW
      (e1 := e1a.trans e1b) (e2 := e2a.trans e2b)
      hV1.abelian hV1.indec hV1.index hV1.nat
      hV2.abelian hV2.indec hV2.index hV2.nat
      hQ1le hQ2le hpCore1 (f112sa_T_sylow_oTwoPrime_P1' hF) hT hcS hcQ

end CFSG.Quasithin.F112R.St84
