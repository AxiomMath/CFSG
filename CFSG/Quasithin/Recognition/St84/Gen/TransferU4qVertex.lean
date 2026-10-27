module

public import CFSG.Quasithin.Recognition.St84.Gen.TransferU4qBasic
public import CFSG.Quasithin.Recognition.St84.Gen.L2SectionBorel

import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalLocal
import CFSG.Quasithin.Recognition.St84.Gen.TransferU4qCore
import CFSG.Quasithin.Recognition.St84.Gen.TransferVertexLift
import CFSG.Quasithin.Recognition.St84.TransferVertex
import CFSG.Quasithin.Recognition.St84.TransferNormality
import CFSG.Quasithin.Recognition.St84.Gen.TreeLLBase
import CFSG.Quasithin.Recognition.St84.Gen.L2RankOne
import CFSG.Quasithin.Background.B6Defs
public import CFSG.CharacterTheory.Wreathed.BrauerWongSylowCentralizer
public import CFSG.CharacterTheory.Wreathed.OddKernelSylowQuotient
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.GroupTheory.QuasiDihedralFusion.InvolutionCentralizer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldAction
public import CFSG.Timmesfeld.RankOne.Defs
import CFSG.CGT.PushingUpLit.BHS.OffenderInternal
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldNaturalAction
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftBaumannDelOrigData
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDelBlockTools
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDelH0
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceCommon
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathGate5
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathGate6
import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points
import CFSG.Quasithin.Background.C1GNA7
import CFSG.Quasithin.Background.C1PackBasic
import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModPack28Proof
import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModS5Irr
import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModSecIrred
import CFSG.Quasithin.EmptyFaithful.Stellmacher.Steps
import CFSG.Quasithin.EmptyFaithful.SzF53BasE
import CFSG.Quasithin.EmptyFaithful.SzF53MSecB
import CFSG.Quasithin.H13.GoldschmidtC137BaumMain
import CFSG.Quasithin.H13.GoldschmidtC137Data
import CFSG.Quasithin.H13.GoldschmidtC137U33Hyp
import CFSG.Quasithin.H13.GoldschmidtC137U33S2Over
import CFSG.Quasithin.H13.GoldschmidtC137U33S2Self
import CFSG.Quasithin.H13.LinearOrders
import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Defs
import CFSG.Quasithin.Recognition.GoldschmidtFan86TArcEven
import CFSG.Quasithin.Recognition.Kleidman.F204.W2FFA5
import CFSG.Quasithin.Recognition.St84.AppTreeSAP1
import CFSG.Quasithin.Recognition.St84.PushUp
import CFSG.Quasithin.Vol2.Ch1Sec3A5Gen
import CFSG.Quasithin.Vol2.KGFact3312A5
import CFSG.RankThree.PartTwo.Sec15.Item153PushProofTools
import Certificates.Kernel.J4Count.Prim

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H] {L1 L2 S : Subgroup H} {m n f : ℕ}

private theorem u4q_commutator_pCoreOf_P1' (hd : U4qEdgeData L1 L2 S f) :
    ⁅pCoreOf 2 (f112saP1' L1 L2 S), oTwoPrime (f112saP1' L1 L2 S)⁆ =
      pCoreOf 2 (f112saP1' L1 L2 S) := by
  have h : ⁅pCoreOf 2 (oTwoPrime (f112saP1' L1 L2 S)), oTwoPrime (f112saP1' L1 L2 S)⁆ =
      pCoreOf 2 (oTwoPrime (f112saP1' L1 L2 S)) := U4qLocalData.blockU_left hd
  rwa [pCoreOf_oTwoPrime] at h

private theorem u4q_commutator_pCoreOf_P2' (hd : U4qEdgeData L1 L2 S f) :
    ⁅pCoreOf 2 (f112saP2' L1 L2 S), oTwoPrime (f112saP2' L1 L2 S)⁆ =
      pCoreOf 2 (f112saP2' L1 L2 S) := by
  have h : ⁅pCoreOf 2 (oTwoPrime (f112saP2' L1 L2 S)), oTwoPrime (f112saP2' L1 L2 S)⁆ =
      pCoreOf 2 (oTwoPrime (f112saP2' L1 L2 S)) := U4qLocalData.blockU_right hd
  rwa [pCoreOf_oTwoPrime] at h

theorem f112ll_u4q_oTwoPrime_le_L2 (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (h1 : IsL2Quot m (oTwoQuot ↥L1)) (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (hd : U4qEdgeData L1 L2 S f) :
    oTwoPrime (f112saP2' L1 L2 S) ≤ L2 := by
  have hR : Hyp111R L1 L2 S := hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2
  refine f112sa_oTwoPrime_P2'_le_L2_of_isL2Quot hF hR hn h2 hn
    (f112ll_isL2Quot_oTwoPrime_P2' hF hm hn h1 h2) ?_
  exact u4q_commutator_pCoreOf_P2' hd

theorem f112ll_u4q_exists_torus_right (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (h1 : IsL2Quot m (oTwoQuot ↥L1)) (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (hd : U4qEdgeData L1 L2 S f) :
    ∃ D : Subgroup H, D ≤ f112saX2 L1 L2 S ⊓ borelOf L2 S ∧
      D ≤ oTwoPrime (f112saP2' L1 L2 S) ⊓
        Subgroup.normalizer ((S ⊓ f112saK L1 L2 S : Subgroup H) : Set H) ∧
      Nat.card D = 2 ^ n - 1 := by
  classical
  obtain ⟨D, hD, hDcard⟩ := f112_exists_torus_X2 hF (by omega) h2
  have hR : Hyp111R L1 L2 S := hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2
  have hDX2 : D ≤ f112saX2 L1 L2 S := fun x hx => (Subgroup.mem_inf.mp (hD hx)).1
  have hDB : D ≤ borelOf L2 S := fun x hx => (Subgroup.mem_inf.mp (hD hx)).2
  have hDBigB : D ≤ bigB L1 L2 S :=
    hDB.trans (le_sup_right.trans le_sup_left)
  have hDLβ : D ≤ oTwoPrime (f112saP2' L1 L2 S) :=
    (hDX2.trans (f112sa_X2_le_oTwoRes L1 L2 S)).trans
      (f112sa_oTwoRes_le_oTwoPrime_P2'_of_isL2Quot hn h2)
  have hTL2 : S ⊓ f112saK L1 L2 S ≤ L2 :=
    (f112sa_T_le_oTwoPrime_P2'_of_hyp111R hF hR).trans
      (f112ll_u4q_oTwoPrime_le_L2 hF hm hn h1 h2 hd)
  have hT_eq : S ⊓ f112saK L1 L2 S = (S ⊓ L2) ⊓ f112saK L1 L2 S := by
    refine le_antisymm ?_ ?_
    · exact le_inf (le_inf inf_le_left hTL2) inf_le_right
    · exact le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have hDNT : D ≤ Subgroup.normalizer ((S ⊓ f112saK L1 L2 S : Subgroup H) : Set H) := by
    have h1' : D ≤ Subgroup.normalizer ((S ⊓ L2 : Subgroup H) : Set H) :=
      hDB.trans inf_le_right
    have h2' : D ≤ Subgroup.normalizer (f112saK L1 L2 S : Set H) :=
      hDBigB.trans (f112sa_bigB_le_normalizer_K hF)
    refine (le_inf h1' h2').trans ?_
    rw [hT_eq]
    exact Subgroup.inf_normalizer_le_normalizer_inf
  exact ⟨D, hD, le_inf hDLβ hDNT, hDcard⟩

theorem f112ll_u4q_pCoreOf_L2_le (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (h1 : IsL2Quot m (oTwoQuot ↥L1)) (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (hd : U4qEdgeData L1 L2 S f) :
    pCoreOf 2 L2 ≤ S ⊓ f112saK L1 L2 S := by
  classical
  let Lβ := oTwoPrime (f112saP2' L1 L2 S)
  intro c hc
  obtain ⟨hcS, -⟩ := Subgroup.mem_inf.mp (B6.pCoreOf_two_le_of_isSylowTwoOf hF.1.h2.sylow hc)
  have hSNβ : S ≤ Subgroup.normalizer (f112saP2' L1 L2 S : Set H) :=
    ((le_sup_right : S ≤ bigB L1 L2 S).trans
      (le_sup_right : bigB L1 L2 S ≤ f112P2 L1 L2 S)).trans
        (f112sa_P2_le_normalizer_P2' hF)
  have hcNβ : c ∈ Subgroup.normalizer (Lβ : Set H) := mem_normalizer_oTwoPrime (hSNβ hcS)
  have hN : Lβ ≤ Subgroup.normalizer ((pCoreOf 2 L2 ⊓ Lβ : Subgroup H) : Set H) := by
    refine (le_inf ?_ Subgroup.le_normalizer).trans Subgroup.inf_normalizer_le_normalizer_inf
    exact (f112ll_u4q_oTwoPrime_le_L2 hF hm hn h1 h2 hd).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L2)
  have h2grp : IsPGroup 2 ↥(pCoreOf 2 L2 ⊓ Lβ) :=
    ((CFSG.pCore_isPGroup (p := 2) (G := ↥L2)).map L2.subtype).to_le inf_le_left
  have hle : pCoreOf 2 L2 ⊓ Lβ ≤ pCoreOf 2 Lβ :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right hN h2grp
  have hcβ : c ∈ trivOTwoQuot Lβ := by
    refine mem_trivOTwoQuot.mpr ⟨hcNβ, fun l hl => ?_⟩
    have hlL2 : l ∈ L2 := f112ll_u4q_oTwoPrime_le_L2 hF hm hn h1 h2 hd hl
    have hlO : l * c⁻¹ * l⁻¹ ∈ pCoreOf 2 L2 :=
      (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L2 hlL2) c⁻¹).mp
          ((pCoreOf 2 L2).inv_mem hc)
    have hmem : c * l * c⁻¹ * l⁻¹ ∈ pCoreOf 2 L2 ⊓ Lβ := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have e : c * l * c⁻¹ * l⁻¹ = c * (l * c⁻¹ * l⁻¹) := by group
        rw [e]
        exact (pCoreOf 2 L2).mul_mem hc hlO
      · have hcl : c * l * c⁻¹ ∈ Lβ := (Subgroup.mem_normalizer_iff.mp hcNβ l).mp hl
        have e : c * l * c⁻¹ * l⁻¹ = (c * l * c⁻¹) * l⁻¹ := by group
        rw [e]
        exact Lβ.mul_mem hcl (Lβ.inv_mem hl)
    exact hle hmem
  exact f112ll_u4q_S_inf_trivOTwoQuot_right_le hF hm hn h1 h2 hd
    (Subgroup.mem_inf.mpr ⟨hcS, hcβ⟩)

theorem f112ll_u4q_pCoreOf_L1_le (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (h1 : IsL2Quot m (oTwoQuot ↥L1)) (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (hd : U4qEdgeData L1 L2 S f) :
    pCoreOf 2 L1 ≤ S ⊓ f112saK L1 L2 S := by
  classical
  let Lβ := oTwoPrime (f112saP2' L1 L2 S)
  let T := S ⊓ f112saK L1 L2 S
  intro c hc
  have hR : Hyp111R L1 L2 S := hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2
  obtain ⟨hcS, -⟩ := Subgroup.mem_inf.mp (B6.pCoreOf_two_le_of_isSylowTwoOf hF.1.h1.sylow hc)
  have hSNK : S ≤ Subgroup.normalizer (f112saK L1 L2 S : Set H) :=
    (le_sup_right : S ≤ bigB L1 L2 S).trans (f112sa_bigB_le_normalizer_K hF)
  have hSNβ : S ≤ Subgroup.normalizer (f112saP2' L1 L2 S : Set H) :=
    ((le_sup_right : S ≤ bigB L1 L2 S).trans
      (le_sup_right : bigB L1 L2 S ≤ f112P2 L1 L2 S)).trans
        (f112sa_P2_le_normalizer_P2' hF)
  have hcNβ : c ∈ Subgroup.normalizer (Lβ : Set H) := mem_normalizer_oTwoPrime (hSNβ hcS)
  have hcNT : c ∈ Subgroup.normalizer (T : Set H) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hcS, hSNK hcS⟩
  have hc2 : ∃ k, c ^ (2 ^ k) = 1 := by
    obtain ⟨k, hk⟩ := hF.1.h1.pgroup ⟨c, hcS⟩
    exact ⟨k, by simpa using congrArg (fun x : ↥S => (x : H)) hk⟩
  obtain ⟨D, hDX2B, hDLβNT, hDcard⟩ := f112ll_u4q_exists_torus_right hF hm hn h1 h2 hd
  have hDX2 : D ≤ f112saX2 L1 L2 S := fun x hx => (Subgroup.mem_inf.mp (hDX2B hx)).1
  have hDLβ : D ≤ Lβ := fun x hx => (Subgroup.mem_inf.mp (hDLβNT hx)).1
  have hDNT : D ≤ Subgroup.normalizer (T : Set H) :=
    fun x hx => (Subgroup.mem_inf.mp (hDLβNT hx)).2
  have hcD : ∀ d ∈ D, d * c * d⁻¹ * c⁻¹ ∈ T := by
    intro d hdD
    have hdX2 : d ∈ f112saX2 L1 L2 S := hDX2 hdD
    have hdK : d ∈ f112saK L1 L2 S :=
      (le_sup_right : f112saX2 L1 L2 S ≤ f112saK L1 L2 S) hdX2
    have hdBigB : d ∈ bigB L1 L2 S := f112sa_X2_le_bigB L1 L2 S hdX2
    have hconjO : d * c * d⁻¹ ∈ pCoreOf 2 L1 :=
      (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L1
          ((F1.bigB_le_normalizer_left hR).1 hdBigB)) c).mp hc
    have hconjS : d * c * d⁻¹ ∈ S :=
      (Subgroup.mem_inf.mp (B6.pCoreOf_two_le_of_isSylowTwoOf hF.1.h1.sylow hconjO)).1
    have hKcomm : c * d⁻¹ * c⁻¹ ∈ f112saK L1 L2 S :=
      (Subgroup.mem_normalizer_iff.mp (hSNK hcS) d⁻¹).mp ((f112saK L1 L2 S).inv_mem hdK)
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have e : d * c * d⁻¹ * c⁻¹ = (d * c * d⁻¹) * c⁻¹ := by group
      rw [e]
      exact S.mul_mem hconjS (S.inv_mem hcS)
    · have e : d * c * d⁻¹ * c⁻¹ = d * (c * d⁻¹ * c⁻¹) := by group
      rw [e]
      exact (f112saK L1 L2 S).mul_mem hdK hKcomm
  obtain ⟨t, htT, htc⟩ := exists_mul_mem_trivOTwoQuot_of_commutator_mem hn
    (f112ll_isL2Quot_oTwoPrime_P2' hF hm hn h1 h2)
    (f112sa_T_sylow_oTwoPrime_P2'_of_hyp111R hF hR) hDLβNT hDcard hc2 hcNβ hcNT hcD
  have htS : t ∈ S := (Subgroup.mem_inf.mp htT).1
  have htcT : t * c ∈ T :=
    f112ll_u4q_S_inf_trivOTwoQuot_right_le hF hm hn h1 h2 hd
      (Subgroup.mem_inf.mpr ⟨S.mul_mem htS hcS, htc⟩)
  have hcEq : c = t⁻¹ * (t * c) := by group
  rw [hcEq]
  exact T.mul_mem (T.inv_mem htT) htcT

theorem f112ll_u4q_L1_eq (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (h1 : IsL2Quot m (oTwoQuot ↥L1)) (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (hd : U4qEdgeData L1 L2 S f) :
    L1 = oTwoPrime (f112saP1' L1 L2 S) := by
  have hR : Hyp111R L1 L2 S := hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2
  refine f112sa_L1_eq_oTwoPrime_of_pCoreOf_le hF hR hm h1 hm
    (f112ll_isL2Quot_oTwoPrime_P1' hF hm hn h1 h2) ?_
    (f112ll_u4q_pCoreOf_L1_le hF hm hn h1 h2 hd)
  exact u4q_commutator_pCoreOf_P1' hd

theorem f112ll_u4q_L2_eq (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (h1 : IsL2Quot m (oTwoQuot ↥L1)) (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (hd : U4qEdgeData L1 L2 S f) :
    L2 = oTwoPrime (f112saP2' L1 L2 S) := by
  have hR : Hyp111R L1 L2 S := hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2
  refine f112sa_L2_eq_oTwoPrime_of_pCoreOf_le hF hR hn h2 hn
    (f112ll_isL2Quot_oTwoPrime_P2' hF hm hn h1 h2) ?_
    (f112ll_u4q_pCoreOf_L2_le hF hm hn h1 h2 hd)
  exact u4q_commutator_pCoreOf_P2' hd

end CFSG.Quasithin.F112R.St84

end
