module

public import CFSG.Quasithin.Recognition.St84.Gen.TransferU4qBasic

import CFSG.Quasithin.Recognition.St84.Gen.TransferU4qModule
import CFSG.Quasithin.Recognition.St84.Gen.TransferU4qCore
import CFSG.Quasithin.Recognition.St84.Gen.TransferU4qVertex
import CFSG.Quasithin.Recognition.St84.Gen.TransferVertexLift
import CFSG.Quasithin.Recognition.St84.Gen.TransferL2OuterTorus
import CFSG.Quasithin.Recognition.St84.Gen.TransferEdgeHyp
import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalTorus
import CFSG.Quasithin.Recognition.St84.Gen.CoprimeLift
import CFSG.Quasithin.Recognition.St84.Gen.TransferL2Torus
import CFSG.Quasithin.Recognition.St84.Gen.TreeLLBase
import CFSG.Quasithin.Recognition.St84.Gen.L2RankOne
import CFSG.Quasithin.Recognition.St84.TransferNormality
import CFSG.Quasithin.Recognition.St84.EdgeStabB
public import CFSG.CharacterTheory.Wreathed.BrauerWongSylowCentralizer
public import CFSG.CharacterTheory.Wreathed.OddKernelSylowQuotient
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.GroupTheory.QuasiDihedralFusion.InvolutionCentralizer
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

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {H : Type} [Group H] [Finite H] {L1 L2 S : Subgroup H} {m n f : ℕ}


private theorem le_card_inf_of_mul_card_sup_le (A N B : Subgroup H) (q : ℕ)
    (hAN : A ≤ Subgroup.normalizer (N : Set H)) (hAB : A ≤ B) (hNB : N ≤ B)
    (hcard : Nat.card A * Nat.card N = Nat.card B * q) :
    q ≤ Nat.card ↥(A ⊓ N) := by
  have hprod :=
    CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer hAN
  have hle : Nat.card ↥(A ⊔ N) ≤ Nat.card B := Subgroup.card_le_of_le (sup_le hAB hNB)
  have hqle : q * Nat.card B ≤ Nat.card ↥(A ⊓ N) * Nat.card B := by
    calc q * Nat.card B = Nat.card B * q := by ring
      _ = Nat.card A * Nat.card N := hcard.symm
      _ = Nat.card ↥(A ⊔ N) * Nat.card ↥(A ⊓ N) := hprod.symm
      _ ≤ Nat.card B * Nat.card ↥(A ⊓ N) := Nat.mul_le_mul_right _ hle
      _ = Nat.card ↥(A ⊓ N) * Nat.card B := by ring
  exact Nat.le_of_mul_le_mul_right hqle Nat.card_pos

theorem f112ll_u4q_le_K_of_normal_right (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (h1 : IsL2Quot m (oTwoQuot ↥L1)) (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (hd : U4qEdgeData L1 L2 S f) (hB : (S.subgroupOf (S ⊔ borelOf L2 S)).Normal) :
    S ≤ f112saK L1 L2 S := by
  intro c hcS
  let Lβ := oTwoPrime (f112saP2' L1 L2 S)
  let T := S ⊓ f112saK L1 L2 S
  have hR : Hyp111R L1 L2 S := hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2
  obtain ⟨D, hDX2B2, hDLβT, hDcard⟩ :=
    f112ll_u4q_exists_torus_right hF hm hn h1 h2 hd
  have hDB2 : D ≤ borelOf L2 S := hDX2B2.trans inf_le_right
  have hDX2 : D ≤ f112saX2 L1 L2 S := hDX2B2.trans inf_le_left
  have hSsup : S ⊔ borelOf L2 S ≤ Subgroup.normalizer (S : Set H) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mp hB
  have hDT : D ≤ Subgroup.normalizer (T : Set H) := hDLβT.trans inf_le_right
  have hcNT : c ∈ Subgroup.normalizer (T : Set H) := by
    have h := (f112sa_bigB_le_normalizer_K hF).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (f112saK L1 L2 S))
    rw [show T = pCoreOf 2 (f112saK L1 L2 S) from
      (f112ll_pCoreOf_K_eq hF hm hn h1 h2).symm]
    exact h ((le_sup_right : S ≤ bigB L1 L2 S) hcS)
  have hcLβ : c ∈ Subgroup.normalizer (Lβ : Set H) :=
    mem_normalizer_oTwoPrime
      (((le_sup_right : S ≤ bigB L1 L2 S).trans
        (le_sup_right : bigB L1 L2 S ≤ f112P2 L1 L2 S)).trans
          (f112sa_P2_le_normalizer_P2' hF) hcS)
  have hc2 : ∃ k, c ^ (2 ^ k) = 1 := by
    obtain ⟨k, hk⟩ := hF.1.h1.pgroup ⟨c, hcS⟩
    exact ⟨k, by simpa using congrArg (fun x : ↥S => (x : H)) hk⟩
  have hcomm : ∀ d ∈ D, d * c * d⁻¹ * c⁻¹ ∈ T := by
    intro d hdD
    have hdK : d ∈ f112saK L1 L2 S :=
      (le_sup_right : f112saX2 L1 L2 S ≤ f112saK L1 L2 S) (hDX2 hdD)
    have hcNK : c ∈ Subgroup.normalizer (f112saK L1 L2 S : Set H) :=
      f112sa_bigB_le_normalizer_K hF ((le_sup_right : S ≤ bigB L1 L2 S) hcS)
    have hdS : d * c * d⁻¹ ∈ S :=
      (Subgroup.mem_normalizer_iff.mp (hSsup (Subgroup.mem_sup_right (hDB2 hdD))) c).mp hcS
    have hcdK : c * d * c⁻¹ ∈ f112saK L1 L2 S :=
      (Subgroup.mem_normalizer_iff.mp hcNK d).mp hdK
    refine Subgroup.mem_inf.mpr ⟨S.mul_mem hdS (S.inv_mem hcS), ?_⟩
    have hinv : c * d * c⁻¹ * d⁻¹ ∈ f112saK L1 L2 S :=
      (f112saK L1 L2 S).mul_mem hcdK ((f112saK L1 L2 S).inv_mem hdK)
    have hinv' : (c * d * c⁻¹ * d⁻¹)⁻¹ ∈ f112saK L1 L2 S :=
      (f112saK L1 L2 S).inv_mem hinv
    have he : (c * d * c⁻¹ * d⁻¹)⁻¹ = d * c * d⁻¹ * c⁻¹ := by group
    rwa [he] at hinv'
  obtain ⟨t, htT, htc⟩ := exists_mul_mem_trivOTwoQuot_of_commutator_mem hn
    (f112ll_isL2Quot_oTwoPrime_P2' hF hm hn h1 h2)
    (f112sa_T_sylow_oTwoPrime_P2'_of_hyp111R hF hR) hDLβT hDcard hc2 hcLβ hcNT hcomm
  have htcT : t * c ∈ T :=
    f112ll_u4q_S_inf_trivOTwoQuot_right_le hF hm hn h1 h2 hd
      (Subgroup.mem_inf.mpr
        ⟨S.mul_mem ((inf_le_left : T ≤ S) htT) hcS, htc⟩)
  have hceq : c = t⁻¹ * (t * c) := by group
  rw [hceq]
  exact (f112saK L1 L2 S).mul_mem
    ((f112saK L1 L2 S).inv_mem ((inf_le_right : T ≤ f112saK L1 L2 S) htT))
    ((inf_le_right : T ≤ f112saK L1 L2 S) htcT)

private theorem u4q_inf_L1_eq_T (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (h1 : IsL2Quot m (oTwoQuot ↥L1)) (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (hd : U4qEdgeData L1 L2 S f) :
    S ⊓ L1 = S ⊓ f112saK L1 L2 S := by
  let Lα := oTwoPrime (f112saP1' L1 L2 S)
  let T := S ⊓ f112saK L1 L2 S
  have hR : Hyp111R L1 L2 S := hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2
  have hL1 : L1 = Lα := f112ll_u4q_L1_eq hF hm hn h1 h2 hd
  have hTleLα : T ≤ Lα := f112sa_T_le_oTwoPrime_P1'_of_hyp111R hF hR
  have hSylα : IsSylowTwoOf T Lα := f112sa_T_sylow_oTwoPrime_P1'_of_hyp111R hF hR
  have hTle : T ≤ S ⊓ L1 := by
    refine le_inf inf_le_left ?_
    rw [hL1]
    exact hTleLα
  have hSyl1 : IsSylowTwoOf T L1 := by rw [hL1]; exact hSylα
  exact hSyl1.eq_of_le hTle inf_le_right (hF.1.h1.pgroup.to_le inf_le_left)

private theorem u4q_borelOf_L1_eq (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (h1 : IsL2Quot m (oTwoQuot ↥L1)) (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (hd : U4qEdgeData L1 L2 S f) :
    borelOf L1 S = L1 ⊓ Subgroup.normalizer
      ((S ⊓ f112saK L1 L2 S : Subgroup H) : Set H) := by
  rw [borelOf, u4q_inf_L1_eq_T hF hm hn h1 h2 hd]

private theorem u4q_S_le_normalizer_T (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (h1 : IsL2Quot m (oTwoQuot ↥L1)) (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    S ≤ Subgroup.normalizer ((S ⊓ f112saK L1 L2 S : Subgroup H) : Set H) := by
  intro s hs
  have h := (f112sa_bigB_le_normalizer_K hF).trans
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (f112saK L1 L2 S))
  rw [show S ⊓ f112saK L1 L2 S = pCoreOf 2 (f112saK L1 L2 S) from
    (f112ll_pCoreOf_K_eq hF hm hn h1 h2).symm]
  exact h ((le_sup_right : S ≤ bigB L1 L2 S) hs)

private theorem u4q_card_bigB_inf_Lα (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (h1 : IsL2Quot m (oTwoQuot ↥L1)) (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (hd : U4qEdgeData L1 L2 S f) :
    Nat.card ↥(bigB (oTwoPrime (f112saP1' L1 L2 S)) (oTwoPrime (f112saP2' L1 L2 S))
      (S ⊓ f112saK L1 L2 S) ⊓ oTwoPrime (f112saP1' L1 L2 S)) =
      Nat.card ↥(S ⊓ f112saK L1 L2 S) * (2 ^ f - 1) := by
  let Lα := oTwoPrime (f112saP1' L1 L2 S)
  let Lβ := oTwoPrime (f112saP2' L1 L2 S)
  let T := S ⊓ f112saK L1 L2 S
  have hR : Hyp111R L1 L2 S := hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2
  have hedge : Hyp111 Lα Lβ T := f112ll_hyp111_edge hF hm hn h1 h2
  have hSedge : Nat.card ↥T = 2 ^ (6 * f) := f112ll_u4q_card_T hF hm hn h1 h2 hd
  have heq : f = m ∧ n = 2 * f := f112ll_u4q_eq_of_localData hF hm hn h1 h2 hd
  have hTleLα : T ≤ Lα := f112sa_T_le_oTwoPrime_P1'_of_hyp111R hF hR
  have hSylα : IsSylowTwoOf T Lα := f112sa_T_sylow_oTwoPrime_P1'_of_hyp111R hF hR
  have hBnorm : bigB Lα Lβ T ≤
      Subgroup.normalizer (Lα : Set H) ⊓ Subgroup.normalizer (Lβ : Set H) ⊓
        Subgroup.normalizer (T : Set H) :=
    U4qLocalData.bigB_le_normalizer (G := H) hedge hd hSedge
  have hNαeq : bigB Lα Lβ T ⊓ Lα = Lα ⊓ Subgroup.normalizer (T : Set H) := by
    refine le_antisymm
      (le_inf inf_le_right ((inf_le_left.trans hBnorm).trans inf_le_right)) ?_
    have hBα : borelOf Lα T ≤ bigB Lα Lβ T := by
      rw [bigB]
      exact le_sup_left.trans le_sup_left
    have : Lα ⊓ Subgroup.normalizer (T : Set H) = borelOf Lα T := by
      rw [borelOf, inf_eq_left.mpr hTleLα]
    rw [this]
    exact le_inf hBα (CFSG.Quasithin.F1.borelOf_le Lα T)
  have hqα : IsL2Quot m (oTwoQuot ↥Lα) := f112ll_isL2Quot_oTwoPrime_P1' hF hm hn h1 h2
  have hrel := relIndex_normalizer_of_isL2Quot (L := Lα) (T := T) (by omega) hqα hSylα
  have hmul := Subgroup.relIndex_mul_card (H := T.subgroupOf Lα)
    (K := Subgroup.normalizer ((T.subgroupOf Lα : Subgroup ↥Lα) : Set ↥Lα))
  rw [inf_eq_left.mpr Subgroup.le_normalizer, hrel] at hmul
  have hcardSub : Nat.card ↥(T.subgroupOf Lα) = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTleLα).toEquiv
  have hcardNorm : Nat.card ↥(Subgroup.normalizer
      ((T.subgroupOf Lα : Subgroup ↥Lα) : Set ↥Lα)) =
      Nat.card ↥(Lα ⊓ Subgroup.normalizer (T : Set H)) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hTleLα,
      ← Subgroup.card_subtype Lα ((Subgroup.normalizer (T : Set H)).subgroupOf Lα),
      Subgroup.subgroupOf_map_subtype, inf_comm]
  rw [hcardSub, hcardNorm] at hmul
  rw [hNαeq, ← hmul, heq.1]
  ring

private theorem u4q_card_bigB_inf_Lβ (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (h1 : IsL2Quot m (oTwoQuot ↥L1)) (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (hd : U4qEdgeData L1 L2 S f) :
    Nat.card ↥(bigB (oTwoPrime (f112saP1' L1 L2 S)) (oTwoPrime (f112saP2' L1 L2 S))
      (S ⊓ f112saK L1 L2 S) ⊓ oTwoPrime (f112saP2' L1 L2 S)) =
      Nat.card ↥(S ⊓ f112saK L1 L2 S) * (4 ^ f - 1) := by
  let Lα := oTwoPrime (f112saP1' L1 L2 S)
  let Lβ := oTwoPrime (f112saP2' L1 L2 S)
  let T := S ⊓ f112saK L1 L2 S
  have hR : Hyp111R L1 L2 S := hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2
  have hedge : Hyp111 Lα Lβ T := f112ll_hyp111_edge hF hm hn h1 h2
  have hSedge : Nat.card ↥T = 2 ^ (6 * f) := f112ll_u4q_card_T hF hm hn h1 h2 hd
  have heq : f = m ∧ n = 2 * f := f112ll_u4q_eq_of_localData hF hm hn h1 h2 hd
  have hTleLβ : T ≤ Lβ := f112sa_T_le_oTwoPrime_P2'_of_hyp111R hF hR
  have hSylβ : IsSylowTwoOf T Lβ := f112sa_T_sylow_oTwoPrime_P2'_of_hyp111R hF hR
  have hBnorm : bigB Lα Lβ T ≤
      Subgroup.normalizer (Lα : Set H) ⊓ Subgroup.normalizer (Lβ : Set H) ⊓
        Subgroup.normalizer (T : Set H) :=
    U4qLocalData.bigB_le_normalizer (G := H) hedge hd hSedge
  have hNβeq : bigB Lα Lβ T ⊓ Lβ = Lβ ⊓ Subgroup.normalizer (T : Set H) := by
    refine le_antisymm
      (le_inf inf_le_right ((inf_le_left.trans hBnorm).trans inf_le_right)) ?_
    have hBβ : borelOf Lβ T ≤ bigB Lα Lβ T := by
      rw [bigB]
      exact le_sup_right.trans le_sup_left
    have : Lβ ⊓ Subgroup.normalizer (T : Set H) = borelOf Lβ T := by
      rw [borelOf, inf_eq_left.mpr hTleLβ]
    rw [this]
    exact le_inf hBβ (CFSG.Quasithin.F1.borelOf_le Lβ T)
  have hqβ : IsL2Quot n (oTwoQuot ↥Lβ) := f112ll_isL2Quot_oTwoPrime_P2' hF hm hn h1 h2
  have hrel := relIndex_normalizer_of_isL2Quot (L := Lβ) (T := T) (by omega) hqβ hSylβ
  have hmul := Subgroup.relIndex_mul_card (H := T.subgroupOf Lβ)
    (K := Subgroup.normalizer ((T.subgroupOf Lβ : Subgroup ↥Lβ) : Set ↥Lβ))
  rw [inf_eq_left.mpr Subgroup.le_normalizer, hrel] at hmul
  have hcardSub : Nat.card ↥(T.subgroupOf Lβ) = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTleLβ).toEquiv
  have hcardNorm : Nat.card ↥(Subgroup.normalizer
      ((T.subgroupOf Lβ : Subgroup ↥Lβ) : Set ↥Lβ)) =
      Nat.card ↥(Lβ ⊓ Subgroup.normalizer (T : Set H)) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hTleLβ,
      ← Subgroup.card_subtype Lβ ((Subgroup.normalizer (T : Set H)).subgroupOf Lβ),
      Subgroup.subgroupOf_map_subtype, inf_comm]
  rw [hcardSub, hcardNorm] at hmul
  rw [hNβeq, ← hmul, heq.2,
    show (4 : ℕ) ^ f = 2 ^ (2 * f) by rw [pow_mul]; norm_num]
  ring

private theorem u4q_card_hall_inf_Lα (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (h1 : IsL2Quot m (oTwoQuot ↥L1)) (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (hd : U4qEdgeData L1 L2 S f) {H0 : Subgroup H}
    (hH0B : H0 ≤ bigB (oTwoPrime (f112saP1' L1 L2 S)) (oTwoPrime (f112saP2' L1 L2 S))
      (S ⊓ f112saK L1 L2 S))
    (hH0card : Nat.card ↥H0 = (2 ^ f - 1) * (4 ^ f - 1)) :
    Nat.card ↥(H0 ⊓ oTwoPrime (f112saP1' L1 L2 S)) = 2 ^ f - 1 := by
  let Lα := oTwoPrime (f112saP1' L1 L2 S)
  let Lβ := oTwoPrime (f112saP2' L1 L2 S)
  let T := S ⊓ f112saK L1 L2 S
  let B := bigB Lα Lβ T
  have hR : Hyp111R L1 L2 S := hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2
  have hedge : Hyp111 Lα Lβ T := f112ll_hyp111_edge hF hm hn h1 h2
  have hSedge : Nat.card ↥T = 2 ^ (6 * f) := f112ll_u4q_card_T hF hm hn h1 h2 hd
  have hBnorm : B ≤ Subgroup.normalizer (Lα : Set H) ⊓
      Subgroup.normalizer (Lβ : Set H) ⊓ Subgroup.normalizer (T : Set H) :=
    U4qLocalData.bigB_le_normalizer (G := H) hedge hd hSedge
  have hH0NLα : H0 ≤ Subgroup.normalizer (Lα : Set H) :=
    (hH0B.trans hBnorm).trans (inf_le_left.trans inf_le_left)
  have hH0Nbig : H0 ≤ Subgroup.normalizer (B : Set H) := hH0B.trans Subgroup.le_normalizer
  have heq : f = m ∧ n = 2 * f := f112ll_u4q_eq_of_localData hF hm hn h1 h2 hd
  have hDodd : Odd (Nat.card ↥(H0 ⊓ Lα)) := by
    refine Odd.of_dvd_nat ?_ (Subgroup.card_dvd_of_le inf_le_left)
    rw [hH0card]
    refine (Nat.Even.sub_odd Nat.one_le_two_pow
      ((show Even 2 by norm_num).pow_of_ne_zero (by omega)) odd_one).mul ?_
    rw [show (4 : ℕ) ^ f = 2 ^ (2 * f) by rw [pow_mul]; norm_num]
    exact Nat.Even.sub_odd Nat.one_le_two_pow
      ((show Even 2 by norm_num).pow_of_ne_zero (by omega)) odd_one
  have hNαcard := u4q_card_bigB_inf_Lα hF hm hn h1 h2 hd
  have hcardBig : Nat.card ↥B =
      Nat.card ↥(S ⊓ f112saK L1 L2 S) * ((2 ^ f - 1) * (4 ^ f - 1)) := by
    rw [U4qLocalData.card_bigB (G := H) hedge hd hSedge, ← hSedge]
  have hDeq : H0 ⊓ Lα = H0 ⊓ (B ⊓ Lα) := by
    rw [← inf_assoc, inf_eq_left.mpr hH0B]
  have hH0NNα : H0 ≤ Subgroup.normalizer ((B ⊓ Lα : Subgroup H) : Set H) :=
    (le_inf hH0Nbig hH0NLα).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hcardMul : Nat.card ↥H0 * Nat.card ↥(B ⊓ Lα) =
      Nat.card ↥B * (2 ^ f - 1) := by
    rw [hNαcard, hcardBig, hH0card]
    ring
  have hle : 2 ^ f - 1 ≤ Nat.card ↥(H0 ⊓ Lα) := by
    rw [hDeq]
    exact le_card_inf_of_mul_card_sup_le H0 (B ⊓ Lα) B (2 ^ f - 1)
      hH0NNα hH0B inf_le_left hcardMul
  have hdvd : Nat.card ↥(H0 ⊓ Lα) ∣ 2 ^ f - 1 := by
    have hdvd := Subgroup.card_dvd_of_le (H := H0 ⊓ Lα) (K := B ⊓ Lα) (by
      rw [hDeq]
      exact inf_le_right)
    rw [hNαcard, hSedge] at hdvd
    have hcop : Nat.Coprime (Nat.card ↥(H0 ⊓ Lα)) (2 ^ (6 * f)) :=
      Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hDodd)
    exact hcop.dvd_of_dvd_mul_left hdvd
  have hpos : 0 < 2 ^ f - 1 := by
    refine Nat.sub_pos_of_lt ?_
    calc 1 = 2 ^ 0 := by norm_num
      _ < 2 ^ f := Nat.pow_lt_pow_right (by norm_num) (by omega)
  exact le_antisymm (Nat.le_of_dvd hpos hdvd) hle

private theorem u4q_card_hall_inf_Lβ (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (h1 : IsL2Quot m (oTwoQuot ↥L1)) (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (hd : U4qEdgeData L1 L2 S f) {H0 : Subgroup H}
    (hH0B : H0 ≤ bigB (oTwoPrime (f112saP1' L1 L2 S)) (oTwoPrime (f112saP2' L1 L2 S))
      (S ⊓ f112saK L1 L2 S))
    (hH0card : Nat.card ↥H0 = (2 ^ f - 1) * (4 ^ f - 1)) :
    Nat.card ↥(H0 ⊓ oTwoPrime (f112saP2' L1 L2 S)) = 4 ^ f - 1 := by
  let Lα := oTwoPrime (f112saP1' L1 L2 S)
  let Lβ := oTwoPrime (f112saP2' L1 L2 S)
  let T := S ⊓ f112saK L1 L2 S
  let B := bigB Lα Lβ T
  have hR : Hyp111R L1 L2 S := hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2
  have hedge : Hyp111 Lα Lβ T := f112ll_hyp111_edge hF hm hn h1 h2
  have hSedge : Nat.card ↥T = 2 ^ (6 * f) := f112ll_u4q_card_T hF hm hn h1 h2 hd
  have hBnorm : B ≤ Subgroup.normalizer (Lα : Set H) ⊓
      Subgroup.normalizer (Lβ : Set H) ⊓ Subgroup.normalizer (T : Set H) :=
    U4qLocalData.bigB_le_normalizer (G := H) hedge hd hSedge
  have hH0NLβ : H0 ≤ Subgroup.normalizer (Lβ : Set H) :=
    (hH0B.trans hBnorm).trans (inf_le_left.trans inf_le_right)
  have hH0Nbig : H0 ≤ Subgroup.normalizer (B : Set H) := hH0B.trans Subgroup.le_normalizer
  have heq : f = m ∧ n = 2 * f := f112ll_u4q_eq_of_localData hF hm hn h1 h2 hd
  have hDodd : Odd (Nat.card ↥(H0 ⊓ Lβ)) := by
    refine Odd.of_dvd_nat ?_ (Subgroup.card_dvd_of_le inf_le_left)
    rw [hH0card]
    refine (Nat.Even.sub_odd Nat.one_le_two_pow
      ((show Even 2 by norm_num).pow_of_ne_zero (by omega)) odd_one).mul ?_
    rw [show (4 : ℕ) ^ f = 2 ^ (2 * f) by rw [pow_mul]; norm_num]
    exact Nat.Even.sub_odd Nat.one_le_two_pow
      ((show Even 2 by norm_num).pow_of_ne_zero (by omega)) odd_one
  have hNβcard := u4q_card_bigB_inf_Lβ hF hm hn h1 h2 hd
  have hcardBig : Nat.card ↥B =
      Nat.card ↥(S ⊓ f112saK L1 L2 S) * ((2 ^ f - 1) * (4 ^ f - 1)) := by
    rw [U4qLocalData.card_bigB (G := H) hedge hd hSedge, ← hSedge]
  have hDeq : H0 ⊓ Lβ = H0 ⊓ (B ⊓ Lβ) := by
    rw [← inf_assoc, inf_eq_left.mpr hH0B]
  have hH0NNβ : H0 ≤ Subgroup.normalizer ((B ⊓ Lβ : Subgroup H) : Set H) :=
    (le_inf hH0Nbig hH0NLβ).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hcardMul : Nat.card ↥H0 * Nat.card ↥(B ⊓ Lβ) =
      Nat.card ↥B * (4 ^ f - 1) := by
    rw [hNβcard, hcardBig, hH0card]
    ring
  have hle : 4 ^ f - 1 ≤ Nat.card ↥(H0 ⊓ Lβ) := by
    rw [hDeq]
    exact le_card_inf_of_mul_card_sup_le H0 (B ⊓ Lβ) B (4 ^ f - 1)
      hH0NNβ hH0B inf_le_left hcardMul
  have hdvd : Nat.card ↥(H0 ⊓ Lβ) ∣ 4 ^ f - 1 := by
    have hdvd := Subgroup.card_dvd_of_le (H := H0 ⊓ Lβ) (K := B ⊓ Lβ) (by
      rw [hDeq]
      exact inf_le_right)
    rw [hNβcard, hSedge] at hdvd
    have hcop : Nat.Coprime (Nat.card ↥(H0 ⊓ Lβ)) (2 ^ (6 * f)) :=
      Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hDodd)
    exact hcop.dvd_of_dvd_mul_left hdvd
  have hpos : 0 < 4 ^ f - 1 := by
    refine Nat.sub_pos_of_lt ?_
    calc 1 = 4 ^ 0 := by norm_num
      _ < 4 ^ f := Nat.pow_lt_pow_right (by norm_num) (by omega)
  exact le_antisymm (Nat.le_of_dvd hpos hdvd) hle

private theorem u4q_commutator_mem_T (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (h1 : IsL2Quot m (oTwoQuot ↥L1)) (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (hd : U4qEdgeData L1 L2 S f) {H0 : Subgroup H}
    (hH0B : H0 ≤ bigB (oTwoPrime (f112saP1' L1 L2 S)) (oTwoPrime (f112saP2' L1 L2 S))
      (S ⊓ f112saK L1 L2 S))
    (hH0card : Nat.card ↥H0 = (2 ^ f - 1) * (4 ^ f - 1))
    (hA : (S.subgroupOf (S ⊔ borelOf L1 S)).Normal) :
    ∀ d ∈ H0 ⊓ oTwoPrime (f112saP1' L1 L2 S), ∀ c ∈ S,
      d * c * d⁻¹ * c⁻¹ ∈ S ⊓ f112saK L1 L2 S := by
  let Lα := oTwoPrime (f112saP1' L1 L2 S)
  let Lβ := oTwoPrime (f112saP2' L1 L2 S)
  let T := S ⊓ f112saK L1 L2 S
  let K := f112saK L1 L2 S
  have hR : Hyp111R L1 L2 S := hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2
  have hL1 : L1 = Lα := f112ll_u4q_L1_eq hF hm hn h1 h2 hd
  have hSedge : Nat.card ↥T = 2 ^ (6 * f) := f112ll_u4q_card_T hF hm hn h1 h2 hd
  have hBnorm : bigB Lα Lβ T ≤ Subgroup.normalizer (Lα : Set H) ⊓
      Subgroup.normalizer (Lβ : Set H) ⊓ Subgroup.normalizer (T : Set H) :=
    U4qLocalData.bigB_le_normalizer (G := H)
      (f112ll_hyp111_edge hF hm hn h1 h2) hd hSedge
  have hH0NT : H0 ≤ Subgroup.normalizer (T : Set H) :=
    (hH0B.trans hBnorm).trans inf_le_right
  have heq : f = m ∧ n = 2 * f := f112ll_u4q_eq_of_localData hF hm hn h1 h2 hd
  have hDodd : Odd (Nat.card ↥(H0 ⊓ Lα)) := by
    refine Odd.of_dvd_nat ?_ (Subgroup.card_dvd_of_le inf_le_left)
    rw [hH0card]
    refine (Nat.Even.sub_odd Nat.one_le_two_pow
      ((show Even 2 by norm_num).pow_of_ne_zero (by omega)) odd_one).mul ?_
    rw [show (4 : ℕ) ^ f = 2 ^ (2 * f) by rw [pow_mul]; norm_num]
    exact Nat.Even.sub_odd Nat.one_le_two_pow
      ((show Even 2 by norm_num).pow_of_ne_zero (by omega)) odd_one
  have hSsup : S ⊔ borelOf L1 S ≤ Subgroup.normalizer (S : Set H) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mp hA
  have hSNT : S ≤ Subgroup.normalizer (T : Set H) :=
    u4q_S_le_normalizer_T hF hm hn h1 h2
  intro d hdD c hcS
  have hdLα : d ∈ Lα := (Subgroup.mem_inf.mp hdD).2
  have hdH0 : d ∈ H0 := (Subgroup.mem_inf.mp hdD).1
  have hDleL1 : H0 ⊓ Lα ≤ L1 := by
    rw [hL1]
    exact inf_le_right
  have hdO2 : d ∈ oTwoRes L1 :=
    CFSG.Quasithin.St84.le_oTwoRes_of_odd_card hDleL1 hDodd hdD
  have hDB1 : d ∈ borelOf L1 S := by
    rw [u4q_borelOf_L1_eq hF hm hn h1 h2 hd]
    exact Subgroup.mem_inf.mpr ⟨by rw [hL1]; exact hdLα, hH0NT hdH0⟩
  have hdS : d * c * d⁻¹ ∈ S :=
    (Subgroup.mem_normalizer_iff.mp (hSsup (Subgroup.mem_sup_right hDB1)) c).mp hcS
  have hdB : d ∈ bigB L1 L2 S :=
    (le_sup_left.trans le_sup_left : borelOf L1 S ≤ bigB L1 L2 S) hDB1
  have hdK : d ∈ K :=
    (le_sup_left : f112saX1 L1 L2 S ≤ K) (Subgroup.mem_inf.mpr ⟨hdO2, hdB⟩)
  have hcNK : c ∈ Subgroup.normalizer (K : Set H) :=
    f112sa_bigB_le_normalizer_K hF ((le_sup_right : S ≤ bigB L1 L2 S) hcS)
  have hcdK : c * d * c⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hcNK d).mp hdK
  refine Subgroup.mem_inf.mpr ⟨S.mul_mem hdS (S.inv_mem hcS), ?_⟩
  have hinv : c * d * c⁻¹ * d⁻¹ ∈ K := K.mul_mem hcdK (K.inv_mem hdK)
  have hinv' : (c * d * c⁻¹ * d⁻¹)⁻¹ ∈ K := K.inv_mem hinv
  have he : (c * d * c⁻¹ * d⁻¹)⁻¹ = d * c * d⁻¹ * c⁻¹ := by group
  rwa [he] at hinv'

private theorem u4q_exists_mul_centralizer (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (h1 : IsL2Quot m (oTwoQuot ↥L1)) (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (hd : U4qEdgeData L1 L2 S f) {H0 : Subgroup H}
    (hH0B : H0 ≤ bigB (oTwoPrime (f112saP1' L1 L2 S)) (oTwoPrime (f112saP2' L1 L2 S))
      (S ⊓ f112saK L1 L2 S))
    (hH0card : Nat.card ↥H0 = (2 ^ f - 1) * (4 ^ f - 1))
    (hA : (S.subgroupOf (S ⊔ borelOf L1 S)).Normal) :
    ∀ c ∈ S, ∃ t ∈ S ⊓ f112saK L1 L2 S,
      ∃ p ∈ S ⊓ Subgroup.centralizer ((H0 ⊓ oTwoPrime (f112saP1' L1 L2 S) : Subgroup H) :
        Set H), c = t * p := by
  let Lα := oTwoPrime (f112saP1' L1 L2 S)
  let T := S ⊓ f112saK L1 L2 S
  have hedge : Hyp111 Lα (oTwoPrime (f112saP2' L1 L2 S)) T :=
    f112ll_hyp111_edge hF hm hn h1 h2
  have hSedge : Nat.card ↥T = 2 ^ (6 * f) := f112ll_u4q_card_T hF hm hn h1 h2 hd
  have hBnorm : bigB Lα (oTwoPrime (f112saP2' L1 L2 S)) T ≤
      Subgroup.normalizer (Lα : Set H) ⊓
        Subgroup.normalizer (oTwoPrime (f112saP2' L1 L2 S) : Set H) ⊓
          Subgroup.normalizer (T : Set H) :=
    U4qLocalData.bigB_le_normalizer (G := H) hedge hd hSedge
  have hH0NT : H0 ≤ Subgroup.normalizer (T : Set H) :=
    (hH0B.trans hBnorm).trans inf_le_right
  have heq : f = m ∧ n = 2 * f := f112ll_u4q_eq_of_localData hF hm hn h1 h2 hd
  have hDodd : Odd (Nat.card ↥(H0 ⊓ Lα)) := by
    refine Odd.of_dvd_nat ?_ (Subgroup.card_dvd_of_le inf_le_left)
    rw [hH0card]
    refine (Nat.Even.sub_odd Nat.one_le_two_pow
      ((show Even 2 by norm_num).pow_of_ne_zero (by omega)) odd_one).mul ?_
    rw [show (4 : ℕ) ^ f = 2 ^ (2 * f) by rw [pow_mul]; norm_num]
    exact Nat.Even.sub_odd Nat.one_le_two_pow
      ((show Even 2 by norm_num).pow_of_ne_zero (by omega)) odd_one
  have hSNT : S ≤ Subgroup.normalizer (T : Set H) :=
    u4q_S_le_normalizer_T hF hm hn h1 h2
  have hcomm := u4q_commutator_mem_T hF hm hn h1 h2 hd hH0B hH0card hA
  intro c hcS
  have hT2 : IsPGroup 2 ↥T := hF.1.h1.pgroup.to_le (inf_le_left : T ≤ S)
  obtain ⟨q, hqT, hqc⟩ := exists_mul_mem_centralizer_of_odd (Q := T) (J := H0 ⊓ Lα)
    hT2 hDodd (fun d hd => hH0NT (Subgroup.mem_inf.mp hd).1)
    (hSNT hcS) (hcomm · · c hcS)
  refine ⟨q⁻¹, T.inv_mem hqT, q * c, ?_, by group⟩
  exact Subgroup.mem_inf.mpr ⟨S.mul_mem ((inf_le_left : T ≤ S) hqT) hcS, hqc⟩

private theorem u4q_relIndex_T_P_dvd_two (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (h1 : IsL2Quot m (oTwoQuot ↥L1)) (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (hd : U4qEdgeData L1 L2 S f) {P : Subgroup H} (hPS : P ≤ S)
    (hrelP : (trivOTwoQuot (oTwoPrime (f112saP2' L1 L2 S))).relIndex P ∣ 2) :
    (S ⊓ f112saK L1 L2 S).relIndex P ∣ 2 := by
  have hle : P ⊓ trivOTwoQuot (oTwoPrime (f112saP2' L1 L2 S)) ≤
      P ⊓ (S ⊓ f112saK L1 L2 S) := by
    intro x hx
    obtain ⟨hxP, hxtriv⟩ := Subgroup.mem_inf.mp hx
    exact Subgroup.mem_inf.mpr ⟨hxP,
      f112ll_u4q_S_inf_trivOTwoQuot_right_le hF hm hn h1 h2 hd
        (Subgroup.mem_inf.mpr ⟨hPS hxP, hxtriv⟩)⟩
  have h := Subgroup.relIndex_dvd_of_le_left
    (H := P ⊓ trivOTwoQuot (oTwoPrime (f112saP2' L1 L2 S)))
    (K := P ⊓ (S ⊓ f112saK L1 L2 S)) (L := P) hle
  have h' : (S ⊓ f112saK L1 L2 S).relIndex P ∣
      (trivOTwoQuot (oTwoPrime (f112saP2' L1 L2 S))).relIndex P := by
    simpa only [Subgroup.relIndex, Subgroup.inf_subgroupOf_left] using h
  exact h'.trans hrelP

private theorem u4q_trivOTwoQuot_relIndex_D (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (h1 : IsL2Quot m (oTwoQuot ↥L1)) (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (hd : U4qEdgeData L1 L2 S f) {H0 : Subgroup H}
    (hDcard : Nat.card ↥(H0 ⊓ oTwoPrime (f112saP1' L1 L2 S)) = 2 ^ f - 1) :
    (trivOTwoQuot (oTwoPrime (f112saP2' L1 L2 S))).relIndex
      (H0 ⊓ oTwoPrime (f112saP1' L1 L2 S)) = 2 ^ f - 1 := by
  let Lα := oTwoPrime (f112saP1' L1 L2 S)
  let Lβ := oTwoPrime (f112saP2' L1 L2 S)
  let D := H0 ⊓ Lα
  have heq : f = m ∧ n = 2 * f := f112ll_u4q_eq_of_localData hF hm hn h1 h2 hd
  have hDodd : Odd (Nat.card ↥D) := by
    rw [hDcard]
    refine Nat.Even.sub_odd Nat.one_le_two_pow
      ((show Even 2 by norm_num).pow_of_ne_zero (by omega)) odd_one
  have hDinf : trivOTwoQuot Lβ ⊓ D = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hxtriv, hxD⟩ := Subgroup.mem_inf.mp hx
    have hxodd : Odd (orderOf x) :=
      Odd.of_dvd_nat hDodd (Subgroup.orderOf_dvd_natCard D hxD)
    exact f112ll_u4q_eq_one_of_mem_trivOTwoQuot_right hF hm hn h1 h2 hd
      ((inf_le_right : D ≤ Lα) hxD) hxodd hxtriv
  have h := Subgroup.relIndex_mul_card (H := trivOTwoQuot Lβ) (K := D)
  rw [hDinf, Subgroup.card_bot, mul_one] at h
  rw [h, hDcard]

private theorem u4q_trivOTwoQuot_relIndex_P_dvd_two (hF : F112HypW L1 L2 S) (hm : 2 ≤ m)
    (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1)) (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (hd : U4qEdgeData L1 L2 S f) {H0 : Subgroup H}
    (hH0B : H0 ≤ bigB (oTwoPrime (f112saP1' L1 L2 S)) (oTwoPrime (f112saP2' L1 L2 S))
      (S ⊓ f112saK L1 L2 S))
    (hH0ab : ∀ a ∈ H0, ∀ b ∈ H0, a * b = b * a)
    (hDcard : Nat.card ↥(H0 ⊓ oTwoPrime (f112saP1' L1 L2 S)) = 2 ^ f - 1)
    (hD'card : Nat.card ↥(H0 ⊓ oTwoPrime (f112saP2' L1 L2 S)) = 4 ^ f - 1) :
    (trivOTwoQuot (oTwoPrime (f112saP2' L1 L2 S))).relIndex
      (S ⊓ Subgroup.centralizer ((H0 ⊓ oTwoPrime (f112saP1' L1 L2 S) : Subgroup H) :
        Set H)) ∣ 2 := by
  let Lα := oTwoPrime (f112saP1' L1 L2 S)
  let Lβ := oTwoPrime (f112saP2' L1 L2 S)
  let T := S ⊓ f112saK L1 L2 S
  let D := H0 ⊓ Lα
  let D' := H0 ⊓ Lβ
  let P := S ⊓ Subgroup.centralizer (D : Set H)
  have hedge : Hyp111 Lα Lβ T := f112ll_hyp111_edge hF hm hn h1 h2
  have hSedge : Nat.card ↥T = 2 ^ (6 * f) := f112ll_u4q_card_T hF hm hn h1 h2 hd
  have heq : f = m ∧ n = 2 * f := f112ll_u4q_eq_of_localData hF hm hn h1 h2 hd
  have hR : Hyp111R L1 L2 S := hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2
  have hBnorm : bigB Lα Lβ T ≤ Subgroup.normalizer (Lα : Set H) ⊓
      Subgroup.normalizer (Lβ : Set H) ⊓ Subgroup.normalizer (T : Set H) :=
    U4qLocalData.bigB_le_normalizer (G := H) hedge hd hSedge
  have hH0NLβ : H0 ≤ Subgroup.normalizer (Lβ : Set H) :=
    (hH0B.trans hBnorm).trans (inf_le_left.trans inf_le_right)
  have hH0NT : H0 ≤ Subgroup.normalizer (T : Set H) := (hH0B.trans hBnorm).trans inf_le_right
  have hD'le : D' ≤ Lβ ⊓ Subgroup.normalizer (T : Set H) :=
    le_inf inf_le_right ((inf_le_left : D' ≤ H0).trans hH0NT)
  have hD'card2 : Nat.card ↥D' = 2 ^ (2 * f) - 1 := by
    rw [hD'card, show (4 : ℕ) ^ f = 2 ^ (2 * f) by rw [pow_mul]; norm_num]
  have hDLβ : D ≤ Subgroup.normalizer (Lβ : Set H) :=
    (inf_le_left : D ≤ H0).trans hH0NLβ
  have hDT : D ≤ Subgroup.normalizer (T : Set H) := (inf_le_left : D ≤ H0).trans hH0NT
  have hDD' : ∀ d ∈ D, ∀ t ∈ D', d * t = t * d :=
    fun d hd t ht => hH0ab d ((inf_le_left : D ≤ H0) hd) t ((inf_le_left : D' ≤ H0) ht)
  have hDidx := u4q_trivOTwoQuot_relIndex_D hF hm hn h1 h2 hd hDcard
  have hqβ' : IsL2Quot (2 * f) (oTwoQuot ↥Lβ) := by
    have hqβ : IsL2Quot n (oTwoQuot ↥Lβ) := f112ll_isL2Quot_oTwoPrime_P2' hF hm hn h1 h2
    rwa [heq.2] at hqβ
  have hSNβ : S ≤ Subgroup.normalizer (Lβ : Set H) := by
    refine ((le_sup_right : S ≤ bigB L1 L2 S).trans
      (le_sup_right : bigB L1 L2 S ≤ f112P2 L1 L2 S)).trans ?_
    intro x hx
    exact mem_normalizer_oTwoPrime ((f112sa_P2_le_normalizer_P2' hF) hx)
  have hSNT : S ≤ Subgroup.normalizer (T : Set H) :=
    u4q_S_le_normalizer_T hF hm hn h1 h2
  have hP2 : IsPGroup 2 ↥P := hF.1.h1.pgroup.to_le (inf_le_left : P ≤ S)
  have hPLβ : P ≤ Subgroup.normalizer (Lβ : Set H) :=
    fun x hx => hSNβ ((inf_le_left : P ≤ S) hx)
  have hPT : P ≤ Subgroup.normalizer (T : Set H) :=
    fun x hx => hSNT ((inf_le_left : P ≤ S) hx)
  have hPD : ∀ c ∈ P, ∀ d ∈ D, c * d = d * c := by
    intro c hcP d hdD
    exact (Subgroup.mem_centralizer_iff.mp ((inf_le_right : P ≤ Subgroup.centralizer
      (D : Set H)) hcP) d hdD).symm
  exact relIndex_trivOTwoQuot_dvd_of_commute_outer_torus (L := Lβ) (T := T) (D' := D') (D := D)
    (P := P) (e := f) (r := 2) (by omega) hqβ'
    (f112sa_T_sylow_oTwoPrime_P2'_of_hyp111R hF hR) hD'le hD'card2 hDLβ hDT hDD' hDidx
    hP2 hPLβ hPT hPD

private theorem u4q_relIndex_eq_of_forall_mul
    (hSNT : S ≤ Subgroup.normalizer ((S ⊓ f112saK L1 L2 S : Subgroup H) : Set H))
    {P : Subgroup H} (hPS : P ≤ S)
    (hSP : ∀ c ∈ S, ∃ t ∈ S ⊓ f112saK L1 L2 S, ∃ p ∈ P, c = t * p) :
    (f112saK L1 L2 S).relIndex S = (S ⊓ f112saK L1 L2 S).relIndex P := by
  classical
  let T := S ⊓ f112saK L1 L2 S
  have hTS : T ≤ S := inf_le_left
  have hTnormS : (T.subgroupOf S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hTS).mpr hSNT
  let T₀ := T.subgroupOf S
  let P₀ := P.subgroupOf S
  have hTPtop : T₀ ⊔ P₀ = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨t, htT, p, hpP, hx⟩ := hSP x x.2
    have htS : t ∈ S := hTS htT
    have hpS : p ∈ S := hPS hpP
    have htT₀ : (⟨t, htS⟩ : ↥S) ∈ T₀ := Subgroup.mem_subgroupOf.mpr htT
    have hpP₀ : (⟨p, hpS⟩ : ↥S) ∈ P₀ := Subgroup.mem_subgroupOf.mpr hpP
    have hx' : x = (⟨t, htS⟩ : ↥S) * ⟨p, hpS⟩ := Subtype.ext hx
    rw [hx']
    exact (T₀ ⊔ P₀).mul_mem (Subgroup.mem_sup_left htT₀) (Subgroup.mem_sup_right hpP₀)
  have hTnormS₀ : T₀.Normal := hTnormS
  have hidx : T.relIndex S = T.relIndex P := by
    have h := Subgroup.relIndex_sup_left (H := P₀) (K := T₀)
    rw [hTPtop, Subgroup.relIndex_top_right, Subgroup.relIndex_subgroupOf hPS] at h
    exact h
  have hKrel : (f112saK L1 L2 S).relIndex S = T.relIndex S :=
    (Subgroup.inf_relIndex_left S (f112saK L1 L2 S)).symm
  rw [hKrel, hidx]

theorem f112ll_u4q_relIndex_dvd_two_of_normal_left (hF : F112HypW L1 L2 S) (hm : 2 ≤ m)
    (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1)) (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (hd : U4qEdgeData L1 L2 S f) (hA : (S.subgroupOf (S ⊔ borelOf L1 S)).Normal) :
    (f112saK L1 L2 S).relIndex S ∣ 2 := by
  classical
  let Lα := oTwoPrime (f112saP1' L1 L2 S)
  let Lβ := oTwoPrime (f112saP2' L1 L2 S)
  let T := S ⊓ f112saK L1 L2 S
  have hedge : Hyp111 Lα Lβ T := f112ll_hyp111_edge hF hm hn h1 h2
  have hSedge : Nat.card ↥T = 2 ^ (6 * f) := f112ll_u4q_card_T hF hm hn h1 h2 hd
  obtain ⟨H0, hH0B, -, -, hH0card, hH0ab⟩ :=
    U4qLocalData.exists_hall_bigB (G := H) hedge hd hSedge
  have hDcard : Nat.card ↥(H0 ⊓ Lα) = 2 ^ f - 1 :=
    u4q_card_hall_inf_Lα hF hm hn h1 h2 hd hH0B hH0card
  have hD'card : Nat.card ↥(H0 ⊓ Lβ) = 4 ^ f - 1 :=
    u4q_card_hall_inf_Lβ hF hm hn h1 h2 hd hH0B hH0card
  have hSNT : S ≤ Subgroup.normalizer (T : Set H) :=
    u4q_S_le_normalizer_T hF hm hn h1 h2
  have hSP := u4q_exists_mul_centralizer hF hm hn h1 h2 hd hH0B hH0card hA
  have hrelP := u4q_trivOTwoQuot_relIndex_P_dvd_two hF hm hn h1 h2 hd hH0B hH0ab
    hDcard hD'card
  have hTP := u4q_relIndex_T_P_dvd_two hF hm hn h1 h2 hd
    (P := S ⊓ Subgroup.centralizer ((H0 ⊓ Lα : Subgroup H) : Set H)) inf_le_left hrelP
  have hidx := u4q_relIndex_eq_of_forall_mul (L1 := L1) (L2 := L2) hSNT
    (P := S ⊓ Subgroup.centralizer ((H0 ⊓ Lα : Subgroup H) : Set H))
    (inf_le_left : S ⊓ Subgroup.centralizer ((H0 ⊓ Lα : Subgroup H) : Set H) ≤ S) hSP
  rw [hidx]
  exact hTP

theorem f112ll_u4q_card_S (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (h1 : IsL2Quot m (oTwoQuot ↥L1)) (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (hd : U4qEdgeData L1 L2 S f) :
    Nat.card S = 2 ^ (6 * m) ∨ Nat.card S = 2 * 2 ^ (6 * m) := by
  let T := S ⊓ f112saK L1 L2 S
  have heq : f = m ∧ n = 2 * f := f112ll_u4q_eq_of_localData hF hm hn h1 h2 hd
  have hcardT : Nat.card ↥T = 2 ^ (6 * f) := f112ll_u4q_card_T hF hm hn h1 h2 hd
  have hcardS : Nat.card S = Nat.card ↥T * (f112saK L1 L2 S).relIndex S := by
    have h := Subgroup.relIndex_mul_card (H := T) (K := S)
    rw [inf_eq_left.mpr (inf_le_left : T ≤ S)] at h
    have hrel : T.relIndex S = (f112saK L1 L2 S).relIndex S :=
      Subgroup.inf_relIndex_left S (f112saK L1 L2 S)
    rw [hrel] at h
    rw [← h, mul_comm]
  have hdvd : (f112saK L1 L2 S).relIndex S ∣ 2 := by
    rcases hF.2 with hA | hB
    · exact f112ll_u4q_relIndex_dvd_two_of_normal_left hF hm hn h1 h2 hd hA
    · have hSK : S ≤ f112saK L1 L2 S :=
        f112ll_u4q_le_K_of_normal_right hF hm hn h1 h2 hd hB
      rw [Subgroup.relIndex_eq_one.mpr hSK]
      exact one_dvd 2
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with hone | htwo
  · left
    rw [hcardS, hone, mul_one, hcardT, heq.1]
  · right
    rw [hcardS, htwo, hcardT, heq.1, mul_comm]


theorem f112ll_u4qLocalData_of_edgeData (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (h1 : IsL2Quot m (oTwoQuot ↥L1)) (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (hd : U4qEdgeData L1 L2 S f) :
    n = 2 * m ∧ U4qLocalData L1 L2 S m := by
  have heq : f = m ∧ n = 2 * f := f112ll_u4q_eq_of_localData hF hm hn h1 h2 hd
  have hL1 : L1 = oTwoPrime (f112saP1' L1 L2 S) := f112ll_u4q_L1_eq hF hm hn h1 h2 hd
  have hL2 : L2 = oTwoPrime (f112saP2' L1 L2 S) := f112ll_u4q_L2_eq hF hm hn h1 h2 hd
  refine ⟨by omega, ?_⟩
  refine
    { card_S := f112ll_u4q_card_S hF hm hn h1 h2 hd
      special_left := ?_
      center_left := ?_
      twoNat_left := ?_
      card_right := ?_
      omega_right := ?_
      card_inf := ?_ }
  · have h := hd.special_left
    rwa [← hL1, heq.1] at h
  · have h := hd.center_left
    rwa [← hL1] at h
  · have h := hd.twoNat_left
    rwa [← hL1, heq.1] at h
  · have h := hd.card_right
    rwa [← hL2, heq.1] at h
  · have h := hd.omega_right
    rwa [← hL2, heq.1] at h
  · have h := hd.card_inf
    rwa [← hL1, ← hL2, heq.1] at h


theorem f112ll_u4qLocalData_of_edgeData_swap (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (h1 : IsL2Quot m (oTwoQuot ↥L1)) (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (hd : U4qLocalData (oTwoPrime (f112saP2' L1 L2 S)) (oTwoPrime (f112saP1' L1 L2 S))
      (S ⊓ f112saK L1 L2 S) f) :
    m = 2 * n ∧ U4qLocalData L2 L1 S n := by
  have hd' : U4qEdgeData L2 L1 S f := by
    show U4qLocalData (oTwoPrime (f112saP1' L2 L1 S)) (oTwoPrime (f112saP2' L2 L1 S))
      (S ⊓ f112saK L2 L1 S) f
    rw [f112saP1'_eq_P2'_swap L2 L1 S, f112saP2'_eq_P1'_swap L2 L1 S,
      f112saK_comm L1 L2 S]
    exact hd
  exact f112ll_u4qLocalData_of_edgeData hF.symm hn hm h2 h1 hd'

end CFSG.Quasithin.F112R.St84

end
