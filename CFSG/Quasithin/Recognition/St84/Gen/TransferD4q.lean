module

public import CFSG.Quasithin.Recognition.St84.Gen.TransferD4qData

import CFSG.Quasithin.Recognition.St84.Gen.TransferD4qCore
import CFSG.Quasithin.Recognition.St84.Gen.TransferLeftCore
import CFSG.Quasithin.Recognition.St84.Gen.TransferL2OuterTorus
import CFSG.Quasithin.Recognition.St84.Gen.TransferEdgeHyp
import CFSG.Quasithin.Recognition.St84.Gen.TransferLL
import CFSG.Quasithin.Recognition.St84.Gen.TreeLLBase
import CFSG.Quasithin.Recognition.St84.Gen.D4qAmalBorel
import CFSG.Quasithin.Recognition.St84.Gen.D4qAmalIndecRight
import CFSG.Quasithin.Recognition.St84.Gen.CoprimeLift
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
import CFSG.Quasithin.Recognition.St84.AppTreeSAP1
import CFSG.Quasithin.Recognition.St84.PushUp
import CFSG.RankThree.PartTwo.Sec15.Item153PushProofTools
import Certificates.Kernel.J4Count.Prim

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped MatrixGroups commutatorElement

variable {H : Type} [Group H] [Finite H]

private theorem f112ll_d4q_exists_centralizing_coset {L1 L2 S Hh : Subgroup H}
    (hF : F112HypW L1 L2 S) {c : H} (hcS : c ∈ S)
    (hc : ∀ l ∈ oTwoPrime (f112saP2' L1 L2 S), ⁅c, l⁆ ∈ pCoreOf 2 (f112saP2' L1 L2 S))
    (hodd : Odd (Nat.card ↥(Hh ⊓ oTwoPrime (f112saP2' L1 L2 S)))) :
    ∃ y ∈ pCoreOf 2 (f112saP2' L1 L2 S),
      y * c ∈ Subgroup.centralizer (Hh ⊓ oTwoPrime (f112saP2' L1 L2 S) : Set H) := by
  classical
  let Lβ := oTwoPrime (f112saP2' L1 L2 S)
  let Qβ := pCoreOf 2 (f112saP2' L1 L2 S)
  have hQ : IsPGroup 2 ↥Qβ :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (f112saP2' L1 L2 S)
  have hJQ : Hh ⊓ Lβ ≤ Subgroup.normalizer (Qβ : Set H) := by
    rw [show Qβ = pCoreOf 2 Lβ from (pCoreOf_oTwoPrime (f112saP2' L1 L2 S)).symm]
    exact (inf_le_right : Hh ⊓ Lβ ≤ Lβ).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Lβ)
  have hcQ : c ∈ Subgroup.normalizer (Qβ : Set H) := by
    have hSβ : S ≤ Subgroup.normalizer (f112saP2' L1 L2 S : Set H) :=
      ((le_sup_right : S ≤ bigB L1 L2 S).trans
        (le_sup_right : bigB L1 L2 S ≤ f112P2 L1 L2 S)).trans
          (f112sa_P2_le_normalizer_P2' hF)
    exact (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (f112saP2' L1 L2 S))
      (hSβ hcS)
  have hcomm : ∀ j ∈ Hh ⊓ Lβ, j * c * j⁻¹ * c⁻¹ ∈ Qβ := by
    intro j hj
    have hinv : ⁅c, j⁆⁻¹ ∈ Qβ := Qβ.inv_mem (hc j (Subgroup.mem_inf.mp hj).2)
    have heq : ⁅c, j⁆⁻¹ = j * c * j⁻¹ * c⁻¹ := by
      rw [commutatorElement_def]
      group
    rwa [heq] at hinv
  exact exists_mul_mem_centralizer_of_odd (Q := Qβ) (J := Hh ⊓ Lβ) hQ hodd hJQ hcQ hcomm

private theorem f112ll_d4q_odd_card_hall {Hh : Subgroup H} {f : ℕ} (hf : 2 ≤ f)
    (hHcard : Nat.card Hh = (2 ^ (3 * f) - 1) * (2 ^ f - 1)) :
    Odd (Nat.card ↥Hh) := by
  rw [hHcard]
  exact (Nat.Even.sub_odd Nat.one_le_two_pow
      ((show Even 2 by norm_num).pow_of_ne_zero (by omega : 3 * f ≠ 0)) odd_one).mul
    (Nat.Even.sub_odd Nat.one_le_two_pow
      ((show Even 2 by norm_num).pow_of_ne_zero (by omega : f ≠ 0)) odd_one)

private theorem f112ll_d4q_hall_inf_trivOTwoQuot {L1 L2 S Hh : Subgroup H} {m n : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) (hleft : TransferLeftData L1 L2 S)
    (hoddH : Odd (Nat.card ↥Hh)) :
    Hh ⊓ oTwoPrime (f112saP2' L1 L2 S) ⊓
      trivOTwoQuot (oTwoPrime (f112saP1' L1 L2 S)) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  rintro k ⟨hkD, hktriv⟩
  obtain ⟨hkHh, hkLβ⟩ := Subgroup.mem_inf.mp hkD
  exact hleft.eq_one_of_mem_trivOTwoQuot k hkLβ
    (Odd.of_dvd_nat hoddH (Subgroup.orderOf_dvd_natCard Hh hkHh)) hktriv

private theorem f112ll_d4q_relIndex_hall {L1 L2 S Hh : Subgroup H} {m n f : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) (hleft : TransferLeftData L1 L2 S) (hf : 2 ≤ f)
    (hHcard : Nat.card Hh = (2 ^ (3 * f) - 1) * (2 ^ f - 1))
    (hcardD : Nat.card ↥(Hh ⊓ oTwoPrime (f112saP2' L1 L2 S)) = 2 ^ f - 1) :
    (trivOTwoQuot (oTwoPrime (f112saP1' L1 L2 S))).relIndex
      (Hh ⊓ oTwoPrime (f112saP2' L1 L2 S)) = 2 ^ f - 1 := by
  let Lα := oTwoPrime (f112saP1' L1 L2 S)
  let Lβ := oTwoPrime (f112saP2' L1 L2 S)
  have htriv := f112ll_d4q_hall_inf_trivOTwoQuot hF hm hn h1 h2 hleft
    (f112ll_d4q_odd_card_hall hf hHcard)
  have hinf : trivOTwoQuot Lα ⊓ (Hh ⊓ Lβ) = ⊥ := by
    simpa only [inf_assoc, inf_comm, inf_left_comm] using htriv
  have hmul := Subgroup.relIndex_mul_card (H := trivOTwoQuot Lα) (K := Hh ⊓ Lβ)
  rw [hinf, hcardD] at hmul
  simpa using hmul

private theorem f112ll_d4q_mem_K_of_centralizes_hall {L1 L2 S Hh : Subgroup H} {m n f : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) (hd : D4qEdgeData L1 L2 S f)
    (hHB : Hh ≤ bigB (oTwoPrime (f112saP1' L1 L2 S)) (oTwoPrime (f112saP2' L1 L2 S))
      (S ⊓ f112saK L1 L2 S))
    (hSH : (S ⊓ f112saK L1 L2 S) ⊔ Hh = bigB (oTwoPrime (f112saP1' L1 L2 S))
      (oTwoPrime (f112saP2' L1 L2 S)) (S ⊓ f112saK L1 L2 S))
    (hSinfH : (S ⊓ f112saK L1 L2 S) ⊓ Hh = ⊥)
    (hHcard : Nat.card Hh = (2 ^ (3 * f) - 1) * (2 ^ f - 1))
    (hHcomm : ∀ a ∈ Hh, ∀ b ∈ Hh, a * b = b * a) {c : H} (hcS : c ∈ S)
    (hcD : ∀ d ∈ Hh ⊓ oTwoPrime (f112saP2' L1 L2 S), c * d = d * c) :
    c ∈ f112saK L1 L2 S := by
  classical
  let Lα := oTwoPrime (f112saP1' L1 L2 S)
  let Lβ := oTwoPrime (f112saP2' L1 L2 S)
  let T := S ⊓ f112saK L1 L2 S
  have hR : Hyp111R L1 L2 S := hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2
  have hH : Hyp111 Lα Lβ T := f112ll_hyp111_edge hF hm hn h1 h2
  have hloc : D4qLocalData Lα Lβ T f := hd
  obtain ⟨hm3, hfn⟩ := f112ll_d4q_eq_of_localData hF hm hn h1 h2 hloc
  have hq : IsL2Quot (3 * f) (oTwoQuot ↥Lα) :=
    hm3 ▸ f112ll_isL2Quot_oTwoPrime_P1' hF hm hn h1 h2
  have hf : 2 ≤ f := by omega
  have htl := hloc.torus_left_of_hall hH hq hHB hSH hSinfH hHcard hHcomm
  have htr := hloc.torus_right_of_hall hf hH hq hHB hSH hSinfH hHcard hHcomm
  have hHhN : Hh ≤ Subgroup.normalizer (Lα : Set H) ⊓ Subgroup.normalizer (Lβ : Set H) ⊓
      Subgroup.normalizer (T : Set H) := hHB.trans (hloc.bigB_le_normalizer hH hq)
  have hdidx : (trivOTwoQuot Lα).relIndex (Hh ⊓ Lβ) = 2 ^ f - 1 :=
    f112ll_d4q_relIndex_hall hF hm hn h1 h2 (hd.transferLeftData hF hm hn h1 h2) hf
      hHcard htr.1
  have hD' : Hh ⊓ Lα ≤ Lα ⊓ Subgroup.normalizer (T : Set H) :=
    le_inf inf_le_right ((inf_le_left : Hh ⊓ Lα ≤ Hh).trans (hHhN.trans inf_le_right))
  have hDL : Hh ⊓ Lβ ≤ Subgroup.normalizer (Lα : Set H) :=
    (inf_le_left : Hh ⊓ Lβ ≤ Hh).trans (hHhN.trans (inf_le_left.trans inf_le_left))
  have hDT : Hh ⊓ Lβ ≤ Subgroup.normalizer (T : Set H) :=
    (inf_le_left : Hh ⊓ Lβ ≤ Hh).trans (hHhN.trans inf_le_right)
  have hDD' : ∀ d ∈ Hh ⊓ Lβ, ∀ t ∈ Hh ⊓ Lα, d * t = t * d :=
    fun d hd' t ht => hHcomm d (Subgroup.mem_inf.mp hd').1 t (Subgroup.mem_inf.mp ht).1
  have hc2 : ∃ k, c ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hF.1.h1.pgroup ⟨c, hcS⟩
    exact ⟨k, by simpa using congrArg (fun x : ↥S => (x : H)) hk⟩
  have hSNα : S ≤ Subgroup.normalizer (f112saP1' L1 L2 S : Set H) :=
    ((le_sup_right : S ≤ bigB L1 L2 S).trans
      (le_sup_right : bigB L1 L2 S ≤ f112P1 L1 L2 S)).trans
        (f112sa_P1_le_normalizer_P1' hF)
  have hcL : c ∈ Subgroup.normalizer (Lα : Set H) := mem_normalizer_oTwoPrime (hSNα hcS)
  have hcT : c ∈ Subgroup.normalizer (T : Set H) := by
    rw [show T = S ⊓ f112saK L1 L2 S from rfl, ← f112ll_pCoreOf_K_eq hF hm hn h1 h2]
    exact ((f112sa_bigB_le_normalizer_K hF).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (f112saK L1 L2 S)))
      ((le_sup_right : S ≤ bigB L1 L2 S) hcS)
  have hcQα : ∀ l ∈ Lα, ⁅c, l⁆ ∈ pCoreOf 2 Lα :=
    commutator_mem_pCoreOf_of_commute_outer_torus (L := Lα) (T := T)
      (D' := Hh ⊓ Lα) (D := Hh ⊓ Lβ) (e := f) (r := 3) (c := c)
      hf (by norm_num) hq (f112sa_T_sylow_oTwoPrime_P1'_of_hyp111R hF hR)
      hD' htl.1 hDL hDT hDD' hdidx hc2 hcL hcT hcD
  refine TransferLeftData.mem_K_of_left hF hm hn h1 h2
    (hd.transferLeftData hF hm hn h1 h2) hcS (fun l hl => ?_)
  have hQα : pCoreOf 2 Lα = pCoreOf 2 (f112saP1' L1 L2 S) :=
    pCoreOf_oTwoPrime (f112saP1' L1 L2 S)
  have h := hcQα l hl
  rwa [hQα] at h

theorem f112ll_d4q_mem_K_of_right {L1 L2 S : Subgroup H} {m n f : ℕ} (hF : F112HypW L1 L2 S)
    (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) (hd : D4qEdgeData L1 L2 S f) {c : H} (hcS : c ∈ S)
    (hc : ∀ l ∈ oTwoPrime (f112saP2' L1 L2 S), ⁅c, l⁆ ∈ pCoreOf 2 (f112saP2' L1 L2 S)) :
    c ∈ f112saK L1 L2 S := by
  classical
  let Lα := oTwoPrime (f112saP1' L1 L2 S)
  let Lβ := oTwoPrime (f112saP2' L1 L2 S)
  let T := S ⊓ f112saK L1 L2 S
  have hH : Hyp111 Lα Lβ T := f112ll_hyp111_edge hF hm hn h1 h2
  have hloc : D4qLocalData Lα Lβ T f := hd
  obtain ⟨hm3, hfn⟩ := f112ll_d4q_eq_of_localData hF hm hn h1 h2 hloc
  have hf : 2 ≤ f := by omega
  have hq : IsL2Quot (3 * f) (oTwoQuot ↥Lα) :=
    hm3 ▸ f112ll_isL2Quot_oTwoPrime_P1' hF hm hn h1 h2
  obtain ⟨Hh, hHB, hSH, hSinfH, hHcard, hHcomm⟩ := hloc.exists_hall_bigB hH hq
  have htr := hloc.torus_right_of_hall hf hH hq hHB hSH hSinfH hHcard hHcomm
  have hodd : Odd (Nat.card ↥(Hh ⊓ Lβ)) := by
    rw [htr.1]
    exact Nat.Even.sub_odd Nat.one_le_two_pow
      ((show Even 2 by norm_num).pow_of_ne_zero (by omega : f ≠ 0)) odd_one
  obtain ⟨y, hyQ, hyc⟩ :=
    f112ll_d4q_exists_centralizing_coset hF hcS hc hodd
  have hQβT : pCoreOf 2 (f112saP2' L1 L2 S) ≤ T := by
    rw [show T = S ⊓ f112saK L1 L2 S from rfl, ← f112ll_pCoreOf_sup_eq hF hm hn h1 h2]
    exact le_sup_right
  have hycS : y * c ∈ S := S.mul_mem (hQβT.trans inf_le_left hyQ) hcS
  have hcy : ∀ d ∈ Hh ⊓ Lβ, (y * c) * d = d * (y * c) :=
    fun d hd' => (Subgroup.mem_centralizer_iff.mp hyc d hd').symm
  have hc'K : y * c ∈ f112saK L1 L2 S :=
    f112ll_d4q_mem_K_of_centralizes_hall hF hm hn h1 h2 hd hHB hSH hSinfH hHcard hHcomm
      hycS hcy
  have hyK : y ∈ f112saK L1 L2 S := (inf_le_right : T ≤ f112saK L1 L2 S) (hQβT hyQ)
  have hcEq : c = y⁻¹ * (y * c) := by group
  rw [hcEq]
  exact (f112saK L1 L2 S).mul_mem ((f112saK L1 L2 S).inv_mem hyK) hc'K

theorem f112ll_d4q_mem_K_of_left {L1 L2 S : Subgroup H} {m n f : ℕ} (hF : F112HypW L1 L2 S)
    (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) (hd : D4qEdgeData L1 L2 S f) {c : H} (hcS : c ∈ S)
    (hc : ∀ l ∈ oTwoPrime (f112saP1' L1 L2 S), ⁅c, l⁆ ∈ pCoreOf 2 (f112saP1' L1 L2 S)) :
    c ∈ f112saK L1 L2 S :=
  TransferLeftData.mem_K_of_left hF hm hn h1 h2 (hd.transferLeftData hF hm hn h1 h2) hcS hc

private theorem f112ll_d4q_indec_right {L1 L2 S : Subgroup H} {m n f : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) (hd : D4qEdgeData L1 L2 S f) (hf : 2 ≤ f) :
    ⁅pCoreOf 2 (f112saP2' L1 L2 S), oTwoPrime (f112saP2' L1 L2 S)⁆ =
      pCoreOf 2 (f112saP2' L1 L2 S) := by
  have hm3 : m = 3 * f := (f112ll_d4q_eq_of_localData hF hm hn h1 h2 hd).1
  have h1' : IsL2Quot (3 * f) (oTwoQuot ↥(oTwoPrime (f112saP1' L1 L2 S))) :=
    hm3 ▸ f112ll_isL2Quot_oTwoPrime_P1' hF hm hn h1 h2
  have h := D4qLocalData.indec_right hf (f112ll_hyp111_edge hF hm hn h1 h2) hd h1'
  rwa [pCoreOf_oTwoPrime (f112saP2' L1 L2 S)] at h

theorem f112ll_d4qLocalData_of_edgeData {L1 L2 S : Subgroup H} {m n f : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) (hd : D4qEdgeData L1 L2 S f) :
    m = 3 * n ∧ D4qLocalData L1 L2 S n := by
  classical
  have hR : Hyp111R L1 L2 S := hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2
  have hq1 : IsL2Quot m (oTwoQuot ↥(oTwoPrime (f112saP1' L1 L2 S))) :=
    f112ll_isL2Quot_oTwoPrime_P1' hF hm hn h1 h2
  have hq2 : IsL2Quot n (oTwoQuot ↥(oTwoPrime (f112saP2' L1 L2 S))) :=
    f112ll_isL2Quot_oTwoPrime_P2' hF hm hn h1 h2
  have hSK : S ≤ f112saK L1 L2 S :=
    f112sa_le_K_of_core_steps_of_isL2Quot hF hm hn h1 h2 hm hq1 hn hq2
      (fun c hcS hc => f112ll_d4q_mem_K_of_left hF hm hn h1 h2 hd hcS hc)
      (fun c hcS hc => f112ll_d4q_mem_K_of_right hF hm hn h1 h2 hd hcS hc)
  have hL1 : L1 = oTwoPrime (f112saP1' L1 L2 S) :=
    (f112sa_S_le_L1_and_eq_oTwoPrime_of_S_le_K_of_isL2Quot hF hR hm h1 hSK hm hq1
      (f112ll_d4q_indec_left hF hm hn h1 h2 hd)).2.1
  obtain ⟨hm3, hfn⟩ := f112ll_d4q_eq_of_localData hF hm hn h1 h2 hd
  have hindec2 : ⁅pCoreOf 2 (f112saP2' L1 L2 S), oTwoPrime (f112saP2' L1 L2 S)⁆ =
      pCoreOf 2 (f112saP2' L1 L2 S) :=
    f112ll_d4q_indec_right hF hm hn h1 h2 hd (by omega)
  have hL2 : L2 = oTwoPrime (f112saP2' L1 L2 S) :=
    (f112sa_S_le_L2_and_eq_oTwoPrime_of_S_le_K_of_isL2Quot hF hR hn h2 hSK hn hq2
      hindec2).2.1
  have hST : S ⊓ f112saK L1 L2 S = S := inf_eq_left.mpr hSK
  refine ⟨hm3.trans ?_, ?_⟩
  · rw [hfn]
  · have h : D4qLocalData (oTwoPrime (f112saP1' L1 L2 S))
        (oTwoPrime (f112saP2' L1 L2 S)) (S ⊓ f112saK L1 L2 S) f := hd
    rw [← hL1, ← hL2, hST, hfn] at h
    exact h

theorem f112ll_d4qLocalData_of_edgeData_swap {L1 L2 S : Subgroup H} {m n f : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (hd : D4qLocalData (oTwoPrime (f112saP2' L1 L2 S)) (oTwoPrime (f112saP1' L1 L2 S))
      (S ⊓ f112saK L1 L2 S) f) :
    n = 3 * m ∧ D4qLocalData L2 L1 S m := by
  have hd' : D4qEdgeData L2 L1 S f := by
    show D4qLocalData (oTwoPrime (f112saP1' L2 L1 S)) (oTwoPrime (f112saP2' L2 L1 S))
      (S ⊓ f112saK L2 L1 S) f
    rw [f112saP1'_eq_P2'_swap L2 L1 S, f112saP2'_eq_P1'_swap L2 L1 S,
      f112saK_comm L1 L2 S]
    exact hd
  exact f112ll_d4qLocalData_of_edgeData hF.symm hn hm h2 h1 hd'

end CFSG.Quasithin.F112R.St84

end
