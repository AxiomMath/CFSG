module

public import CFSG.Quasithin.Recognition.St84.Gen.TransferG2qCore

import CFSG.Quasithin.Recognition.St84.Gen.TransferLeftCore
import CFSG.Quasithin.Recognition.St84.Gen.TransferLL
import CFSG.Quasithin.Recognition.St84.Gen.TreeLLBase
import CFSG.Quasithin.Recognition.St84.Gen.L2RankOne
import CFSG.Quasithin.Recognition.St84.Gen.NatSecModule
import CFSG.Quasithin.Recognition.St84.Gen.TransferL2Inner
public import CFSG.CharacterTheory.Wreathed.BrauerWongSylowCentralizer
public import CFSG.CharacterTheory.Wreathed.OddKernelSylowQuotient
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.GroupTheory.QuasiDihedralFusion.InvolutionCentralizer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldAction
public import CFSG.Quasithin.Recognition.St84.TransferInner
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
import CFSG.Quasithin.Recognition.St84.AppTreeSAP1
import CFSG.Quasithin.Recognition.St84.PushUp
import CFSG.RankThree.PartTwo.Sec15.Item153PushProofTools
import Certificates.Kernel.J4Count.Prim

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped MatrixGroups Pointwise commutatorElement

variable {H : Type} [Group H] [Finite H]

private theorem conj_mem_centerOf {O : Subgroup H} {g c : H}
    (hg : g ∈ Subgroup.normalizer (O : Set H)) (hc : c ∈ centerOf O) :
    g * c * g⁻¹ ∈ centerOf O := by
  obtain ⟨hcO, hcC⟩ := Subgroup.mem_inf.mp hc
  refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hg c).mp hcO, ?_⟩
  rw [Subgroup.mem_centralizer_iff] at hcC ⊢
  intro q hq
  have hq'O : g⁻¹ * q * g ∈ O := by
    simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) q).mp hq
  have hcq : c * (g⁻¹ * q * g) = (g⁻¹ * q * g) * c := (hcC _ hq'O).symm
  have hconj : (g * c * g⁻¹) * q * (g * c * g⁻¹)⁻¹ = q := by
    calc (g * c * g⁻¹) * q * (g * c * g⁻¹)⁻¹
        = g * (c * (g⁻¹ * q * g) * c⁻¹) * g⁻¹ := by group
      _ = g * (g⁻¹ * q * g) * g⁻¹ := by rw [hcq]; group
      _ = q := by group
  have h2 : (g * c * g⁻¹) * q = q * (g * c * g⁻¹) := by
    have := congrArg (fun y => y * (g * c * g⁻¹)) hconj
    simpa [mul_assoc] using this
  exact h2.symm

theorem f112ll_g2q_mem_K_of_left {L1 L2 S : Subgroup H} {m n f : ℕ} (hF : F112HypW L1 L2 S)
    (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) (hd : G2qEdgeData L1 L2 S f) {c : H} (hcS : c ∈ S)
    (hc : ∀ l ∈ oTwoPrime (f112saP1' L1 L2 S), ⁅c, l⁆ ∈ pCoreOf 2 (f112saP1' L1 L2 S)) :
    c ∈ f112saK L1 L2 S := by
  exact (hd.transferLeftData hF hm hn h1 h2).mem_K_of_left hF hm hn h1 h2 hcS hc

private theorem conj_mem_middle {L Q Z W : Subgroup H} {F : Type} [Field F]
    {α : ↥L →* SL(2, F)} (hWnat : IsNatSecOf L Q W α) (hα : Function.Surjective α)
    (hLQ : L ≤ Subgroup.normalizer (Q : Set H)) (hWQ : W ≤ Q)
    (hWcomm : ⁅W, L⁆ ≤ Z) (hZW : Z ≤ W) {c : H}
    (hcL : c ∈ Subgroup.normalizer (L : Set H)) (hcQ : c ∈ Subgroup.normalizer (Q : Set H))
    (hcZ : ∀ z ∈ Z, c * z * c⁻¹ ∈ Z) :
    ∀ x ∈ W, c * x * c⁻¹ ∈ W := by
  intro x hx
  have hxQ : x ∈ Q := hWQ hx
  have hyQ : c * x * c⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hcQ x).mp hxQ
  refine IsNatSecOf.mem_of_forall_commutator_mem hWnat hα hLQ hyQ ?_
  intro ℓ hℓ
  have hℓ' : c⁻¹ * ℓ * c ∈ L := by
    simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hcL) ℓ).mp hℓ
  have hcommZ : c⁻¹ * ℓ * c * x * (c⁻¹ * ℓ * c)⁻¹ * x⁻¹ ∈ Z := by
    have hmem := Subgroup.commutator_mem_commutator (H₁ := W) (H₂ := L) hx hℓ'
    have hinv : ⁅x, c⁻¹ * ℓ * c⁆⁻¹ ∈ Z := Z.inv_mem (hWcomm hmem)
    have heq : ⁅x, c⁻¹ * ℓ * c⁆⁻¹ = c⁻¹ * ℓ * c * x * (c⁻¹ * ℓ * c)⁻¹ * x⁻¹ := by
      rw [commutatorElement_def]
      group
    rwa [heq] at hinv
  have hconj : ℓ * (c * x * c⁻¹) * ℓ⁻¹ * (c * x * c⁻¹)⁻¹ =
      c * ((c⁻¹ * ℓ * c) * x * (c⁻¹ * ℓ * c)⁻¹ * x⁻¹) * c⁻¹ := by
    group
  rw [hconj]
  exact hZW (hcZ _ hcommZ)

private theorem f112ll_g2q_middle_of_edgeData {L1 L2 S : Subgroup H} {m n f : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) (hd : G2qEdgeData L1 L2 S f) {c : H} (hcS : c ∈ S)
    (hc : ∀ l ∈ oTwoPrime (f112saP2' L1 L2 S), ⁅c, l⁆ ∈ pCoreOf 2 (f112saP2' L1 L2 S)) :
    ∃ W : Subgroup H, W ≤ pCoreOf 2 (f112saP1' L1 L2 S) ∧
      ∀ e ∈ pCoreOf 2 (f112saP2' L1 L2 S), ⁅c, e⁆ ∈ W := by
  classical
  let Lβ := oTwoPrime (f112saP2' L1 L2 S)
  let Qβ := pCoreOf 2 (f112saP2' L1 L2 S)
  have hR : Hyp111R L1 L2 S := hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2
  have hQβ : pCoreOf 2 Lβ = Qβ := pCoreOf_oTwoPrime (f112saP2' L1 L2 S)
  have hSNβ : S ≤ Subgroup.normalizer (f112saP2' L1 L2 S : Set H) :=
    ((le_sup_right : S ≤ bigB L1 L2 S).trans
      (le_sup_right : bigB L1 L2 S ≤ f112P2 L1 L2 S)).trans
        (f112sa_P2_le_normalizer_P2' hF)
  obtain ⟨F, hField, hFintype, hFcard, α, hαsurj, hαker, -, W, hZW, hWQ, -, hWcomm, hWnat⟩ :=
    hd.local_.nat_right
  letI : Field F := hField
  letI : Fintype F := hFintype
  letI : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := f) hFcard
  rw [hQβ] at hZW hWQ hWcomm hWnat
  have hcLβ : c ∈ Subgroup.normalizer (Lβ : Set H) := mem_normalizer_oTwoPrime (hSNβ hcS)
  have hcQβ : c ∈ Subgroup.normalizer (Qβ : Set H) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (f112saP2' L1 L2 S)
      (hSNβ hcS)
  have hLQβ : Lβ ≤ Subgroup.normalizer (Qβ : Set H) := by
    simpa [hQβ] using CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Lβ
  have hc2 : ∃ k, c ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hF.1.h1.pgroup ⟨c, hcS⟩
    exact ⟨k, by simpa using congrArg (fun x : ↥S => (x : H)) hk⟩
  have hcqβ : ∀ x ∈ Lβ, c * x * c⁻¹ * x⁻¹ ∈ pCoreOf 2 Lβ := by
    intro x hx
    rw [hQβ]
    exact hc x hx
  have hcW : ∀ x ∈ W, c * x * c⁻¹ ∈ W :=
    conj_mem_middle hWnat hαsurj hLQβ hWQ hWcomm hZW hcLβ hcQβ
      (fun z hz => conj_mem_centerOf hcQβ hz)
  have hcQβmem : ∀ e ∈ Qβ, ⁅c, e⁆ ∈ W :=
    IsNatSecOf.commutatorElement_mem hWnat hαsurj hαker hLQβ hc2 hcQβ
      (fun x hxQ hxW => hcW x hxW) hcLβ hcqβ
  have hWQα : W ≤ pCoreOf 2 (f112saP1' L1 L2 S) := by
    intro x hx
    exact hd.relCent_left x (hWQ hx)
      (fun l hl => hWcomm (Subgroup.commutator_mem_commutator (H₁ := W) (H₂ := Lβ) hx hl))
  exact ⟨W, hWQα, hcQβmem⟩

private theorem f112ll_g2q_mem_K_of_middle {L1 L2 S : Subgroup H} {m n f : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) (hd : G2qEdgeData L1 L2 S f) {c : H} (hcS : c ∈ S)
    {W : Subgroup H} (hWQα : W ≤ pCoreOf 2 (f112saP1' L1 L2 S))
    (hcW : ∀ e ∈ pCoreOf 2 (f112saP2' L1 L2 S), ⁅c, e⁆ ∈ W) :
    c ∈ f112saK L1 L2 S := by
  classical
  let Lα := oTwoPrime (f112saP1' L1 L2 S)
  let Qα := pCoreOf 2 (f112saP1' L1 L2 S)
  let Qβ := pCoreOf 2 (f112saP2' L1 L2 S)
  let T := S ⊓ f112saK L1 L2 S
  have hR : Hyp111R L1 L2 S := hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2
  have hQα : pCoreOf 2 Lα = Qα := pCoreOf_oTwoPrime (f112saP1' L1 L2 S)
  have hSNα : S ≤ Subgroup.normalizer (f112saP1' L1 L2 S : Set H) :=
    ((le_sup_right : S ≤ bigB L1 L2 S).trans
      (le_sup_right : bigB L1 L2 S ≤ f112P1 L1 L2 S)).trans
        (f112sa_P1_le_normalizer_P1' hF)
  have hTQ : T = pCoreOf 2 (f112saP2' L1 L2 S) ⊔ pCoreOf 2 (f112saP1' L1 L2 S) := by
    rw [show T = S ⊓ f112saK L1 L2 S from rfl, ← f112ll_pCoreOf_sup_eq hF hm hn h1 h2,
      sup_comm]
  have hQβT : Qβ ≤ T := by
    rw [hTQ]
    exact le_sup_left
  have hAT : Qβ ⊔ pCoreOf 2 Lα = T := by
    rw [hTQ, hQα]
  obtain ⟨a, haQβ, ha⟩ :=
    exists_mul_inv_commutator_mem_pCoreOf_of_isL2Quot_of_commutator_mem
      (L := Lα) (T := T) (A := Qβ)
      (f112ll_isL2Quot_oTwoPrime_P1' hF hm hn h1 h2)
      (f112sa_T_sylow_oTwoPrime_P1'_of_hyp111R hF hR) hQβT hAT
      (mem_normalizer_oTwoPrime (hSNα hcS))
      (fun a ha => by
        have h := hWQα (hcW a ha)
        simpa [commutatorElement_def, hQα] using h)
  have hQβLα : Qβ ≤ Lα := hQβT.trans (f112sa_T_le_oTwoPrime_P1'_of_hyp111R hF hR)
  have hcaS : c * a⁻¹ ∈ S := S.mul_mem hcS (S.inv_mem (hQβT.trans (inf_le_left : T ≤ S) haQβ))
  have hca : c * a⁻¹ ∈ trivOTwoQuot Lα := by
    refine mem_trivOTwoQuot.mpr ⟨?_, ?_⟩
    · exact Subgroup.mul_mem _ (mem_normalizer_oTwoPrime (hSNα hcS))
        (Subgroup.inv_mem _ (Subgroup.le_normalizer (hQβLα haQβ)))
    · intro l hl
      exact ha l hl
  have hcaK : c * a⁻¹ ∈ f112saK L1 L2 S :=
    f112ll_g2q_mem_K_of_left hF hm hn h1 h2 hd hcaS
      (fun l hl => by
        have h := (mem_trivOTwoQuot.mp hca).2 l hl
        rw [hQα] at h
        simpa [commutatorElement_def] using h)
  have haK : a ∈ f112saK L1 L2 S := hQβT.trans (inf_le_right : T ≤ f112saK L1 L2 S) haQβ
  have hcEq : c = (c * a⁻¹) * a := by group
  rw [hcEq]
  exact (f112saK L1 L2 S).mul_mem hcaK haK

theorem f112ll_g2q_mem_K_of_right {L1 L2 S : Subgroup H} {m n f : ℕ} (hF : F112HypW L1 L2 S)
    (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) (hd : G2qEdgeData L1 L2 S f) {c : H} (hcS : c ∈ S)
    (hc : ∀ l ∈ oTwoPrime (f112saP2' L1 L2 S), ⁅c, l⁆ ∈ pCoreOf 2 (f112saP2' L1 L2 S)) :
    c ∈ f112saK L1 L2 S := by
  obtain ⟨W, hWQα, hcW⟩ := f112ll_g2q_middle_of_edgeData hF hm hn h1 h2 hd hcS hc
  exact f112ll_g2q_mem_K_of_middle hF hm hn h1 h2 hd hcS hWQα hcW

theorem f112ll_g2qLocalData_of_edgeData {L1 L2 S : Subgroup H} {m n f : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) (hd : G2qEdgeData L1 L2 S f) :
    m = n ∧ G2qLocalData L1 L2 S n := by
  have hR : Hyp111R L1 L2 S := hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2
  have hq1 : IsL2Quot m (oTwoQuot ↥(oTwoPrime (f112saP1' L1 L2 S))) :=
    f112ll_isL2Quot_oTwoPrime_P1' hF hm hn h1 h2
  have hq2 : IsL2Quot n (oTwoQuot ↥(oTwoPrime (f112saP2' L1 L2 S))) :=
    f112ll_isL2Quot_oTwoPrime_P2' hF hm hn h1 h2
  have hSK : S ≤ f112saK L1 L2 S :=
    f112sa_le_K_of_core_steps_of_isL2Quot hF hm hn h1 h2 hm hq1 hn hq2
      (fun c hcS hc => f112ll_g2q_mem_K_of_left hF hm hn h1 h2 hd hcS hc)
      (fun c hcS hc => f112ll_g2q_mem_K_of_right hF hm hn h1 h2 hd hcS hc)
  have hL1 : L1 = oTwoPrime (f112saP1' L1 L2 S) :=
    (f112sa_S_le_L1_and_eq_oTwoPrime_of_S_le_K_of_isL2Quot hF hR hm h1 hSK hm hq1
      hd.indec_left).2.1
  have hL2 : L2 = oTwoPrime (f112saP2' L1 L2 S) :=
    (f112sa_S_le_L2_and_eq_oTwoPrime_of_S_le_K_of_isL2Quot hF hR hn h2 hSK hn hq2
      hd.indec_right).2.1
  have hST : S ⊓ f112saK L1 L2 S = S := inf_eq_left.mpr hSK
  have heq : f = m ∧ f = n := f112ll_g2q_eq_of_localData hF hm hn h1 h2 hd.local_
  have hloc : G2qLocalData L1 L2 S n := by
    have h := hd.local_
    rw [← hL1, ← hL2, hST, heq.2] at h
    exact h
  exact ⟨heq.1.symm.trans heq.2, hloc⟩

end CFSG.Quasithin.F112R.St84

end
