module

public import CFSG.Quasithin.Recognition.St84.Gen.TransferLeftData
public import CFSG.Quasithin.Recognition.St84.Gen.L2SectionBorel
public import CFSG.Quasithin.Recognition.St84.TransferInner

import CFSG.Quasithin.Recognition.St84.TransferVertex
import CFSG.Quasithin.Recognition.St84.Gen.TreeLLBase
import CFSG.Quasithin.Recognition.St84.Gen.L2RankOne
import CFSG.Quasithin.Recognition.St84.Gen.L2SectionHall
import CFSG.Quasithin.Recognition.St84.Gen.PerfectGen
import CFSG.Quasithin.Recognition.St84.Gen.NatSecModule
import CFSG.Quasithin.Recognition.St84.Gen.CoprimeLift
import CFSG.Quasithin.Recognition.St84.Gen.CoprimeComplement
import CFSG.Quasithin.Recognition.St84.Gen.TransferL2Inner
import CFSG.Quasithin.Recognition.St84.Gen.TransferLL
import CFSG.Quasithin.Recognition.St84.Gen.TransferL2Torus
import CFSG.GroupTheory.PermSylowTwo.SymCore
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84Residual
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
import CFSG.Quasithin.Recognition.St84.AppTreeSAP1
import CFSG.Quasithin.Recognition.St84.PushUp
import CFSG.RankThree.PartTwo.Sec15.Item153PushProofTools
import Certificates.Kernel.J4Count.Prim

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped MatrixGroups commutatorElement

variable {H : Type} [Group H] [Finite H]

private theorem exists_odd_prime_order_of_not_isPGroup_two {X : Type*} [Group X] [Finite X]
    (h : ¬ IsPGroup 2 X) :
    ∃ (x : X) (p : ℕ), p.Prime ∧ Odd p ∧ orderOf x = p := by
  have h1 : ¬ ((Nat.card X).primeFactors ⊆ (2).primeFactors) := by
    rwa [isPGroup_iff_primeFactors_card_subset (p := 2) (by norm_num)] at h
  change ¬ ∀ p, p ∈ (Nat.card X).primeFactors → p ∈ (2).primeFactors at h1
  push Not at h1
  obtain ⟨p, hp_mem, hp_not⟩ := h1
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
  have hp2 : p ≠ 2 := by
    intro hp2
    apply hp_not
    rw [hp2]
    exact Nat.Prime.mem_primeFactors Nat.prime_two dvd_rfl (by norm_num)
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p (Nat.dvd_of_mem_primeFactors hp_mem)
  exact ⟨x, p, hp, hp.odd_of_ne_two hp2, hx⟩

private theorem le_normalizer_centerOf_pCoreOf (L : Subgroup H) :
    L ≤ Subgroup.normalizer (centerOf (pCoreOf 2 L) : Set H) := by
  intro g hg
  have hgQ : g ∈ Subgroup.normalizer (pCoreOf 2 L : Set H) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L hg
  have hgC : g ∈ Subgroup.normalizer
      (Subgroup.centralizer (pCoreOf 2 L : Set H) : Set H) :=
    CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer (pCoreOf 2 L) hgQ
  change g ∈ Subgroup.normalizer
    ((pCoreOf 2 L ⊓ Subgroup.centralizer (pCoreOf 2 L : Set H) : Subgroup H) : Set H)
  exact Subgroup.inf_normalizer_le_normalizer_inf (Subgroup.mem_inf.mpr ⟨hgQ, hgC⟩)

private theorem centralizes_centerRight {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (hd : TransferLeftData L1 L2 S) {c : H} (hcS : c ∈ S)
    (hc2 : c ∈ trivOTwoQuot (oTwoPrime (f112saP2' L1 L2 S))) :
    ∀ z ∈ centerOf (pCoreOf 2 (f112saP2' L1 L2 S)), c * z = z * c := by
  classical
  obtain ⟨F, hFld, hFchar, α, hα, hker, hnat⟩ := hd.nat_right
  letI := hFld
  letI := hFchar
  let Lβ := oTwoPrime (f112saP2' L1 L2 S)
  let Qβ := pCoreOf 2 (f112saP2' L1 L2 S)
  have hQeq : pCoreOf 2 Lβ = Qβ := pCoreOf_oTwoPrime _
  have hc2pow : ∃ k, c ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hF.1.h2.pgroup ⟨c, hcS⟩
    exact ⟨k, by simpa using congrArg (fun x : ↥S => (x : H)) hk⟩
  have hcNLβ : c ∈ Subgroup.normalizer (Lβ : Set H) := (mem_trivOTwoQuot.mp hc2).1
  have hcNQβ : c ∈ Subgroup.normalizer (Qβ : Set H) := by
    have h := CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Lβ hcNLβ
    rwa [hQeq] at h
  have hcNCβ : c ∈ Subgroup.normalizer
      (Subgroup.centralizer (Qβ : Set H) : Set H) :=
    CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer Qβ hcNQβ
  have hcNE : c ∈ Subgroup.normalizer (centerOf (pCoreOf 2 Lβ) : Set H) := by
    rw [hQeq]
    change c ∈ Subgroup.normalizer
      ((Qβ ⊓ Subgroup.centralizer (Qβ : Set H) : Subgroup H) : Set H)
    exact Subgroup.inf_normalizer_le_normalizer_inf (Subgroup.mem_inf.mpr ⟨hcNQβ, hcNCβ⟩)
  have hLE : Lβ ≤ Subgroup.normalizer (centerOf (pCoreOf 2 Lβ) : Set H) :=
    le_normalizer_centerOf_pCoreOf Lβ
  have hcN : ∀ x ∈ centerOf (pCoreOf 2 Lβ), x ∈ (⊥ : Subgroup H) →
      c * x * c⁻¹ ∈ (⊥ : Subgroup H) := by
    intro x _ hx
    rw [Subgroup.mem_bot] at hx ⊢
    rw [hx]
    simp
  have hcomm := hnat.commutatorElement_mem hα hker hLE hc2pow hcNE hcN hcNLβ
    (mem_trivOTwoQuot.mp hc2).2
  intro z hz
  have hz' : z ∈ centerOf (pCoreOf 2 Lβ) := by
    rw [hQeq]
    exact hz
  exact commutatorElement_eq_one_iff_mul_comm.mp (by simpa using hcomm z hz')

private def commutatorSubgroup (Qα Zα : Subgroup H) (c : H)
    (hQα_N : Qα ≤ Subgroup.normalizer (Zα : Set H)) : Subgroup H :=
  { carrier := {x : H | x ∈ Qα ∧ ⁅c, x⁆ ∈ Zα},
    one_mem' := by
      refine ⟨Qα.one_mem, ?_⟩
      rw [commutatorElement_one_right]
      exact Zα.one_mem,
    mul_mem' := by
      rintro x y ⟨hxQ, hxZ⟩ ⟨hyQ, hyZ⟩
      refine ⟨Qα.mul_mem hxQ hyQ, ?_⟩
      rw [commutatorElement_mul_right_eq_mul_conj]
      have h : x * ⁅c, y⁆ * x⁻¹ ∈ Zα :=
        (Subgroup.mem_normalizer_iff.mp (hQα_N hxQ) ⁅c, y⁆).mp hyZ
      rw [show ⁅c, x⁆ * x * ⁅c, y⁆ * x⁻¹ = ⁅c, x⁆ * (x * ⁅c, y⁆ * x⁻¹) by group]
      exact Zα.mul_mem hxZ h,
    inv_mem' := by
      rintro x ⟨hxQ, hxZ⟩
      refine ⟨Qα.inv_mem hxQ, ?_⟩
      rw [commutatorElement_inv_right, ← commutatorElement_inv]
      simpa using (Subgroup.mem_normalizer_iff.mp (hQα_N (Qα.inv_mem hxQ)) ⁅c, x⁆⁻¹).mp
        (Zα.inv_mem hxZ) }

private theorem commutatorSubgroup_normalized {L1 L2 S : Subgroup H}
    (hZ : centerOf (pCoreOf 2 (f112saP1' L1 L2 S)) ≤
      Subgroup.centralizer (oTwoPrime (f112saP1' L1 L2 S) : Set H))
    (hcomm : ⁅pCoreOf 2 (f112saP1' L1 L2 S), pCoreOf 2 (f112saP1' L1 L2 S)⁆ ≤
      centerOf (pCoreOf 2 (f112saP1' L1 L2 S))) {c : H}
    (hc1 : c ∈ trivOTwoQuot (oTwoPrime (f112saP1' L1 L2 S)))
    (hQα_N : pCoreOf 2 (f112saP1' L1 L2 S) ≤
      Subgroup.normalizer (centerOf (pCoreOf 2 (f112saP1' L1 L2 S)) : Set H)) :
    oTwoPrime (f112saP1' L1 L2 S) ≤
      Subgroup.normalizer (commutatorSubgroup
        (pCoreOf 2 (f112saP1' L1 L2 S))
        (centerOf (pCoreOf 2 (f112saP1' L1 L2 S))) c hQα_N : Set H) := by
  classical
  let Eα := f112saP1' L1 L2 S
  let Lα := oTwoPrime Eα
  let Qα := pCoreOf 2 Eα
  let Zα := centerOf Qα
  let N : Subgroup H := commutatorSubgroup Qα Zα c hQα_N
  rw [Subgroup.le_normalizer_iff]
  intro l hl x hx
  have hxQ : x ∈ Qα := hx.1
  have hxZ : ⁅c, x⁆ ∈ Zα := hx.2
  have hqQ : ⁅c, l⁆ ∈ Qα := by
    have h := (mem_trivOTwoQuot.mp hc1).2 l hl
    rwa [pCoreOf_oTwoPrime] at h
  have hlNQ : l ∈ Subgroup.normalizer (Qα : Set H) :=
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Eα) ((oTwoPrime_le Eα) hl)
  have hwQ : l * x * l⁻¹ ∈ Qα := (Subgroup.mem_normalizer_iff.mp hlNQ x).mp hxQ
  have hlz : l * ⁅c, x⁆ * l⁻¹ = ⁅c, x⁆ := by
    have hzC : ⁅c, x⁆ ∈ Subgroup.centralizer (Lα : Set H) := hZ hxZ
    rw [Subgroup.mem_centralizer_iff.mp hzC l hl]
    group
  have hclinv : l * ⁅c, l⁻¹⁆ * l⁻¹ = ⁅c, l⁆⁻¹ := by
    rw [commutatorElement_inv_right, commutatorElement_inv]
    group
  have hmain : ⁅c, l * x * l⁻¹⁆ = ⁅c, l⁆ * (l * ⁅c, x⁆ * l⁻¹) * (l * x * l⁻¹) *
      (l * ⁅c, l⁻¹⁆ * l⁻¹) * (l * x * l⁻¹)⁻¹ := by
    simp only [commutatorElement_def]
    group
  refine ⟨hwQ, ?_⟩
  rw [hmain, hlz, hclinv]
  have hzq : ⁅c, x⁆ * ⁅c, l⁆ = ⁅c, l⁆ * ⁅c, x⁆ :=
    (Subgroup.mem_centralizer_iff.mp hxZ.2 ⁅c, l⁆ hqQ).symm
  have hqwc : ⁅(⁅c, l⁆), l * x * l⁻¹⁆ ∈ Zα :=
    hcomm (Subgroup.commutator_mem_commutator hqQ hwQ)
  have heq : ⁅c, l⁆ * ⁅c, x⁆ * (l * x * l⁻¹) * ⁅c, l⁆⁻¹ * (l * x * l⁻¹)⁻¹ =
      ⁅c, x⁆ * ⁅(⁅c, l⁆), l * x * l⁻¹⁆ := by
    rw [commutatorElement_def (⁅c, l⁆) (l * x * l⁻¹)]
    rw [← hzq]
    group
  rw [heq]
  exact Zα.mul_mem hxZ hqwc

private theorem commutator_pCoreOf_mem_center {L1 L2 S : Subgroup H}
    (hd : TransferLeftData L1 L2 S) {c : H}
    (hc1 : c ∈ trivOTwoQuot (oTwoPrime (f112saP1' L1 L2 S)))
    (hcZ : ∀ z ∈ centerOf (pCoreOf 2 (f112saP2' L1 L2 S)), c * z = z * c) :
    ∀ x ∈ pCoreOf 2 (f112saP1' L1 L2 S),
      ⁅c, x⁆ ∈ centerOf (pCoreOf 2 (f112saP1' L1 L2 S)) := by
  classical
  let Eα := f112saP1' L1 L2 S
  let Lα := oTwoPrime Eα
  let Qα := pCoreOf 2 Eα
  let Zα := centerOf Qα
  let Zβ := centerOf (pCoreOf 2 (f112saP2' L1 L2 S))
  have hQα_N : Qα ≤ Subgroup.normalizer (Zα : Set H) := by
    change pCoreOf 2 Eα ≤ Subgroup.normalizer (centerOf (pCoreOf 2 Eα) : Set H)
    exact (CFSG.LieType.BorelTits.pCoreOf_le 2 Eα).trans
      (le_normalizer_centerOf_pCoreOf Eα)
  let N : Subgroup H := commutatorSubgroup Qα Zα c hQα_N
  have hcNLα : c ∈ Subgroup.normalizer (Lα : Set H) := (mem_trivOTwoQuot.mp hc1).1
  have hcNQα : c ∈ Subgroup.normalizer (Qα : Set H) := by
    have h := CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Lα hcNLα
    rwa [pCoreOf_oTwoPrime] at h
  have hcNZα : c ∈ Subgroup.normalizer (Zα : Set H) := by
    have hcNC : c ∈ Subgroup.normalizer
        (Subgroup.centralizer (Qα : Set H) : Set H) :=
      CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer Qα hcNQα
    change c ∈ Subgroup.normalizer
      ((Qα ⊓ Subgroup.centralizer (Qα : Set H) : Subgroup H) : Set H)
    exact Subgroup.inf_normalizer_le_normalizer_inf (Subgroup.mem_inf.mpr ⟨hcNQα, hcNC⟩)
  have hZαN : Zα ≤ N := by
    intro z hz
    refine ⟨hz.1, ?_⟩
    have hconj : c * z * c⁻¹ ∈ Zα :=
      (Subgroup.mem_normalizer_iff.mp hcNZα z).mp hz
    rw [commutatorElement_def]
    exact Zα.mul_mem hconj (Zα.inv_mem hz)
  have hZβN : Zβ ≤ N := by
    intro z hz
    refine ⟨hd.centerRight_le hz, ?_⟩
    rw [commutatorElement_eq_one_iff_mul_comm.mpr (hcZ z hz)]
    exact Zα.one_mem
  have hLαN : Lα ≤ Subgroup.normalizer (N : Set H) :=
    commutatorSubgroup_normalized hd.centerLeft_le hd.commutator_le hc1 hQα_N
  have hN_eq : N = Qα := hd.gen_left N hZαN hZβN (fun x hx => hx.1) hLαN
  intro x hx
  have hxN : x ∈ N := by
    rw [hN_eq]
    exact hx
  exact hxN.2

private def conjSubgroup (T : Subgroup H) (c : H) : Subgroup H :=
  { carrier := {g : H | g ∈ Subgroup.normalizer (T : Set H) ∧ ⁅c, g⁆ ∈ T},
    one_mem' := by
      refine ⟨Subgroup.one_mem _, ?_⟩
      rw [commutatorElement_one_right]
      exact T.one_mem,
    mul_mem' := by
      rintro g h ⟨hgN, hgT⟩ ⟨hhN, hhT⟩
      refine ⟨Subgroup.mul_mem _ hgN hhN, ?_⟩
      rw [commutatorElement_mul_right_eq_mul_conj]
      have hconj : g * ⁅c, h⁆ * g⁻¹ ∈ T :=
        (Subgroup.mem_normalizer_iff.mp hgN ⁅c, h⁆).mp hhT
      rw [show ⁅c, g⁆ * g * ⁅c, h⁆ * g⁻¹ = ⁅c, g⁆ * (g * ⁅c, h⁆ * g⁻¹) by group]
      exact T.mul_mem hgT hconj,
    inv_mem' := by
      rintro g ⟨hgN, hgT⟩
      refine ⟨Subgroup.inv_mem _ hgN, ?_⟩
      rw [commutatorElement_inv_right, ← commutatorElement_inv]
      simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgN) ⁅c, g⁆⁻¹).mp
        (T.inv_mem hgT) }

private theorem torus_le_trivOTwoQuot {L1 L2 S : Subgroup H} {J : Subgroup H}
    (hJtriv : ∀ j ∈ J, ∀ l ∈ oTwoPrime (f112saP1' L1 L2 S),
      ⁅j, l⁆ ∈ pCoreOf 2 (f112saP1' L1 L2 S)) :
    J ≤ trivOTwoQuot (oTwoPrime (f112saP1' L1 L2 S)) := by
  let Eα := f112saP1' L1 L2 S
  let Lα := oTwoPrime Eα
  let Qα := pCoreOf 2 Eα
  have hQα_le_Lα : Qα ≤ Lα := by
    change pCoreOf 2 Eα ≤ oTwoPrime Eα
    rw [← pCoreOf_oTwoPrime Eα]
    exact CFSG.LieType.BorelTits.pCoreOf_le 2 Lα
  have hJN_Lα : J ≤ Subgroup.normalizer (Lα : Set H) := by
    rw [Subgroup.le_normalizer_iff]
    intro j hj l hl
    have h := hJtriv j hj l hl
    have e : j * l * j⁻¹ = ⁅j, l⁆ * l := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact Lα.mul_mem (hQα_le_Lα h) hl
  intro j hj
  refine mem_trivOTwoQuot.mpr ⟨hJN_Lα hj, fun x hx => ?_⟩
  have h := hJtriv j hj x hx
  rw [commutatorElement_def, ← pCoreOf_oTwoPrime Eα] at h
  exact h

private theorem torus_commutator_mem_T {L1 L2 S : Subgroup H} {m n : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) {J : Subgroup H}
    (hJB : J ≤ bigB (oTwoPrime (f112saP1' L1 L2 S)) (oTwoPrime (f112saP2' L1 L2 S))
      (S ⊓ f112saK L1 L2 S))
    (hJtriv : ∀ j ∈ J, ∀ l ∈ oTwoPrime (f112saP1' L1 L2 S),
      ⁅j, l⁆ ∈ pCoreOf 2 (f112saP1' L1 L2 S))
    {c : H} (hcS : c ∈ S)
    (hc1 : c ∈ trivOTwoQuot (oTwoPrime (f112saP1' L1 L2 S)))
    (hc2 : c ∈ trivOTwoQuot (oTwoPrime (f112saP2' L1 L2 S))) :
    ∀ j ∈ J, ⁅c, j⁆ ∈ S ⊓ f112saK L1 L2 S := by
  classical
  let Eα := f112saP1' L1 L2 S
  let Eβ := f112saP2' L1 L2 S
  let Lα := oTwoPrime Eα
  let Lβ := oTwoPrime Eβ
  let Qα := pCoreOf 2 Eα
  let Qβ := pCoreOf 2 Eβ
  let T := S ⊓ f112saK L1 L2 S
  have hR : Hyp111R L1 L2 S := hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2
  have hT_le_Lα : T ≤ Lα := f112sa_T_le_oTwoPrime_P1'_of_hyp111R hF hR
  have hT_le_Lβ : T ≤ Lβ := f112sa_T_le_oTwoPrime_P2'_of_hyp111R hF hR
  have hQα_le_T : Qα ≤ T := by
    change pCoreOf 2 Eα ≤ S ⊓ f112saK L1 L2 S
    rw [← f112ll_pCoreOf_sup_eq hF hm hn h1 h2]
    exact le_sup_left
  have hQβ_le_T : Qβ ≤ T := by
    change pCoreOf 2 Eβ ≤ S ⊓ f112saK L1 L2 S
    rw [← f112ll_pCoreOf_sup_eq hF hm hn h1 h2]
    exact le_sup_right
  have hS_N_T : S ≤ Subgroup.normalizer (T : Set H) := by
    have hSK : S ≤ Subgroup.normalizer (f112saK L1 L2 S : Set H) :=
      (le_sup_right : S ≤ bigB L1 L2 S).trans (f112sa_bigB_le_normalizer_K hF)
    exact (le_inf Subgroup.le_normalizer hSK).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hB_N_T : bigB Lα Lβ T ≤ Subgroup.normalizer (T : Set H) := by
    refine sup_le (sup_le ?_ ?_) Subgroup.le_normalizer
    · have h : borelOf Lα T ≤ Subgroup.normalizer ((T ⊓ Lα : Subgroup H) : Set H) :=
        inf_le_right
      rwa [inf_eq_left.mpr hT_le_Lα] at h
    · have h : borelOf Lβ T ≤ Subgroup.normalizer ((T ⊓ Lβ : Subgroup H) : Set H) :=
        inf_le_right
      rwa [inf_eq_left.mpr hT_le_Lβ] at h
  let M : Subgroup H := conjSubgroup T c
  have hT_M : T ≤ M := by
    intro t ht
    refine ⟨Subgroup.le_normalizer ht, ?_⟩
    rw [commutatorElement_def]
    have hconj : c * t * c⁻¹ ∈ T :=
      (Subgroup.mem_normalizer_iff.mp (hS_N_T hcS) t).mp ht
    exact T.mul_mem hconj (T.inv_mem ht)
  have hBα_M : borelOf Lα T ≤ M := by
    intro g hg
    have hgN : g ∈ Subgroup.normalizer (T : Set H) :=
      hB_N_T (Subgroup.mem_sup_left (Subgroup.mem_sup_left hg))
    refine ⟨hgN, ?_⟩
    have hgLα : g ∈ Lα := CFSG.Quasithin.F1.borelOf_le Lα T hg
    have h := (mem_trivOTwoQuot.mp hc1).2 g hgLα
    have hQ : ⁅c, g⁆ ∈ Qα := by
      rwa [pCoreOf_oTwoPrime] at h
    exact hQα_le_T hQ
  have hBβ_M : borelOf Lβ T ≤ M := by
    intro g hg
    have hgN : g ∈ Subgroup.normalizer (T : Set H) :=
      hB_N_T (Subgroup.mem_sup_left (Subgroup.mem_sup_right hg))
    refine ⟨hgN, ?_⟩
    have hgLβ : g ∈ Lβ := CFSG.Quasithin.F1.borelOf_le Lβ T hg
    have h := (mem_trivOTwoQuot.mp hc2).2 g hgLβ
    have hQ : ⁅c, g⁆ ∈ Qβ := by
      rwa [pCoreOf_oTwoPrime] at h
    exact hQβ_le_T hQ
  have hBig_M : bigB Lα Lβ T ≤ M := sup_le (sup_le hBα_M hBβ_M) hT_M
  exact fun j hj => (hJB.trans hBig_M hj).2

private theorem torus_commutator_mem_pCoreOfLeft {L1 L2 S : Subgroup H} {m n : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) {J : Subgroup H}
    (hJB : J ≤ bigB (oTwoPrime (f112saP1' L1 L2 S)) (oTwoPrime (f112saP2' L1 L2 S))
      (S ⊓ f112saK L1 L2 S))
    (hJtriv : ∀ j ∈ J, ∀ l ∈ oTwoPrime (f112saP1' L1 L2 S),
      ⁅j, l⁆ ∈ pCoreOf 2 (f112saP1' L1 L2 S))
    {c : H} (hcS : c ∈ S)
    (hc1 : c ∈ trivOTwoQuot (oTwoPrime (f112saP1' L1 L2 S)))
    (hc2 : c ∈ trivOTwoQuot (oTwoPrime (f112saP2' L1 L2 S))) :
    ∀ j ∈ J, ⁅c, j⁆ ∈ pCoreOf 2 (f112saP1' L1 L2 S) := by
  classical
  let Eα := f112saP1' L1 L2 S
  let Lα := oTwoPrime Eα
  have hJ_triv : J ≤ trivOTwoQuot Lα := torus_le_trivOTwoQuot hJtriv
  have hcjT := torus_commutator_mem_T hF hm hn h1 h2 hJB hJtriv hcS hc1 hc2
  have hT_le_Lα : S ⊓ f112saK L1 L2 S ≤ Lα :=
    f112sa_T_le_oTwoPrime_P1'_of_hyp111R hF
      (hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2)
  obtain ⟨α, hαsurj, hαker⟩ :=
    exists_surjective_SL2_of_isL2Quot (f112ll_isL2Quot_oTwoPrime_P1' hF hm hn h1 h2)
  have hker : ∀ x : ↥Lα, α x = 1 ↔ (x : H) ∈ pCoreOf 2 Lα := by
    intro x
    rw [← MonoidHom.mem_ker, hαker, Subgroup.mem_subgroupOf]
  intro j hj
  have hcj_Lα : ⁅c, j⁆ ∈ Lα := hT_le_Lα (hcjT j hj)
  have hcj_triv : ⁅c, j⁆ ∈ trivOTwoQuot Lα := by
    have hprod : c * j * c⁻¹ * j⁻¹ ∈ trivOTwoQuot Lα :=
      (trivOTwoQuot Lα).mul_mem
        ((trivOTwoQuot Lα).mul_mem ((trivOTwoQuot Lα).mul_mem hc1 (hJ_triv hj))
          ((trivOTwoQuot Lα).inv_mem hc1)) ((trivOTwoQuot Lα).inv_mem (hJ_triv hj))
    simpa [commutatorElement_def] using hprod
  have h := mem_pCoreOf_of_mem_trivOTwoQuot α hαsurj hker hcj_triv hcj_Lα
  rwa [pCoreOf_oTwoPrime] at h

private theorem exists_mul_centralizes_torus {L1 L2 S : Subgroup H} {m n : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (hcomm : ⁅pCoreOf 2 (f112saP1' L1 L2 S), pCoreOf 2 (f112saP1' L1 L2 S)⁆ ≤
      centerOf (pCoreOf 2 (f112saP1' L1 L2 S))) {J : Subgroup H}
    (hJB : J ≤ bigB (oTwoPrime (f112saP1' L1 L2 S)) (oTwoPrime (f112saP2' L1 L2 S))
      (S ⊓ f112saK L1 L2 S))
    (hJtriv : ∀ j ∈ J, ∀ l ∈ oTwoPrime (f112saP1' L1 L2 S), ⁅j, l⁆ ∈
      pCoreOf 2 (f112saP1' L1 L2 S))
    (hJodd : Odd (Nat.card J)) {c : H} (hcS : c ∈ S)
    (hc1 : c ∈ trivOTwoQuot (oTwoPrime (f112saP1' L1 L2 S)))
    (hc2 : c ∈ trivOTwoQuot (oTwoPrime (f112saP2' L1 L2 S)))
    (hZ : ∀ x ∈ pCoreOf 2 (f112saP1' L1 L2 S),
      ⁅c, x⁆ ∈ centerOf (pCoreOf 2 (f112saP1' L1 L2 S))) :
    ∃ y ∈ pCoreOf 2 (f112saP1' L1 L2 S),
      y * c ∈ S ∧ y * c ∈ trivOTwoQuot (oTwoPrime (f112saP1' L1 L2 S)) ∧
        y * c ∈ Subgroup.centralizer (J : Set H) ∧
        ∀ x ∈ pCoreOf 2 (f112saP1' L1 L2 S),
          ⁅y * c, x⁆ ∈ centerOf (pCoreOf 2 (f112saP1' L1 L2 S)) := by
  classical
  let Eα := f112saP1' L1 L2 S
  let Lα := oTwoPrime Eα
  let Qα := pCoreOf 2 Eα
  let Zα := centerOf Qα
  let T := S ⊓ f112saK L1 L2 S
  have hQα_le_T : Qα ≤ T := by
    change pCoreOf 2 Eα ≤ S ⊓ f112saK L1 L2 S
    rw [← f112ll_pCoreOf_sup_eq hF hm hn h1 h2]
    exact le_sup_left
  have hQα_le_Lα : Qα ≤ Lα := by
    change pCoreOf 2 Eα ≤ oTwoPrime Eα
    rw [← pCoreOf_oTwoPrime Eα]
    exact CFSG.LieType.BorelTits.pCoreOf_le 2 Lα
  have hJ_triv : J ≤ trivOTwoQuot Lα := torus_le_trivOTwoQuot hJtriv
  have hjc : ∀ j ∈ J, ⁅c, j⁆ ∈ Qα :=
    torus_commutator_mem_pCoreOfLeft hF hm hn h1 h2 hJB hJtriv hcS hc1 hc2
  have hQα_N : Qα ≤ Subgroup.normalizer (Zα : Set H) := by
    change pCoreOf 2 Eα ≤ Subgroup.normalizer (centerOf (pCoreOf 2 Eα) : Set H)
    exact (CFSG.LieType.BorelTits.pCoreOf_le 2 Eα).trans
      (le_normalizer_centerOf_pCoreOf Eα)
  have hQeq : pCoreOf 2 Lα = Qα := pCoreOf_oTwoPrime Eα
  have hJN_Qα : J ≤ Subgroup.normalizer (Qα : Set H) := by
    have hJN_Lα : J ≤ Subgroup.normalizer (Lα : Set H) :=
      fun j hj => (mem_trivOTwoQuot.mp (hJ_triv hj)).1
    refine hJN_Lα.trans ?_
    have h := CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Lα
    rwa [hQeq] at h
  have hcNQα : c ∈ Subgroup.normalizer (Qα : Set H) := by
    have hcNLα : c ∈ Subgroup.normalizer (Lα : Set H) := (mem_trivOTwoQuot.mp hc1).1
    have h := CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Lα hcNLα
    rwa [hQeq] at h
  have hQα2 : IsPGroup 2 ↥Qα := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Eα
  have hc : ∀ j ∈ J, j * c * j⁻¹ * c⁻¹ ∈ Qα := by
    intro j hj
    have h := Qα.inv_mem (hjc j hj)
    have he : ⁅c, j⁆⁻¹ = j * c * j⁻¹ * c⁻¹ := by
      rw [commutatorElement_inv, commutatorElement_def]
    rwa [he] at h
  obtain ⟨y, hyQ, hyCent⟩ :=
    exists_mul_mem_centralizer_of_odd (Q := Qα) (J := J) hQα2 hJodd hJN_Qα hcNQα hc
  have hy_triv : y ∈ trivOTwoQuot Lα := by
    apply pCoreOf_le_trivOTwoQuot
    rw [pCoreOf_oTwoPrime]
    exact hyQ
  refine ⟨y, hyQ, ?_, (trivOTwoQuot Lα).mul_mem hy_triv hc1, hyCent, fun x hxQ => ?_⟩
  · exact S.mul_mem (hQα_le_T hyQ |>.1) hcS
  · have hcx : ⁅c, x⁆ ∈ Zα := hZ x hxQ
    have hconj : y * ⁅c, x⁆ * y⁻¹ ∈ Zα :=
      (Subgroup.mem_normalizer_iff.mp (hQα_N hyQ) ⁅c, x⁆).mp hcx
    have hyx : ⁅y, x⁆ ∈ Zα :=
      hcomm (Subgroup.commutator_mem_commutator hyQ hxQ)
    rw [commutatorElement_mul_left_eq_conj_mul]
    exact Zα.mul_mem hconj hyx

private theorem torus_commutator_conj_mem_center {L1 L2 S : Subgroup H}
    (hcomm : ⁅pCoreOf 2 (f112saP1' L1 L2 S), pCoreOf 2 (f112saP1' L1 L2 S)⁆ ≤
      centerOf (pCoreOf 2 (f112saP1' L1 L2 S))) {J : Subgroup H}
    (hJtriv : ∀ j ∈ J, ∀ l ∈ oTwoPrime (f112saP1' L1 L2 S),
      ⁅j, l⁆ ∈ pCoreOf 2 (f112saP1' L1 L2 S))
    {c₃ : H} (hc3Cent : c₃ ∈ Subgroup.centralizer (J : Set H))
    (hc3Z : ∀ x ∈ pCoreOf 2 (f112saP1' L1 L2 S),
      ⁅c₃, x⁆ ∈ centerOf (pCoreOf 2 (f112saP1' L1 L2 S)))
    {l : H} (hl : l ∈ oTwoPrime (f112saP1' L1 L2 S))
    (hmQ : ⁅c₃, l⁆ ∈ pCoreOf 2 (f112saP1' L1 L2 S)) :
    ∀ j ∈ J, j * ⁅c₃, l⁆ * j⁻¹ * ⁅c₃, l⁆⁻¹ ∈
      centerOf (pCoreOf 2 (f112saP1' L1 L2 S)) := by
  classical
  let Eα := f112saP1' L1 L2 S
  let Lα := oTwoPrime Eα
  let Qα := pCoreOf 2 Eα
  let Zα := centerOf Qα
  intro j hj
  have hcj : j * c₃ = c₃ * j :=
    Subgroup.mem_centralizer_iff.mp hc3Cent j hj
  let u : H := ⁅j, l⁆
  have huQ : u ∈ Qα := hJtriv j hj l hl
  have hjl : j * l * j⁻¹ = u * l := by
    change j * l * j⁻¹ = ⁅j, l⁆ * l
    rw [commutatorElement_def]
    group
  have hstep : j * (c₃ * l * c₃⁻¹ * l⁻¹) * j⁻¹ =
      c₃ * (j * l * j⁻¹) * c₃⁻¹ * (j * l * j⁻¹)⁻¹ := by
    have hcomm : Commute j c₃ := hcj
    calc
      j * (c₃ * l * c₃⁻¹ * l⁻¹) * j⁻¹
          = (j * c₃ * j⁻¹) * (j * l * j⁻¹) * (j * c₃⁻¹ * j⁻¹) *
              (j * l * j⁻¹)⁻¹ := by group
      _ = c₃ * (j * l * j⁻¹) * c₃⁻¹ * (j * l * j⁻¹)⁻¹ := by
        have h1 : j * c₃ * j⁻¹ = c₃ := by rw [hcj]; group
        have h2 : j * c₃⁻¹ * j⁻¹ = c₃⁻¹ := by rw [hcomm.inv_right.eq]; group
        rw [h1, h2]
  have hjmj : j * ⁅c₃, l⁆ * j⁻¹ = ⁅c₃, u * l⁆ := by
    change j * (c₃ * l * c₃⁻¹ * l⁻¹) * j⁻¹ = ⁅c₃, u * l⁆
    rw [hstep, hjl]
    rfl
  have hmul : ⁅c₃, u * l⁆ = ⁅c₃, u⁆ * u * ⁅c₃, l⁆ * u⁻¹ := by
    rw [commutatorElement_mul_right_eq_mul_conj]
  have hfin : j * ⁅c₃, l⁆ * j⁻¹ * ⁅c₃, l⁆⁻¹ =
      ⁅c₃, u⁆ * (u * ⁅c₃, l⁆ * u⁻¹ * ⁅c₃, l⁆⁻¹) := by
    rw [hjmj, hmul]
    group
  rw [hfin]
  exact Zα.mul_mem (hc3Z u huQ)
    (hcomm (Subgroup.commutator_mem_commutator huQ hmQ))

private theorem commutator_torus_mem_center {L1 L2 S : Subgroup H}
    (hcomm : ⁅pCoreOf 2 (f112saP1' L1 L2 S), pCoreOf 2 (f112saP1' L1 L2 S)⁆ ≤
      centerOf (pCoreOf 2 (f112saP1' L1 L2 S))) {J : Subgroup H}
    (hJtriv : ∀ j ∈ J, ∀ l ∈ oTwoPrime (f112saP1' L1 L2 S), ⁅j, l⁆ ∈
      pCoreOf 2 (f112saP1' L1 L2 S))
    (hJodd : Odd (Nat.card J))
    (hJcent : pCoreOf 2 (f112saP1' L1 L2 S) ⊓ Subgroup.centralizer (J : Set H) = ⊥)
    {c₃ : H} (hc3Cent : c₃ ∈ Subgroup.centralizer (J : Set H))
    (hc3 : c₃ ∈ trivOTwoQuot (oTwoPrime (f112saP1' L1 L2 S)))
    (hc3Z : ∀ x ∈ pCoreOf 2 (f112saP1' L1 L2 S),
      ⁅c₃, x⁆ ∈ centerOf (pCoreOf 2 (f112saP1' L1 L2 S))) :
    ∀ l ∈ oTwoPrime (f112saP1' L1 L2 S),
      ⁅c₃, l⁆ ∈ centerOf (pCoreOf 2 (f112saP1' L1 L2 S)) := by
  classical
  let Eα := f112saP1' L1 L2 S
  let Lα := oTwoPrime Eα
  let Qα := pCoreOf 2 Eα
  let Zα := centerOf Qα
  have hQα_le_Lα : Qα ≤ Lα := by
    change pCoreOf 2 Eα ≤ oTwoPrime Eα
    rw [← pCoreOf_oTwoPrime Eα]
    exact CFSG.LieType.BorelTits.pCoreOf_le 2 Lα
  have hQα_N : Qα ≤ Subgroup.normalizer (Zα : Set H) := by
    change pCoreOf 2 Eα ≤ Subgroup.normalizer (centerOf (pCoreOf 2 Eα) : Set H)
    exact (CFSG.LieType.BorelTits.pCoreOf_le 2 Eα).trans
      (le_normalizer_centerOf_pCoreOf Eα)
  have hJN_Lα : J ≤ Subgroup.normalizer (Lα : Set H) := by
    rw [Subgroup.le_normalizer_iff]
    intro j hj x hx
    have h := hJtriv j hj x hx
    have e : j * x * j⁻¹ = ⁅j, x⁆ * x := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact Lα.mul_mem (hQα_le_Lα h) hx
  have hQeq : pCoreOf 2 Lα = Qα := pCoreOf_oTwoPrime Eα
  have hJN_Qα : J ≤ Subgroup.normalizer (Qα : Set H) := by
    have h := CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Lα
    rw [hQeq] at h
    exact hJN_Lα.trans h
  have hJN_Zα : J ≤ Subgroup.normalizer (Zα : Set H) := by
    refine hJN_Qα.trans ?_
    intro g hg
    have hgC := CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer Qα hg
    change g ∈ Subgroup.normalizer
      ((Qα ⊓ Subgroup.centralizer (Qα : Set H) : Subgroup H) : Set H)
    exact Subgroup.inf_normalizer_le_normalizer_inf (Subgroup.mem_inf.mpr ⟨hg, hgC⟩)
  have hZα2 : IsPGroup 2 ↥Zα :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Eα).to_le inf_le_left
  intro l hl
  let m : H := ⁅c₃, l⁆
  have hmQ : m ∈ Qα := by
    have h := (mem_trivOTwoQuot.mp hc3).2 l hl
    rw [pCoreOf_oTwoPrime] at h
    exact h
  have hmN : m ∈ Subgroup.normalizer (Zα : Set H) := hQα_N hmQ
  have hcommJ := torus_commutator_conj_mem_center hcomm hJtriv hc3Cent hc3Z hl hmQ
  obtain ⟨z, hzZ, hzC⟩ :=
    exists_mul_mem_centralizer_of_odd (Q := Zα) (J := J) hZα2 hJodd hJN_Zα hmN hcommJ
  have hZα_le_Qα : Zα ≤ Qα := inf_le_left
  have hzmQ : z * m ∈ Qα := Qα.mul_mem (hZα_le_Qα hzZ) hmQ
  have hzm_bot : z * m ∈ Qα ⊓ Subgroup.centralizer (J : Set H) := ⟨hzmQ, hzC⟩
  rw [hJcent] at hzm_bot
  have hzm1 : z * m = 1 := by simpa using hzm_bot
  have hmZ : m ∈ Zα := by
    have hm_eq : m = z⁻¹ := by
      calc m = z⁻¹ * (z * m) := by group
        _ = z⁻¹ := by rw [hzm1, mul_one]
    rw [hm_eq]
    exact Zα.inv_mem hzZ
  exact hmZ

private theorem mem_centralizer_of_commutator_le_center_of_perfect {L : Subgroup H}
    (hperf : ⁅L, L⁆ = L) {z : H}
    (hcomm : ∀ l ∈ L, ⁅z, l⁆ ∈ centerOf L) :
    z ∈ Subgroup.centralizer (L : Set H) := by
  have hzcent : ∀ l ∈ L, ⁅z, l⁆ ∈ Subgroup.centralizer (L : Set H) :=
    fun l hl => (hcomm l hl).2
  let φ : ↥L →* H :=
    { toFun := fun l => ⁅z, (l : H)⁆
      map_one' := commutatorElement_one_right z
      map_mul' := by
        intro x y
        change ⁅z, (x : H) * (y : H)⁆ = ⁅z, (x : H)⁆ * ⁅z, (y : H)⁆
        rw [commutatorElement_mul_right_eq_mul_conj]
        have hx : (x : H) * ⁅z, (y : H)⁆ * (x : H)⁻¹ = ⁅z, (y : H)⁆ := by
          rw [Subgroup.mem_centralizer_iff.mp (hzcent y y.2) (x : H) x.2]
          group
        rw [show ⁅z, (x : H)⁆ * (x : H) * ⁅z, (y : H)⁆ * (x : H)⁻¹ =
          ⁅z, (x : H)⁆ * ((x : H) * ⁅z, (y : H)⁆ * (x : H)⁻¹) by group, hx] }
  have hcommφ : ∀ x y : ↥L, ⁅φ x, φ y⁆ = 1 := by
    intro x y
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_centralizer_iff.mp (hzcent x x.2) (φ y) (hcomm y y.2).1).symm
  have hle : ⁅L, L⁆ ≤ Subgroup.centralizer ({z} : Set H) := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h : φ (⁅(⟨x, hx⟩ : ↥L), (⟨y, hy⟩ : ↥L)⁆) = 1 := by
      rw [map_commutatorElement]
      exact hcommφ ⟨x, hx⟩ ⟨y, hy⟩
    exact (commutatorElement_eq_one_iff_mul_comm.mp h).symm
  rw [hperf] at hle
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hl)

private theorem exists_torus_element {L1 L2 S : Subgroup H} {n : ℕ}
    (hF : F112HypW L1 L2 S) (hn : 2 ≤ n) (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    ∃ k : H, k ∈ f112saX2 L1 L2 S ∧ k ∈ oTwoPrime (f112saP2' L1 L2 S) ∧
      k ≠ 1 ∧ Odd (orderOf k) := by
  obtain ⟨D, hD, hDcard⟩ := f112_exists_torus_X2 hF (by omega) h2
  have hDge : 3 ≤ Nat.card D := by
    rw [hDcard]
    have h4 : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  have hDne : D ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hDge
    omega
  obtain ⟨k, hk1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hDne
  have hk1' : (k : H) ≠ 1 := fun h => hk1 (Subtype.ext h)
  have hkX2 : (k : H) ∈ f112saX2 L1 L2 S := (Subgroup.mem_inf.mp (hD k.2)).1
  have hkLβ : (k : H) ∈ oTwoPrime (f112saP2' L1 L2 S) :=
    (f112sa_oTwoRes_le_oTwoPrime_P2'_of_isL2Quot hn h2)
      ((f112sa_X2_le_oTwoRes L1 L2 S) hkX2)
  have hkodd : Odd (orderOf (k : H)) := by
    have hoddD : Odd (Nat.card D) := by
      rw [hDcard]
      exact odd_two_pow_sub_one (by omega)
    have hdvd : orderOf (k : ↥D) ∣ Nat.card D := orderOf_dvd_natCard k
    rw [Subgroup.orderOf_mk] at hdvd
    exact Odd.of_dvd_nat hoddD hdvd
  exact ⟨(k : H), hkX2, hkLβ, hk1', hkodd⟩

private theorem centerOf_T_inf_centralizer_eq_bot {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (hR : Hyp111R L1 L2 S)
    {F : Type} [Field F] [CharP F 2]
    {α : ↥(oTwoPrime (f112saP2' L1 L2 S)) →* SL(2, F)}
    (hker : α.ker = CFSG.pCore 2 ↥(oTwoPrime (f112saP2' L1 L2 S)))
    (hnat : IsNatSecOf (oTwoPrime (f112saP2' L1 L2 S))
      (centerOf (pCoreOf 2 (oTwoPrime (f112saP2' L1 L2 S)))) ⊥ α)
    {k : H} (hkLβ : k ∈ oTwoPrime (f112saP2' L1 L2 S))
    (hkodd : Odd (orderOf k)) (hk1 : k ≠ 1) :
    centerOf (S ⊓ f112saK L1 L2 S) ⊓
      Subgroup.centralizer ({k} : Set H) = ⊥ := by
  classical
  let Lβ := oTwoPrime (f112saP2' L1 L2 S)
  let kk : ↥Lβ := ⟨k, hkLβ⟩
  have hαk1 : α kk ≠ 1 := by
    intro h1k
    have hmem : kk ∈ CFSG.pCore 2 ↥Lβ := by
      rw [← hker, MonoidHom.mem_ker]
      exact h1k
    obtain ⟨j, hj⟩ :=
      (IsPGroup.iff_orderOf.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥Lβ))) ⟨kk, hmem⟩
    have hj' : orderOf (⟨kk, hmem⟩ : ↥(CFSG.pCore 2 ↥Lβ)) = 2 ^ j := hj
    have hoddkk : Odd (orderOf kk) := by
      rw [Subgroup.orderOf_mk]
      exact hkodd
    rw [Subgroup.orderOf_mk] at hj
    rw [hj] at hoddkk
    have hj0 : j = 0 := by
      by_contra hj0
      exact (Nat.not_even_iff_odd.mpr hoddkk)
        (Even.pow_of_ne_zero (a := (2 : ℕ)) even_two hj0)
    rw [hj0, pow_zero] at hj'
    have hkk1 : kk = 1 := by
      simpa using congrArg (fun x : ↥(CFSG.pCore 2 ↥Lβ) => (x : ↥Lβ))
        (orderOf_eq_one_iff.mp hj')
    exact hk1 (Subtype.ext_iff.mp hkk1)
  refine le_antisymm ?_ bot_le
  intro z hz
  have hzT : z ∈ centerOf (S ⊓ f112saK L1 L2 S) := hz.1
  have hzC : z ∈ Subgroup.centralizer ({k} : Set H) := hz.2
  have hzQ : z ∈ centerOf (pCoreOf 2 (f112saP2' L1 L2 S)) :=
    f112sa_centerOf_T_le_P2'_of_hyp111R hF hR hzT
  have hzQ' : z ∈ centerOf (pCoreOf 2 (oTwoPrime (f112saP2' L1 L2 S))) := by
    rwa [pCoreOf_oTwoPrime]
  have hzk : (kk : H) * z = z * (kk : H) :=
    Subgroup.mem_centralizer_iff.mp hzC k (Set.mem_singleton k)
  have hzbot : z ∈ (⊥ : Subgroup H) :=
    hnat.mem_of_commute_of_odd
      (by rw [Subgroup.orderOf_mk]; exact hkodd) hαk1 hzQ' hzk
  simpa using hzbot

theorem f112ll_W_eq_bot_of_isNatSecOf {L1 L2 S : Subgroup H} {m n : ℕ} (hF : F112HypW L1 L2 S)
    (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1)) (h2 : IsL2Quot n (oTwoQuot ↥L2))
    {F : Type} [Field F] [CharP F 2] {α : ↥(oTwoPrime (f112saP2' L1 L2 S)) →* SL(2, F)}
    (hker : α.ker = CFSG.pCore 2 ↥(oTwoPrime (f112saP2' L1 L2 S)))
    (hnat : IsNatSecOf (oTwoPrime (f112saP2' L1 L2 S))
      (centerOf (pCoreOf 2 (oTwoPrime (f112saP2' L1 L2 S)))) ⊥ α) :
    f112saW L1 L2 S = ⊥ := by
  have hR : Hyp111R L1 L2 S := hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2
  obtain ⟨k, hkX2, hkLβ, hk1, hkodd⟩ := exists_torus_element hF hn h2
  have hkK : k ∈ f112saK L1 L2 S := Subgroup.mem_sup_right hkX2
  have hZk : centerOf (S ⊓ f112saK L1 L2 S) ⊓
      Subgroup.centralizer ({k} : Set H) = ⊥ :=
    centerOf_T_inf_centralizer_eq_bot hF hR hker hnat hkLβ hkodd hk1
  exact f112saW_eq_bot_of_centerOf_inf_centralizer_le_of_hyp111R hF hR hkK hkK
    (by rw [hZk]; exact bot_le) (by rw [hZk]; exact bot_le)

private theorem commutator_zpowers_mem_inf {L1 L2 S : Subgroup H} {m n : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) {k : H}
    (hkLβ : k ∈ oTwoPrime (f112saP2' L1 L2 S))
    (hktriv : k ∈ trivOTwoQuot (oTwoPrime (f112saP1' L1 L2 S))) :
    ∀ h ∈ Subgroup.zpowers k, ∀ l ∈ pCoreOf 2 (f112saP2' L1 L2 S),
      h * l * h⁻¹ * l⁻¹ ∈ pCoreOf 2 (f112saP1' L1 L2 S) ⊓
        pCoreOf 2 (f112saP2' L1 L2 S) := by
  classical
  let Eα := f112saP1' L1 L2 S
  let Eβ := f112saP2' L1 L2 S
  let Lα := oTwoPrime Eα
  let Lβ := oTwoPrime Eβ
  let Qα := pCoreOf 2 Eα
  let Qβ := pCoreOf 2 Eβ
  let T := S ⊓ f112saK L1 L2 S
  have hR : Hyp111R L1 L2 S := hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2
  have hT_le_Lα : T ≤ Lα := f112sa_T_le_oTwoPrime_P1'_of_hyp111R hF hR
  have hQβ_le_T : Qβ ≤ T := by
    change pCoreOf 2 Eβ ≤ S ⊓ f112saK L1 L2 S
    rw [← f112ll_pCoreOf_sup_eq hF hm hn h1 h2]
    exact le_sup_right
  have hzpY : Subgroup.zpowers k ≤ oTwoPrime Eβ ⊓ trivOTwoQuot Lα :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨hkLβ, hktriv⟩)
  intro h hh l hl
  have hhY := hzpY hh
  have hhtriv : h ∈ trivOTwoQuot Lα := (Subgroup.mem_inf.mp hhY).2
  have hhLβ : h ∈ Lβ := (Subgroup.mem_inf.mp hhY).1
  have hlLα : l ∈ Lα := hT_le_Lα (hQβ_le_T hl)
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · have hmem := (mem_trivOTwoQuot.mp hhtriv).2 l hlLα
    rwa [pCoreOf_oTwoPrime] at hmem
  · have hhNQβ : h ∈ Subgroup.normalizer (Qβ : Set H) :=
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Eβ) ((oTwoPrime_le Eβ) hhLβ)
    exact Qβ.mul_mem ((Subgroup.mem_normalizer_iff.mp hhNQβ l).mp hl) (Qβ.inv_mem hl)

private theorem Qβ_le_Qα_of_odd_mem_triv {L1 L2 S : Subgroup H} {m n : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (hcent : ∀ k ∈ oTwoPrime (f112saP2' L1 L2 S), Odd (orderOf k) → k ≠ 1 →
      pCoreOf 2 (f112saP2' L1 L2 S) ⊓ Subgroup.centralizer ({k} : Set H) ≤
        pCoreOf 2 (f112saP1' L1 L2 S)) {k : H}
    (hkLβ : k ∈ oTwoPrime (f112saP2' L1 L2 S))
    (hktriv : k ∈ trivOTwoQuot (oTwoPrime (f112saP1' L1 L2 S)))
    (hkodd : Odd (orderOf k)) (hk1 : k ≠ 1) :
    pCoreOf 2 (f112saP2' L1 L2 S) ≤ pCoreOf 2 (f112saP1' L1 L2 S) := by
  classical
  let Eα := f112saP1' L1 L2 S
  let Eβ := f112saP2' L1 L2 S
  let Lα := oTwoPrime Eα
  let Lβ := oTwoPrime Eβ
  let Qα := pCoreOf 2 Eα
  let Qβ := pCoreOf 2 Eβ
  let T := S ⊓ f112saK L1 L2 S
  have hR : Hyp111R L1 L2 S := hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2
  have hT_le_Lα : T ≤ Lα := f112sa_T_le_oTwoPrime_P1'_of_hyp111R hF hR
  have hQβ_le_T : Qβ ≤ T := by
    change pCoreOf 2 Eβ ≤ S ⊓ f112saK L1 L2 S
    rw [← f112ll_pCoreOf_sup_eq hF hm hn h1 h2]
    exact le_sup_right
  have hkNQα : k ∈ Subgroup.normalizer (Qα : Set H) := by
    have h : k ∈ Subgroup.normalizer (pCoreOf 2 Lα : Set H) :=
      CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Lα
        (mem_trivOTwoQuot.mp hktriv).1
    have hQeq : pCoreOf 2 Lα = Qα := pCoreOf_oTwoPrime Eα
    rwa [hQeq] at h
  have hkNQβ : k ∈ Subgroup.normalizer (Qβ : Set H) :=
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Eβ) ((oTwoPrime_le Eβ) hkLβ)
  have hky_inf : k ∈ Subgroup.normalizer ((Qα ⊓ Qβ : Subgroup H) : Set H) :=
    Subgroup.inf_normalizer_le_normalizer_inf (Subgroup.mem_inf.mpr ⟨hkNQα, hkNQβ⟩)
  have hHQ : Subgroup.zpowers k ≤
      Subgroup.normalizer ((Qα ⊓ Qβ : Subgroup H) : Set H) :=
    Subgroup.zpowers_le.mpr hky_inf
  have hQβNQα : Qβ ≤ Subgroup.normalizer (Qα : Set H) :=
    (hQβ_le_T.trans hT_le_Lα).trans ((oTwoPrime_le Eα).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Eα))
  have hLQ : Qβ ≤ Subgroup.normalizer ((Qα ⊓ Qβ : Subgroup H) : Set H) :=
    (le_inf hQβNQα Subgroup.le_normalizer).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hQinf2 : IsPGroup 2 ↥(Qα ⊓ Qβ) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Eα).to_le inf_le_left
  have hcop : Nat.Coprime (Nat.card ↥(Subgroup.zpowers k)) (Nat.card ↥(Qα ⊓ Qβ)) := by
    rw [Nat.card_zpowers]
    obtain ⟨a, ha⟩ := hQinf2.exists_card_eq
    rw [ha]
    exact Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr hkodd)
  have hcomm := commutator_zpowers_mem_inf hF hm hn h1 h2 hkLβ hktriv
  have hQβ_le_Qα : Qβ ≤ Qα := by
    intro l hl
    obtain ⟨q, hqQ, c, hcC, hl_eq⟩ :=
      exists_mul_mem_inf_centralizer_of_coprime (L := Qβ) (Q := Qα ⊓ Qβ)
        (H := Subgroup.zpowers k) inf_le_right hLQ hHQ hcop hcomm hl
    have hcQβ : c ∈ Qβ := hcC.1
    have hcCent : c ∈ Subgroup.centralizer ({k} : Set H) :=
      Subgroup.centralizer_le
        (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers k)) hcC.2
    have hck := hcent k hkLβ hkodd hk1
    have hcQα : c ∈ Qα := hck (Subgroup.mem_inf.mpr ⟨hcQβ, hcCent⟩)
    rw [hl_eq]
    exact Qα.mul_mem hqQ.1 hcQα
  exact hQβ_le_Qα

theorem f112ll_eq_one_of_mem_trivOTwoQuot_of_centralizer_le {L1 L2 S : Subgroup H} {m n : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (hcent : ∀ k ∈ oTwoPrime (f112saP2' L1 L2 S), Odd (orderOf k) → k ≠ 1 →
      pCoreOf 2 (f112saP2' L1 L2 S) ⊓ Subgroup.centralizer ({k} : Set H) ≤
        pCoreOf 2 (f112saP1' L1 L2 S))
    (hnot : ¬ pCoreOf 2 (f112saP2' L1 L2 S) ≤ pCoreOf 2 (f112saP1' L1 L2 S)) {k : H}
    (hk : k ∈ oTwoPrime (f112saP2' L1 L2 S)) (hkodd : Odd (orderOf k))
    (hktriv : k ∈ trivOTwoQuot (oTwoPrime (f112saP1' L1 L2 S))) : k = 1 := by
  by_contra hk1
  exact hnot (Qβ_le_Qα_of_odd_mem_triv hF hm hn h1 h2 hcent hk hktriv hkodd hk1)

private theorem X2_inf_triv_isPGroup {L1 L2 S : Subgroup H} {m n : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) (hd : TransferLeftData L1 L2 S) :
    IsPGroup 2 ↥(f112saX2 L1 L2 S ⊓
      trivOTwoQuot (oTwoPrime (f112saP1' L1 L2 S))) := by
  classical
  let Y := f112saX2 L1 L2 S ⊓ trivOTwoQuot (oTwoPrime (f112saP1' L1 L2 S))
  by_contra hnot
  obtain ⟨y, p, hp, hpodd, hyord⟩ := exists_odd_prime_order_of_not_isPGroup_two hnot
  let k : H := (y : H)
  have hkY : k ∈ Y := y.2
  have hkord : orderOf k = p :=
    (Subgroup.orderOf_mk (H := Y) (y : H) y.2).symm.trans hyord
  have hkodd : Odd (orderOf k) := by rw [hkord]; exact hpodd
  have hk1 : k ≠ 1 := by
    intro h1k
    have h : orderOf k = 1 := by rw [h1k]; exact orderOf_one
    rw [hkord] at h
    exact hp.ne_one h
  have hkLβ : k ∈ oTwoPrime (f112saP2' L1 L2 S) :=
    (f112sa_oTwoRes_le_oTwoPrime_P2'_of_isL2Quot hn h2)
      ((f112sa_X2_le_oTwoRes L1 L2 S) (Subgroup.mem_inf.mp hkY).1)
  have hktriv : k ∈ trivOTwoQuot (oTwoPrime (f112saP1' L1 L2 S)) :=
    (Subgroup.mem_inf.mp hkY).2
  exact hk1 (hd.eq_one_of_mem_trivOTwoQuot k hkLβ hkodd hktriv)

private theorem X2_inf_triv_le_T {L1 L2 S : Subgroup H} {m n : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) (hd : TransferLeftData L1 L2 S) :
    f112saX2 L1 L2 S ⊓ trivOTwoQuot (oTwoPrime (f112saP1' L1 L2 S)) ≤
      S ⊓ f112saK L1 L2 S := by
  classical
  let Y := f112saX2 L1 L2 S ⊓ trivOTwoQuot (oTwoPrime (f112saP1' L1 L2 S))
  let T := S ⊓ f112saK L1 L2 S
  have hR : Hyp111R L1 L2 S := hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2
  have hY2 : IsPGroup 2 ↥Y := X2_inf_triv_isPGroup hF hm hn h1 h2 hd
  have hY_K : Y ≤ f112saK L1 L2 S :=
    inf_le_left.trans (by rw [f112saK]; exact le_sup_right)
  have hK_N_T : f112saK L1 L2 S ≤ Subgroup.normalizer (T : Set H) := by
    have h : f112saK L1 L2 S ≤
        Subgroup.normalizer (pCoreOf 2 (f112saK L1 L2 S) : Set H) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
    rwa [f112ll_pCoreOf_K_eq hF hm hn h1 h2] at h
  have hY_N_T : Y ≤ Subgroup.normalizer (T : Set H) := hY_K.trans hK_N_T
  have hT2 : IsPGroup 2 ↥T := (f112sa_T_sylow_K_of_hyp111R hF hR).isPGroup
  have hsup2 : IsPGroup 2 ↥(Y ⊔ T) := hY2.to_sup_of_normal_right' hT2 hY_N_T
  have hsupK : Y ⊔ T ≤ f112saK L1 L2 S := sup_le hY_K inf_le_right
  exact le_sup_left.trans
    (CFSG.GroupTheory.PermSylowTwo.le_of_isSylowTwoOf_of_isPGroup
      (f112sa_T_sylow_K_of_hyp111R hF hR) le_sup_right hsupK hsup2)

theorem TransferLeftData.X2_inf_trivOTwoQuot_le {L1 L2 S : Subgroup H} {m n : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) (hd : TransferLeftData L1 L2 S) :
    f112saX2 L1 L2 S ⊓ trivOTwoQuot (oTwoPrime (f112saP1' L1 L2 S)) ≤
      S ⊓ f112saK L1 L2 S := by
  exact X2_inf_triv_le_T hF hm hn h1 h2 hd

private theorem conj_mem_trivOTwoQuot {L : Subgroup H} {g : H}
    (hg : g ∈ Subgroup.normalizer (L : Set H)) {x : H} (hx : x ∈ trivOTwoQuot L) :
    g * x * g⁻¹ ∈ trivOTwoQuot L := by
  obtain ⟨hxN, hxQ⟩ := mem_trivOTwoQuot.mp hx
  have hgInv : g⁻¹ ∈ Subgroup.normalizer (L : Set H) :=
    (Subgroup.normalizer (L : Set H)).inv_mem hg
  refine mem_trivOTwoQuot.mpr ⟨?_, ?_⟩
  · exact (Subgroup.normalizer (L : Set H)).mul_mem
      ((Subgroup.normalizer (L : Set H)).mul_mem hg hxN)
      ((Subgroup.normalizer (L : Set H)).inv_mem hg)
  · intro l hl
    have hl' : g⁻¹ * l * g ∈ L := by
      simpa using (Subgroup.mem_normalizer_iff.mp hgInv l).mp hl
    have hcomm : (g * x * g⁻¹) * l * (g * x * g⁻¹)⁻¹ * l⁻¹ =
        g * (x * (g⁻¹ * l * g) * x⁻¹ * (g⁻¹ * l * g)⁻¹) * g⁻¹ := by
      group
    rw [hcomm]
    exact (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L hg) _).mp
      (hxQ (g⁻¹ * l * g) hl')

private theorem f112ll_commutator_mem_T_of_torus {L1 L2 S D : Subgroup H} {m n : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) (hd : TransferLeftData L1 L2 S) {c : H} (hcS : c ∈ S)
    (hDX2 : D ≤ f112saX2 L1 L2 S)
    (hcα : c ∈ trivOTwoQuot (oTwoPrime (f112saP1' L1 L2 S))) :
    ∀ d ∈ D, d * c * d⁻¹ * c⁻¹ ∈ S ⊓ f112saK L1 L2 S := by
  let Lα := oTwoPrime (f112saP1' L1 L2 S)
  intro d hdD
  have hdX2 : d ∈ f112saX2 L1 L2 S := hDX2 hdD
  have hcdX2 : c * d * c⁻¹ * d⁻¹ ∈ f112saX2 L1 L2 S := by
    have hconj : c * d * c⁻¹ ∈ f112saX2 L1 L2 S :=
      (Subgroup.mem_normalizer_iff.mp
        (f112sa_bigB_le_normalizer_X2 hF ((le_sup_right : S ≤ bigB L1 L2 S) hcS)) d).mp hdX2
    exact (f112saX2 L1 L2 S).mul_mem hconj ((f112saX2 L1 L2 S).inv_mem hdX2)
  have hcdtriv : c * d * c⁻¹ * d⁻¹ ∈ trivOTwoQuot Lα := by
    have hdE : d ∈ f112saP1' L1 L2 S :=
      (le_sup_right : f112saX2 L1 L2 S ≤ f112saP1' L1 L2 S) hdX2
    have hdN : d ∈ Subgroup.normalizer (Lα : Set H) :=
      mem_normalizer_oTwoPrime (Subgroup.le_normalizer (H := f112saP1' L1 L2 S) hdE)
    have hconj := conj_mem_trivOTwoQuot hdN ((trivOTwoQuot Lα).inv_mem hcα)
    have hmul := (trivOTwoQuot Lα).mul_mem hcα hconj
    simpa [mul_assoc] using hmul
  have hmem : c * d * c⁻¹ * d⁻¹ ∈ f112saX2 L1 L2 S ⊓ trivOTwoQuot Lα :=
    ⟨hcdX2, hcdtriv⟩
  have hle := hd.X2_inf_trivOTwoQuot_le hF hm hn h1 h2
  have hcdT : c * d * c⁻¹ * d⁻¹ ∈ S ⊓ f112saK L1 L2 S := hle hmem
  have hinv := (S ⊓ f112saK L1 L2 S).inv_mem hcdT
  simpa [mul_assoc] using hinv

private theorem f112ll_exists_correction_of_left {L1 L2 S : Subgroup H} {m n : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) (hd : TransferLeftData L1 L2 S) {c : H} (hcS : c ∈ S)
    (hcα : c ∈ trivOTwoQuot (oTwoPrime (f112saP1' L1 L2 S))) :
    ∃ t ∈ S ⊓ f112saK L1 L2 S,
      t * c ∈ trivOTwoQuot (oTwoPrime (f112saP2' L1 L2 S)) := by
  classical
  let Lα := oTwoPrime (f112saP1' L1 L2 S)
  let Lβ := oTwoPrime (f112saP2' L1 L2 S)
  let Qα := pCoreOf 2 (f112saP1' L1 L2 S)
  let Qβ := pCoreOf 2 (f112saP2' L1 L2 S)
  let T := S ⊓ f112saK L1 L2 S
  have hR : Hyp111R L1 L2 S := hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2
  have hSB : S ≤ bigB L1 L2 S := le_sup_right
  have hSNα : S ≤ Subgroup.normalizer (f112saP1' L1 L2 S : Set H) :=
    (hSB.trans (le_sup_right : bigB L1 L2 S ≤ f112P1 L1 L2 S)).trans
      (f112sa_P1_le_normalizer_P1' hF)
  have hSNβ : S ≤ Subgroup.normalizer (f112saP2' L1 L2 S : Set H) :=
    (hSB.trans (le_sup_right : bigB L1 L2 S ≤ f112P2 L1 L2 S)).trans
      (f112sa_P2_le_normalizer_P2' hF)
  obtain ⟨D, hD, hDcard⟩ := f112_exists_torus_X2 hF (by omega) h2
  have hDX2 : D ≤ f112saX2 L1 L2 S := hD.trans inf_le_left
  have hDB : D ≤ borelOf L2 S := hD.trans inf_le_right
  have hDBigB : D ≤ bigB L1 L2 S := hDB.trans (le_sup_right.trans le_sup_left)
  have hoddD : Odd (Nat.card ↥D) := by
    rw [hDcard]
    exact Nat.Even.sub_odd Nat.one_le_two_pow
      (Even.pow_of_ne_zero (a := (2 : ℕ)) even_two (by omega)) odd_one
  have hT2 : IsPGroup 2 ↥T := IsPGroup.to_le hF.1.h1.pgroup (inf_le_left : T ≤ S)
  have hDT : D ≤ Subgroup.normalizer (T : Set H) := by
    rw [show T = S ⊓ f112saK L1 L2 S from rfl, ← f112ll_pCoreOf_K_eq hF hm hn h1 h2]
    exact hDBigB.trans ((f112sa_bigB_le_normalizer_K hF).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (f112saK L1 L2 S)))
  have hcNT : c ∈ Subgroup.normalizer (T : Set H) := by
    rw [show T = S ⊓ f112saK L1 L2 S from rfl, ← f112ll_pCoreOf_K_eq hF hm hn h1 h2]
    exact ((f112sa_bigB_le_normalizer_K hF).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (f112saK L1 L2 S))) (hSB hcS)
  have hcommDT : ∀ d ∈ D, d * c * d⁻¹ * c⁻¹ ∈ T :=
    f112ll_commutator_mem_T_of_torus hF hm hn h1 h2 hd hcS hDX2 hcα
  obtain ⟨t, htT, hqt⟩ := exists_mul_mem_centralizer_of_odd (Q := T) (J := D)
    hT2 hoddD hDT hcNT hcommDT
  let c' := t * c
  have hc'S : c' ∈ S := S.mul_mem ((inf_le_left : T ≤ S) htT) hcS
  have hc'2 : ∃ k, c' ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hF.1.h1.pgroup ⟨c', hc'S⟩
    exact ⟨k, by simpa using congrArg (fun x : ↥S => (x : H)) hk⟩
  have hc'Lβ : c' ∈ Subgroup.normalizer (Lβ : Set H) := mem_normalizer_oTwoPrime (hSNβ hc'S)
  have hc'T : c' ∈ Subgroup.normalizer (T : Set H) := by
    rw [show T = S ⊓ f112saK L1 L2 S from rfl, ← f112ll_pCoreOf_K_eq hF hm hn h1 h2]
    exact ((f112sa_bigB_le_normalizer_K hF).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (f112saK L1 L2 S))) (hSB hc'S)
  have hc'D : ∀ d ∈ D, c' * d = d * c' := by
    intro d hdD
    have h := Subgroup.mem_centralizer_iff.mp hqt d hdD
    exact h.symm
  have hDle : D ≤ Lβ ⊓ Subgroup.normalizer (T : Set H) := fun d hd =>
    ⟨hDX2.trans ((f112sa_X2_le_oTwoRes L1 L2 S).trans
      (f112sa_oTwoRes_le_oTwoPrime_P2'_of_isL2Quot hn h2)) hd, hDT hd⟩
  have hc'Qβ : ∀ l ∈ Lβ, ⁅c', l⁆ ∈ pCoreOf 2 Lβ :=
    commutator_mem_pCoreOf_of_centralizes_torus hn
      (f112ll_isL2Quot_oTwoPrime_P2' hF hm hn h1 h2)
      (f112sa_T_sylow_oTwoPrime_P2'_of_hyp111R hF hR) hDle hDcard hc'2 hc'Lβ hc'T hc'D
  have hc'β : c' ∈ trivOTwoQuot Lβ := mem_trivOTwoQuot.mpr ⟨hc'Lβ, hc'Qβ⟩
  exact ⟨t, htT, hc'β⟩

theorem f112ll_mem_T_of_commutator_mem_center_left {L1 L2 S : Subgroup H} {m n : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (h1 : IsL2Quot m (oTwoQuot ↥L1)) (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (hcomm : ⁅pCoreOf 2 (f112saP1' L1 L2 S), pCoreOf 2 (f112saP1' L1 L2 S)⁆ ≤
      centerOf (pCoreOf 2 (f112saP1' L1 L2 S)))
    (hZ : centerOf (pCoreOf 2 (f112saP1' L1 L2 S)) ≤
      Subgroup.centralizer (oTwoPrime (f112saP1' L1 L2 S) : Set H))
    (hindec : ⁅pCoreOf 2 (f112saP1' L1 L2 S), oTwoPrime (f112saP1' L1 L2 S)⁆ =
      pCoreOf 2 (f112saP1' L1 L2 S))
    (hJ : ∃ J : Subgroup H, J ≤ bigB (oTwoPrime (f112saP1' L1 L2 S))
        (oTwoPrime (f112saP2' L1 L2 S)) (S ⊓ f112saK L1 L2 S) ∧ Odd (Nat.card J) ∧
      (∀ j ∈ J, ∀ l ∈ oTwoPrime (f112saP1' L1 L2 S), ⁅j, l⁆ ∈ pCoreOf 2 (f112saP1' L1 L2 S)) ∧
      pCoreOf 2 (f112saP1' L1 L2 S) ⊓ Subgroup.centralizer (J : Set H) = ⊥)
    (hW : f112saW L1 L2 S = ⊥) {c : H} (hcS : c ∈ S)
    (hcα : c ∈ trivOTwoQuot (oTwoPrime (f112saP1' L1 L2 S)))
    (hcβ : c ∈ trivOTwoQuot (oTwoPrime (f112saP2' L1 L2 S)))
    (hcQ : ∀ x ∈ pCoreOf 2 (f112saP1' L1 L2 S),
      ⁅c, x⁆ ∈ centerOf (pCoreOf 2 (f112saP1' L1 L2 S))) :
    c ∈ S ⊓ f112saK L1 L2 S := by
  classical
  let Eα := f112saP1' L1 L2 S
  let Lα := oTwoPrime Eα
  let Qα := pCoreOf 2 Eα
  let T := S ⊓ f112saK L1 L2 S
  have hR : Hyp111R L1 L2 S := hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2
  obtain ⟨J, hJB, hJodd, hJtriv, hJcent⟩ := hJ
  obtain ⟨y, hyQ, hc3S, hc3triv, hc3CentJ, hc3Z⟩ :=
    exists_mul_centralizes_torus hF hm hn h1 h2 hcomm hJB hJtriv hJodd hcS hcα hcβ hcQ
  let c₃ : H := y * c
  have hstepg : ∀ l ∈ Lα, ⁅c₃, l⁆ ∈ centerOf Qα :=
    commutator_torus_mem_center hcomm hJtriv hJodd hJcent hc3CentJ hc3triv hc3Z
  have hQleL : Qα ≤ Lα := by
    change pCoreOf 2 Eα ≤ oTwoPrime Eα
    rw [← pCoreOf_oTwoPrime Eα]
    exact CFSG.LieType.BorelTits.pCoreOf_le 2 Lα
  have hO : pCoreOf 2 Lα ≤ ⁅Lα, Lα⁆ := by
    change pCoreOf 2 (oTwoPrime Eα) ≤ ⁅Lα, Lα⁆
    rw [pCoreOf_oTwoPrime, ← hindec]
    exact Subgroup.commutator_mono hQleL le_rfl
  have hperf : ⁅Lα, Lα⁆ = Lα :=
    CFSG.Quasithin.F112R.perfect_of_isL2Quot (f := m) (by omega)
      (f112ll_isL2Quot_oTwoPrime_P1' hF hm hn h1 h2) hO
  have hc3commL : ∀ l ∈ Lα, ⁅c₃, l⁆ ∈ centerOf Lα := by
    intro l hl
    have h := hstepg l hl
    exact ⟨hQleL h.1, hZ h⟩
  have hc3centL : c₃ ∈ Subgroup.centralizer (Lα : Set H) :=
    mem_centralizer_of_commutator_le_center_of_perfect hperf hc3commL
  have hT_le_Lα : T ≤ Lα := f112sa_T_le_oTwoPrime_P1'_of_hyp111R hF hR
  have hc3centT : c₃ ∈ Subgroup.centralizer (T : Set H) :=
    Subgroup.centralizer_le hT_le_Lα hc3centL
  have hc3T : c₃ ∈ T :=
    f112sa_S_inf_centralizer_le_T_of_W_eq_bot_of_hyp111R hF hR hW ⟨hc3S, hc3centT⟩
  have hQα_le_T : Qα ≤ T := by
    change pCoreOf 2 Eα ≤ S ⊓ f112saK L1 L2 S
    rw [← f112ll_pCoreOf_sup_eq hF hm hn h1 h2]
    exact le_sup_left
  have hc_eq : c = y⁻¹ * c₃ := by
    change c = y⁻¹ * (y * c)
    group
  rw [hc_eq]
  exact T.mul_mem (T.inv_mem (hQα_le_T hyQ)) hc3T

theorem TransferLeftData.mem_T_of_mem_trivOTwoQuot {L1 L2 S : Subgroup H} {m n : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) (hd : TransferLeftData L1 L2 S) {c : H} (hcS : c ∈ S)
    (hc1 : c ∈ trivOTwoQuot (oTwoPrime (f112saP1' L1 L2 S)))
    (hc2 : c ∈ trivOTwoQuot (oTwoPrime (f112saP2' L1 L2 S))) :
    c ∈ S ⊓ f112saK L1 L2 S := by
  classical
  let Eα := f112saP1' L1 L2 S
  let Eβ := f112saP2' L1 L2 S
  let Qα := pCoreOf 2 Eα
  let Qβ := pCoreOf 2 Eβ
  obtain ⟨F, hFld, hFchar, α, hα, hker, hnat⟩ := hd.nat_right
  letI := hFld
  letI := hFchar
  have hW : f112saW L1 L2 S = ⊥ :=
    f112ll_W_eq_bot_of_isNatSecOf hF hm hn h1 h2 hker hnat
  have hcZ : ∀ z ∈ centerOf Qβ, c * z = z * c :=
    centralizes_centerRight hF hd hcS hc2
  have hstepd : ∀ x ∈ Qα, ⁅c, x⁆ ∈ centerOf Qα :=
    commutator_pCoreOf_mem_center hd hc1 hcZ
  exact f112ll_mem_T_of_commutator_mem_center_left hF hm hn h1 h2 hd.commutator_le
    hd.centerLeft_le hd.indec_left hd.torus_left hW hcS hc1 hc2 hstepd

private theorem f112ll_mem_T_of_exists_correction {L1 L2 S : Subgroup H} {m n : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) (hd : TransferLeftData L1 L2 S) {c t : H} (hcS : c ∈ S)
    (hcα : c ∈ trivOTwoQuot (oTwoPrime (f112saP1' L1 L2 S)))
    (htT : t ∈ S ⊓ f112saK L1 L2 S)
    (hcβ : t * c ∈ trivOTwoQuot (oTwoPrime (f112saP2' L1 L2 S))) :
    c ∈ S ⊓ f112saK L1 L2 S := by
  classical
  let Lα := oTwoPrime (f112saP1' L1 L2 S)
  let Lβ := oTwoPrime (f112saP2' L1 L2 S)
  let Qα := pCoreOf 2 (f112saP1' L1 L2 S)
  let Qβ := pCoreOf 2 (f112saP2' L1 L2 S)
  let T := S ⊓ f112saK L1 L2 S
  have hR : Hyp111R L1 L2 S := hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2
  have hQα : pCoreOf 2 Lα = Qα := pCoreOf_oTwoPrime (f112saP1' L1 L2 S)
  have hQβ : pCoreOf 2 Lβ = Qβ := pCoreOf_oTwoPrime (f112saP2' L1 L2 S)
  let c' := t * c
  have hc'β : c' ∈ trivOTwoQuot Lβ := hcβ
  have hTQ : T = pCoreOf 2 (f112saP2' L1 L2 S) ⊔ pCoreOf 2 (f112saP1' L1 L2 S) := by
    rw [show T = S ⊓ f112saK L1 L2 S from rfl, ← f112ll_pCoreOf_sup_eq hF hm hn h1 h2,
      sup_comm]
  have hQαT : Qα ≤ T := by
    rw [hTQ]
    exact le_sup_right
  have hQαβ : Qα ≤ Subgroup.normalizer (Qβ : Set H) :=
    (hQαT.trans (f112sa_T_le_oTwoPrime_P2'_of_hyp111R hF hR)).trans
      (by simpa [hQβ] using CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Lβ)
  have htQ : t ∈ Qβ ⊔ Qα := by
    rw [← hTQ]
    exact htT
  have hcoemul : (↑(Qβ ⊔ Qα) : Set H) = Set.mul.mul (Qβ : Set H) (Qα : Set H) :=
    Subgroup.coe_mul_of_right_le_normalizer_left Qβ Qα hQαβ
  have htm : t ∈ Set.mul.mul (Qβ : Set H) (Qα : Set H) := by
    rw [← hcoemul]
    exact htQ
  obtain ⟨tb, htb, ta, hta, htba⟩ := Set.mem_mul.mp htm
  let c₂ := ta * c
  have htaT : ta ∈ T := hQαT hta
  have hc₂S : c₂ ∈ S := S.mul_mem ((inf_le_left : T ≤ S) htaT) hcS
  have hc₂α : c₂ ∈ trivOTwoQuot Lα :=
    (trivOTwoQuot Lα).mul_mem
      (pCoreOf_le_trivOTwoQuot Lα (by rw [hQα]; exact hta)) hcα
  have hc₂β : c₂ ∈ trivOTwoQuot Lβ := by
    have htaeq : c₂ = tb⁻¹ * c' := by
      show ta * c = tb⁻¹ * (t * c)
      rw [← htba]
      group
    rw [htaeq]
    exact (trivOTwoQuot Lβ).mul_mem
      ((trivOTwoQuot Lβ).inv_mem (pCoreOf_le_trivOTwoQuot Lβ (by rw [hQβ]; exact htb)))
      hcβ
  have hc₂T : c₂ ∈ T := hd.mem_T_of_mem_trivOTwoQuot hF hm hn h1 h2 hc₂S hc₂α hc₂β
  have hcEq : c = ta⁻¹ * c₂ := by
    show c = ta⁻¹ * (ta * c)
    group
  rw [hcEq]
  exact T.mul_mem (T.inv_mem htaT) hc₂T

private theorem f112ll_mem_T_of_left {L1 L2 S : Subgroup H} {m n : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) (hd : TransferLeftData L1 L2 S) {c : H} (hcS : c ∈ S)
    (hcα : c ∈ trivOTwoQuot (oTwoPrime (f112saP1' L1 L2 S))) :
    c ∈ S ⊓ f112saK L1 L2 S := by
  obtain ⟨t, htT, htc⟩ :=
    f112ll_exists_correction_of_left hF hm hn h1 h2 hd hcS hcα
  exact f112ll_mem_T_of_exists_correction hF hm hn h1 h2 hd hcS hcα htT htc

theorem TransferLeftData.mem_K_of_left {L1 L2 S : Subgroup H} {m n : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) (hd : TransferLeftData L1 L2 S) {c : H} (hcS : c ∈ S)
    (hc : ∀ l ∈ oTwoPrime (f112saP1' L1 L2 S), ⁅c, l⁆ ∈ pCoreOf 2 (f112saP1' L1 L2 S)) :
    c ∈ f112saK L1 L2 S := by
  have hSNα : S ≤ Subgroup.normalizer (f112saP1' L1 L2 S : Set H) :=
    ((le_sup_right : S ≤ bigB L1 L2 S).trans
      (le_sup_right : bigB L1 L2 S ≤ f112P1 L1 L2 S)).trans
        (f112sa_P1_le_normalizer_P1' hF)
  have htriv : c ∈ trivOTwoQuot (oTwoPrime (f112saP1' L1 L2 S)) := by
    refine mem_trivOTwoQuot.mpr ⟨mem_normalizer_oTwoPrime (hSNα hcS), ?_⟩
    intro l hl
    rw [pCoreOf_oTwoPrime]
    exact hc l hl
  exact (Subgroup.mem_inf.mp (f112ll_mem_T_of_left hF hm hn h1 h2 hd hcS htriv)).2

end CFSG.Quasithin.F112R.St84

end
