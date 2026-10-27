module

public import Certificates.Data.TabCo1FiveA
public meta import Certificates.Data.TabCo1FiveA
public import Certificates.Kernel.Co1B.Chk17324
public import Certificates.Kernel.Co1B.Lvl17324
public import Certificates.Kernel.Co1B.C17330
import Mathlib.Tactic.IntervalCases
public import CFSG.Monster.B.TwoA.Par3.Main

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.Bound17324

open CFSG.KC.Co1BBoundP (lvlChunkP)
open CFSG.KC.Co1BBoundN CFSG.KC.Co1BBound CFSG.KC.Co1BSpin CFSG.KC.Co1B CFSG.KC.Co1F2 CFSG.KC.M1F2
  CFSG.KLie.CT CFSG.KC.Enum CFSG.HardMathSupport.Dickson.I271.TabCo1FiveA
  CFSG.HardMathSupport.Dickson.I271.TabCo1 CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Block
open CertificateChecks.KernelCo1B.Bound17591 (XB)
open CertificateChecks.KernelCo1B.Bound17330 (boundOK_of_sel wf_unpackR not_of_notB mul_unpackW')
open CFSG.KS.SporSch.M24 (unpackR_eq_unpack dagWK_sound)

theorem DA_base : [aR, bR] = (List.range 2).map fun i => CFSG.KS.Raw.unpack 24 24 (DA.M i) := by
  have h := kDAB
  simp only [Bool.and_eq_true] at h
  have e0 : DA.M 0 = CertificateChecks.KernelCo1ThreeK.SM 0 := Nat.eq_of_beq_eq_true h.1
  have e1 : DA.M 1 = CertificateChecks.KernelCo1ThreeK.SM 1 := Nat.eq_of_beq_eq_true h.2
  rw [CertificateChecks.KernelCo1ThreeK.base_eq]
  refine List.map_congr_left fun i hi => ?_
  have hi2 : i < 2 := List.mem_range.1 hi
  interval_cases i
  · rw [e0]
  · rw [e1]

theorem kDagA_eq : kDag ext = ((List.range 90).map fun i => CFSG.KS.Raw.unpack 24 24 (DA.M i),
    (List.range 90).map fun i => CFSG.KS.Raw.unpack 24 24 (DA.MI i), true) := by
  rw [kDag, ← kDAW]
  exact dagWK_sound DA_base kDA

theorem hflag : (kDag ext).2.2 = true := by
  rw [kDagA_eq]

theorem nd_eq {i : Nat} (h1 : 0 < i) (h2 : i ≤ 90) : nd (kDag ext) i = unpackR 24 (DA.M (i - 1)) := by
  rw [nd, kDagA_eq,
    List.getD_eq_getElem _ _ (by simp only [List.length_map, List.length_range]; omega),
    List.getElem_map, List.getElem_range, unpackR_eq_unpack]

theorem ndI_eq {i : Nat} (h1 : 0 < i) (h2 : i ≤ 90) :
    ndI (kDag ext) i = unpackR 24 (DA.MI (i - 1)) := by
  rw [ndI, kDagA_eq,
    List.getD_eq_getElem _ _ (by simp only [List.length_map, List.length_range]; omega),
    List.getElem_map, List.getElem_range, unpackR_eq_unpack]

theorem k_eq : nd (kDag ext) 88 = unpackR 24 KK := nd_eq (by decide) (by decide)
theorem u_eq : nd (kDag ext) 89 = unpackR 24 UK := nd_eq (by decide) (by decide)
theorem v_eq : nd (kDag ext) 90 = unpackR 24 VK := nd_eq (by decide) (by decide)

theorem word_eq (w : List Int) : word [nd (kDag ext) 89, nd (kDag ext) 90]
    [ndI (kDag ext) 89, ndI (kDag ext) 90] w = unpackR 24 (wordK RS2 IS2 w) := by
  have h1 : [nd (kDag ext) 89, nd (kDag ext) 90] = RS2.map (unpackR 24) := by
    rw [u_eq, v_eq]
    rfl
  have h2 : [ndI (kDag ext) 89, ndI (kDag ext) 90] = IS2.map (unpackR 24) := by
    rw [ndI_eq (i := 89) (by decide) (by decide), ndI_eq (i := 90) (by decide) (by decide)]
    rfl
  rw [h1, h2, word_sound]

theorem repD0_eq : repD0 = unpackR 24 KA.D0 := by decide +kernel

theorem kSmall' : eqK (powWK KK 5) oneK = true ∧ notB (eqK KK oneK) = true ∧
    eqK KK KA.D0 = true ∧ notB (eqK UK oneK) = true ∧ eqK (mulWK KK UK) (mulWK UK KK) = true ∧
    eqK (mulWK KK VK) (mulWK VK KK) = true ∧ eqK (wordK RS2 IS2 rel1) oneK = true ∧
    eqK (wordK RS2 IS2 rel2) oneK = true ∧ eqK (wordK RS2 IS2 rel3) oneK = true := by
  have h := kSmall
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1.1.1.1, h.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.2, h.1.1.1.1.1.2, h.1.1.1.1.2,
    h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem c_wfk : wf (nd (kDag ext) 88) = true := by
  rw [k_eq]
  exact wf_unpackR _

theorem c_wfu : wf (nd (kDag ext) 89) = true := by
  rw [u_eq]
  exact wf_unpackR _

theorem c_wf1 : wf (one ()) = true := by
  rw [CFSG.KC.Co1B.one_eq]
  exact wf_unpackR _

theorem c_rep : (nd (kDag ext) 88 == repD0) = true := by
  rw [k_eq, repD0_eq, beq_unpack]
  exact kSmall'.2.2.1

theorem c_pow : (pow (nd (kDag ext) 88) 5 == one ()) = true := by
  rw [k_eq, pow_unpack', CFSG.KC.Co1B.one_eq, beq_unpack]
  exact kSmall'.1

theorem c_ne : (nd (kDag ext) 88 != one ()) = true := by
  rw [k_eq, CFSG.KC.Co1B.one_eq, bne, beq_unpack]
  exact not_of_notB kSmall'.2.1

theorem c_une : (nd (kDag ext) 89 != one ()) = true := by
  rw [u_eq, CFSG.KC.Co1B.one_eq, bne, beq_unpack]
  exact not_of_notB kSmall'.2.2.2.1

theorem c_ku : (mul (nd (kDag ext) 88) (nd (kDag ext) 89) ==
    mul (nd (kDag ext) 89) (nd (kDag ext) 88)) = true := by
  rw [k_eq, u_eq, mul_unpackW', mul_unpackW', beq_unpack]
  exact kSmall'.2.2.2.2.1

theorem c_kv : (mul (nd (kDag ext) 88) (nd (kDag ext) 90) ==
    mul (nd (kDag ext) 90) (nd (kDag ext) 88)) = true := by
  rw [k_eq, v_eq, mul_unpackW', mul_unpackW', beq_unpack]
  exact kSmall'.2.2.2.2.2.1

theorem c_rel1 : (word [nd (kDag ext) 89, nd (kDag ext) 90] [ndI (kDag ext) 89, ndI (kDag ext) 90]
    rel1 == one ()) = true := by
  rw [word_eq, CFSG.KC.Co1B.one_eq, beq_unpack]
  exact kSmall'.2.2.2.2.2.2.1

theorem c_rel2 : (word [nd (kDag ext) 89, nd (kDag ext) 90] [ndI (kDag ext) 89, ndI (kDag ext) 90]
    rel2 == one ()) = true := by
  rw [word_eq, CFSG.KC.Co1B.one_eq, beq_unpack]
  exact kSmall'.2.2.2.2.2.2.2.1

theorem c_rel3 : (word [nd (kDag ext) 89, nd (kDag ext) 90] [ndI (kDag ext) 89, ndI (kDag ext) 90]
    rel3 == one ()) = true := by
  rw [word_eq, CFSG.KC.Co1B.one_eq, beq_unpack]
  exact kSmall'.2.2.2.2.2.2.2.2

theorem kT' : KA.T.length = 5 ∧ ∀ i < 5, eqK (getL 0 KA.T i) (trK 24 (powWK KK i)) = true := by
  have h := kT
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  exact ⟨h.1, allN_true' h.2⟩

theorem cs1 : colsOf (powList (nd (kDag ext) 88) 5) = (KA.T.map (unpackR 24)).toArray := by
  obtain ⟨hl, hall⟩ := kT'
  rw [k_eq, colsOf, powList, List.map_toArray, List.map_map]
  refine congrArg List.toArray ?_
  apply List.ext_getElem (by simp [hl])
  intro i h1 h2
  have hi : i < 5 := by simpa using h1
  have e := beq_of_eqK (hall i hi)
  rw [CFSG.KC.Co1B.getL_eq, List.getElem?_eq_getElem (by rw [hl]; exact hi), Option.getD_some] at e
  rw [List.getElem_map, List.getElem_map, List.getElem_range, Function.comp_apply, pow_unpack',
    CFSG.KC.F2W.transposeRows_unpackR, e]

theorem kNF {i : Nat} (hi : i < 6) : memK XB (base.getD i 0) = true ∧
    (KA.CNs.getD i []).length = 9 ∧ (KA.CNs.getD i []).sum ≤ cnts.getD i 0 := by
  have h := kNs
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  have h' := allN_true' h.2 i hi
  simp only [Bool.and_eq_true, Nat.beq_eq] at h'
  exact ⟨h'.1.1, h'.1.2, Nat.le_of_ble_eq_true h'.2⟩

theorem chunks : ∀ n < 54,
    lvlChunkP 5 XB KA.T KA.CFs KA.NP CertificateChecks.KernelCo1B.CV.F KA.CNs n = true := by
  intro n hn
  rcases Nat.lt_or_ge n 27 with h | h
  · interval_cases n
    exacts [ch17324p0, ch17324p1, ch17324p2, ch17324p3, ch17324p4, ch17324p5, ch17324p6,
      ch17324p7, ch17324p8, ch17324p9, ch17324p10, ch17324p11, ch17324p12, ch17324p13,
      ch17324p14, ch17324p15, ch17324p16, ch17324p17, ch17324p18, ch17324p19, ch17324p20,
      ch17324p21, ch17324p22, ch17324p23, ch17324p24, ch17324p25, ch17324p26]
  · interval_cases n
    exacts [ch17324p27, ch17324p28, ch17324p29, ch17324p30, ch17324p31, ch17324p32,
      ch17324p33, ch17324p34, ch17324p35, ch17324p36, ch17324p37, ch17324p38, ch17324p39,
      ch17324p40, ch17324p41, ch17324p42, ch17324p43, ch17324p44, ch17324p45, ch17324p46,
      ch17324p47, ch17324p48, ch17324p49, ch17324p50, ch17324p51, ch17324p52, ch17324p53]

theorem c_bound : boundOK (colsOf (powList (nd (kDag ext) 88) 5)) 5 base conds cnts span comb =
    true := by
  rw [cs1]
  exact boundOK_of_sel (m := 6) kT'.1 rfl rfl rfl (of_decide_eq_true kCFs)
    (fun i hi => kNF hi) chunks kSpan

theorem c_prod : decide (cnts.prod ≤ 3024000) = true := by decide

open Certificates in
open CFSG.HardMathSupport.Dickson.I271.TabCo1FiveA in
theorem c17324 : fiveACheck () = true := by
  unfold fiveACheck
  simp only [hflag, c_wfk, c_wfu, c_wf1, c_rep, c_pow, c_ne, c_ku, c_kv, c_une, c_rel1, c_rel2,
    c_rel3, c_bound, c_prod, Bool.and_self]

end CertificateChecks.KernelCo1B.Bound17324

end
