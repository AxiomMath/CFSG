module

public import Certificates.Data.TabCo1FiveC
public meta import Certificates.Data.TabCo1FiveC
public import Certificates.Kernel.Co1B.Chk17326
public import Certificates.Kernel.Co1B.Tree17326
public import Certificates.Kernel.Co1B.Lvl17326A
public import Certificates.Kernel.Co1B.Lvl17326B
public import Certificates.Kernel.Co1B.C17330
import Mathlib.Tactic.IntervalCases
public import CFSG.Monster.B.TwoA.Par3.Main

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.Bound17326

open CFSG.KC.Co1BBoundP (lvlChunkP)
open CFSG.KC.Co1BBoundN CFSG.KC.Co1BBound CFSG.KC.Co1BSpin CFSG.KC.Co1B CFSG.KC.Co1F2 CFSG.KC.M1F2
  CFSG.KLie.CT CFSG.KC.Enum CFSG.HardMathSupport.Dickson.I271.TabCo1FiveC
  CFSG.HardMathSupport.Dickson.I271.TabCo1 CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1.TwoBNative
open CertificateChecks.KernelCo1B.Bound17591 (XB)
open CertificateChecks.KernelCo1B.Bound17330 (boundOK_of_sel wf_unpackR not_of_notB mul_unpackW')
open CFSG.KS.SporSch.M24 (unpackR_eq_unpack dagWK_sound gtBFS_of_K bfsMemK_sound contains_bfsTree
  bfsTree gensArr gtPinK bfsMemK)

theorem DC_base : [aR, bR] = (List.range 2).map fun i => CFSG.KS.Raw.unpack 24 24 (DC.M i) := by
  have h := kDCB
  simp only [Bool.and_eq_true] at h
  have e0 : DC.M 0 = CertificateChecks.KernelCo1ThreeK.SM 0 := Nat.eq_of_beq_eq_true h.1
  have e1 : DC.M 1 = CertificateChecks.KernelCo1ThreeK.SM 1 := Nat.eq_of_beq_eq_true h.2
  rw [CertificateChecks.KernelCo1ThreeK.base_eq]
  refine List.map_congr_left fun i hi => ?_
  have hi2 : i < 2 := List.mem_range.1 hi
  interval_cases i
  · rw [e0]
  · rw [e1]

theorem kDagC_eq : kDag ext = ((List.range 92).map fun i => CFSG.KS.Raw.unpack 24 24 (DC.M i),
    (List.range 92).map fun i => CFSG.KS.Raw.unpack 24 24 (DC.MI i), true) := by
  rw [kDag, ← kDCW]
  exact dagWK_sound DC_base kDC

theorem hflag : (kDag ext).2.2 = true := by
  rw [kDagC_eq]

theorem nd_eq {i : Nat} (h1 : 0 < i) (h2 : i ≤ 92) : nd (kDag ext) i = unpackR 24 (DC.M (i - 1)) := by
  rw [nd, kDagC_eq,
    List.getD_eq_getElem _ _ (by simp only [List.length_map, List.length_range]; omega),
    List.getElem_map, List.getElem_range, unpackR_eq_unpack]

theorem ndI_eq {i : Nat} (h1 : 0 < i) (h2 : i ≤ 92) :
    ndI (kDag ext) i = unpackR 24 (DC.MI (i - 1)) := by
  rw [ndI, kDagC_eq,
    List.getD_eq_getElem _ _ (by simp only [List.length_map, List.length_range]; omega),
    List.getElem_map, List.getElem_range, unpackR_eq_unpack]

theorem z_eq : nd (kDag ext) 88 = unpackR 24 ZK := nd_eq (by decide) (by decide)
theorem t1_eq : nd (kDag ext) 89 = unpackR 24 T1K := nd_eq (by decide) (by decide)
theorem t2_eq : nd (kDag ext) 90 = unpackR 24 T2K := nd_eq (by decide) (by decide)
theorem s1_eq : nd (kDag ext) 91 = unpackR 24 S1K := nd_eq (by decide) (by decide)
theorem s2_eq : nd (kDag ext) 92 = unpackR 24 S2K := nd_eq (by decide) (by decide)
theorem t1I_eq : ndI (kDag ext) 89 = unpackR 24 (DC.MI 88) := ndI_eq (by decide) (by decide)
theorem t2I_eq : ndI (kDag ext) 90 = unpackR 24 (DC.MI 89) := ndI_eq (by decide) (by decide)
theorem s1I_eq : ndI (kDag ext) 91 = unpackR 24 (DC.MI 90) := ndI_eq (by decide) (by decide)
theorem s2I_eq : ndI (kDag ext) 92 = unpackR 24 (DC.MI 91) := ndI_eq (by decide) (by decide)

theorem repZ_eq : repZ = unpackR 24 KC.Z0 := by decide +kernel

theorem kSmall' : eqK (powWK ZK 5) oneK = true ∧ notB (eqK ZK oneK) = true ∧
    eqK ZK KC.Z0 = true ∧ eqK (mulWK ZK T1K) (mulWK T1K ZK) = true ∧
    eqK (mulWK ZK T2K) (mulWK T2K ZK) = true ∧ eqK (mulWK ZK S1K) (mulWK S1K ZK) = true ∧
    eqK (mulWK ZK S2K) (mulWK S2K ZK) = true ∧
    eqK ZK (mulWK (mulWK T1K T2K) (mulWK (DC.MI 88) (DC.MI 89))) = true := by
  have h := kSmall
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1.1.1, h.1.1.1.1.1.1.2, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2,
    h.1.2, h.2⟩

theorem c_wfz : wf (nd (kDag ext) 88) = true := by
  rw [z_eq]
  exact wf_unpackR _

theorem c_wf1 : wf (one ()) = true := by
  rw [CFSG.KC.Co1B.one_eq]
  exact wf_unpackR _

theorem c_rep : (nd (kDag ext) 88 == repZ) = true := by
  rw [z_eq, repZ_eq, beq_unpack]
  exact kSmall'.2.2.1

theorem c_pow : (pow (nd (kDag ext) 88) 5 == one ()) = true := by
  rw [z_eq, pow_unpack', CFSG.KC.Co1B.one_eq, beq_unpack]
  exact kSmall'.1

theorem c_ne : (nd (kDag ext) 88 != one ()) = true := by
  rw [z_eq, CFSG.KC.Co1B.one_eq, bne, beq_unpack]
  exact not_of_notB kSmall'.2.1

theorem c_zt1 : (mul (nd (kDag ext) 88) (nd (kDag ext) 89) ==
    mul (nd (kDag ext) 89) (nd (kDag ext) 88)) = true := by
  rw [z_eq, t1_eq, mul_unpackW', mul_unpackW', beq_unpack]
  exact kSmall'.2.2.2.1

theorem c_zt2 : (mul (nd (kDag ext) 88) (nd (kDag ext) 90) ==
    mul (nd (kDag ext) 90) (nd (kDag ext) 88)) = true := by
  rw [z_eq, t2_eq, mul_unpackW', mul_unpackW', beq_unpack]
  exact kSmall'.2.2.2.2.1

theorem c_zs1 : (mul (nd (kDag ext) 88) (nd (kDag ext) 91) ==
    mul (nd (kDag ext) 91) (nd (kDag ext) 88)) = true := by
  rw [z_eq, s1_eq, mul_unpackW', mul_unpackW', beq_unpack]
  exact kSmall'.2.2.2.2.2.1

theorem c_zs2 : (mul (nd (kDag ext) 88) (nd (kDag ext) 92) ==
    mul (nd (kDag ext) 92) (nd (kDag ext) 88)) = true := by
  rw [z_eq, s2_eq, mul_unpackW', mul_unpackW', beq_unpack]
  exact kSmall'.2.2.2.2.2.2.1

theorem c_comm : (nd (kDag ext) 88 == mul (mul (nd (kDag ext) 89) (nd (kDag ext) 90))
    (mul (ndI (kDag ext) 89) (ndI (kDag ext) 90))) = true := by
  rw [z_eq, t1_eq, t2_eq, t1I_eq, t2I_eq, mul_unpackW', mul_unpackW', mul_unpackW', beq_unpack]
  exact kSmall'.2.2.2.2.2.2.2

theorem kTT' : gtPinK TM 2 200 TT.N TT.P TT.PAR TT.LAB TT.W TT.S = true ∧ TT.N = 125 := by
  have h := kTT
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  exact h

theorem kCT' : gtPinK CM 2 20000 CT.N CT.P CT.PAR CT.LAB CT.W CT.S = true ∧ CT.N = 15000 := by
  have h := kCT
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  exact h

theorem TG_eq : [nd (kDag ext) 89, nd (kDag ext) 90].toArray = gensArr 2 TM := by
  rw [t1_eq, t2_eq]
  apply Array.ext (by simp [gensArr])
  intro i h1 h2
  have hi : i < 2 := by simpa using h1
  interval_cases i <;> simp [gensArr, TM, T1K, T2K, unpackR_eq_unpack]

theorem CG_eq : [nd (kDag ext) 91, nd (kDag ext) 92].toArray = gensArr 2 CM := by
  rw [s1_eq, s2_eq]
  apply Array.ext (by simp [gensArr])
  intro i h1 h2
  have hi : i < 2 := by simpa using h1
  interval_cases i <;> simp [gensArr, CM, S1K, S2K, unpackR_eq_unpack]

theorem gtT_eq : gtBFS [nd (kDag ext) 89, nd (kDag ext) 90].toArray 200 =
    bfsTree TT.N TT.P TT.PAR TT.LAB := by
  rw [TG_eq]
  exact (gtBFS_of_K kTT'.1).1

theorem gtC_eq : gtBFS [nd (kDag ext) 91, nd (kDag ext) 92].toArray 20000 =
    bfsTree CT.N CT.P CT.PAR CT.LAB := by
  rw [CG_eq]
  exact (gtBFS_of_K kCT'.1).1

theorem c_gtT : gtOK [nd (kDag ext) 89, nd (kDag ext) 90].toArray
    (gtBFS [nd (kDag ext) 89, nd (kDag ext) 90].toArray 200) = true := by
  rw [gtT_eq, TG_eq]
  exact (gtBFS_of_K kTT'.1).2

theorem c_gtC : gtOK [nd (kDag ext) 91, nd (kDag ext) 92].toArray
    (gtBFS [nd (kDag ext) 91, nd (kDag ext) 92].toArray 20000) = true := by
  rw [gtC_eq, CG_eq]
  exact (gtBFS_of_K kCT'.1).2

theorem c_sizeT : decide ((gtBFS [nd (kDag ext) 89, nd (kDag ext) 90].toArray 200).pts.size = 125) =
    true := by
  rw [gtT_eq, decide_eq_true_iff]
  simp [bfsTree, kTT'.2]

theorem c_sizeC : decide ((gtBFS [nd (kDag ext) 91, nd (kDag ext) 92].toArray 20000).pts.size =
    15000) = true := by
  rw [gtC_eq, decide_eq_true_iff]
  simp [bfsTree, kCT'.2]

theorem memT {K : Nat} (h : bfsMemK TT.P TT.S TT.N K = true) :
    (bfsTree TT.N TT.P TT.PAR TT.LAB).pts.contains (unpackR 24 K) = true := by
  obtain ⟨hw, hK⟩ := bfsMemK_sound h
  exact contains_bfsTree hw (by rw [hK, unpackR_eq_unpack])

theorem kNorm' : bfsMemK TT.P TT.S TT.N (mulWK (mulWK S1K T1K) (DC.MI 90)) = true ∧
    bfsMemK TT.P TT.S TT.N (mulWK (mulWK S1K T2K) (DC.MI 90)) = true ∧
    bfsMemK TT.P TT.S TT.N (mulWK (mulWK S2K T1K) (DC.MI 91)) = true ∧
    bfsMemK TT.P TT.S TT.N (mulWK (mulWK S2K T2K) (DC.MI 91)) = true ∧
    bfsMemK TT.P TT.S TT.N (mulWK (mulWK (DC.MI 90) T1K) S1K) = true ∧
    bfsMemK TT.P TT.S TT.N (mulWK (mulWK (DC.MI 90) T2K) S1K) = true ∧
    bfsMemK TT.P TT.S TT.N (mulWK (mulWK (DC.MI 91) T1K) S2K) = true ∧
    bfsMemK TT.P TT.S TT.N (mulWK (mulWK (DC.MI 91) T2K) S2K) = true := by
  have h := kNorm
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1.1.1, h.1.1.1.1.1.1.2, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2,
    h.1.2, h.2⟩

theorem c_n1 : (gtBFS [nd (kDag ext) 89, nd (kDag ext) 90].toArray 200).pts.contains
    (mul (mul (nd (kDag ext) 91) (nd (kDag ext) 89)) (ndI (kDag ext) 91)) = true := by
  rw [gtT_eq, s1_eq, s1I_eq, t1_eq, mul_unpackW', mul_unpackW']
  exact memT kNorm'.1

theorem c_n2 : (gtBFS [nd (kDag ext) 89, nd (kDag ext) 90].toArray 200).pts.contains
    (mul (mul (nd (kDag ext) 91) (nd (kDag ext) 90)) (ndI (kDag ext) 91)) = true := by
  rw [gtT_eq, s1_eq, s1I_eq, t2_eq, mul_unpackW', mul_unpackW']
  exact memT kNorm'.2.1

theorem c_n3 : (gtBFS [nd (kDag ext) 89, nd (kDag ext) 90].toArray 200).pts.contains
    (mul (mul (nd (kDag ext) 92) (nd (kDag ext) 89)) (ndI (kDag ext) 92)) = true := by
  rw [gtT_eq, s2_eq, s2I_eq, t1_eq, mul_unpackW', mul_unpackW']
  exact memT kNorm'.2.2.1

theorem c_n4 : (gtBFS [nd (kDag ext) 89, nd (kDag ext) 90].toArray 200).pts.contains
    (mul (mul (nd (kDag ext) 92) (nd (kDag ext) 90)) (ndI (kDag ext) 92)) = true := by
  rw [gtT_eq, s2_eq, s2I_eq, t2_eq, mul_unpackW', mul_unpackW']
  exact memT kNorm'.2.2.2.1

theorem c_n5 : (gtBFS [nd (kDag ext) 89, nd (kDag ext) 90].toArray 200).pts.contains
    (mul (mul (ndI (kDag ext) 91) (nd (kDag ext) 89)) (nd (kDag ext) 91)) = true := by
  rw [gtT_eq, s1_eq, s1I_eq, t1_eq, mul_unpackW', mul_unpackW']
  exact memT kNorm'.2.2.2.2.1

theorem c_n6 : (gtBFS [nd (kDag ext) 89, nd (kDag ext) 90].toArray 200).pts.contains
    (mul (mul (ndI (kDag ext) 91) (nd (kDag ext) 90)) (nd (kDag ext) 91)) = true := by
  rw [gtT_eq, s1_eq, s1I_eq, t2_eq, mul_unpackW', mul_unpackW']
  exact memT kNorm'.2.2.2.2.2.1

theorem c_n7 : (gtBFS [nd (kDag ext) 89, nd (kDag ext) 90].toArray 200).pts.contains
    (mul (mul (ndI (kDag ext) 92) (nd (kDag ext) 89)) (nd (kDag ext) 92)) = true := by
  rw [gtT_eq, s2_eq, s2I_eq, t1_eq, mul_unpackW', mul_unpackW']
  exact memT kNorm'.2.2.2.2.2.2.1

theorem c_n8 : (gtBFS [nd (kDag ext) 89, nd (kDag ext) 90].toArray 200).pts.contains
    (mul (mul (ndI (kDag ext) 92) (nd (kDag ext) 90)) (nd (kDag ext) 92)) = true := by
  rw [gtT_eq, s2_eq, s2I_eq, t2_eq, mul_unpackW', mul_unpackW']
  exact memT kNorm'.2.2.2.2.2.2.2

theorem kT' : KC.T.length = 5 ∧ ∀ i < 5, eqK (getL 0 KC.T i) (trK 24 (powWK ZK i)) = true := by
  have h := kT
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  exact ⟨h.1, allN_true' h.2⟩

theorem cs1 : colsOf (powList (nd (kDag ext) 88) 5) = (KC.T.map (unpackR 24)).toArray := by
  obtain ⟨hl, hall⟩ := kT'
  rw [z_eq, colsOf, powList, List.map_toArray, List.map_map]
  refine congrArg List.toArray ?_
  apply List.ext_getElem (by simp [hl])
  intro i h1 h2
  have hi : i < 5 := by simpa using h1
  have e := beq_of_eqK (hall i hi)
  rw [CFSG.KC.Co1B.getL_eq, List.getElem?_eq_getElem (by rw [hl]; exact hi), Option.getD_some] at e
  rw [List.getElem_map, List.getElem_map, List.getElem_range, Function.comp_apply, pow_unpack',
    CFSG.KC.F2W.transposeRows_unpackR, e]

theorem kNF {i : Nat} (hi : i < 7) : memK XB (base.getD i 0) = true ∧
    (KC.CNs.getD i []).length = 9 ∧ (KC.CNs.getD i []).sum ≤ cnts.getD i 0 := by
  have h := kNs
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  have h' := allN_true' h.2 i hi
  simp only [Bool.and_eq_true, Nat.beq_eq] at h'
  exact ⟨h'.1.1, h'.1.2, Nat.le_of_ble_eq_true h'.2⟩

theorem chunks1 : ∀ n < 63,
    lvlChunkP 5 XB KC.T KC.CFs KC.NP CertificateChecks.KernelCo1B.CV.F KC.CNs n = true := by
  intro n hn
  rcases Nat.lt_or_ge n 32 with h | h
  · interval_cases n
    exacts [ch17326pA0, ch17326pA1, ch17326pA2, ch17326pA3, ch17326pA4, ch17326pA5, ch17326pA6,
      ch17326pA7, ch17326pA8, ch17326pA9, ch17326pA10, ch17326pA11, ch17326pA12, ch17326pA13,
      ch17326pA14, ch17326pA15, ch17326pA16, ch17326pA17, ch17326pA18, ch17326pA19, ch17326pA20,
      ch17326pA21, ch17326pA22, ch17326pA23, ch17326pA24, ch17326pA25, ch17326pA26,
      ch17326pA27, ch17326pA28, ch17326pA29, ch17326pA30, ch17326pA31]
  · interval_cases n
    exacts [ch17326pA32, ch17326pA33, ch17326pA34, ch17326pA35, ch17326pA36, ch17326pA37,
      ch17326pA38, ch17326pA39, ch17326pA40, ch17326pA41, ch17326pA42, ch17326pA43,
      ch17326pA44, ch17326pA45, ch17326pA46, ch17326pA47, ch17326pA48, ch17326pA49,
      ch17326pA50, ch17326pA51, ch17326pA52, ch17326pA53, ch17326pA54, ch17326pA55,
      ch17326pA56, ch17326pA57, ch17326pA58, ch17326pA59, ch17326pA60, ch17326pA61, ch17326pA62]

theorem c_bound1 : boundOK (colsOf (powList (nd (kDag ext) 88) 5)) 5 base conds cnts span comb =
    true := by
  rw [cs1]
  exact boundOK_of_sel (m := 7) kT'.1 rfl rfl rfl (of_decide_eq_true kCFs)
    (fun i hi => kNF hi) chunks1 kSpan

theorem kT2' : KC.T2.length = 7 ∧ ∀ i < 7, eqK (getL 0 KC.T2 i) (trK 24 (getL 0 PT2 i)) = true := by
  have h := kT2
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  exact ⟨h.1, allN_true' h.2⟩

theorem cs2 : colsOf (ptRows (nd (kDag ext) 88) (nd (kDag ext) 89) (nd (kDag ext) 90)) =
    (KC.T2.map (unpackR 24)).toArray := by
  have hpt : ptRows (unpackR 24 ZK) (unpackR 24 T1K) (unpackR 24 T2K) = PT2.map (unpackR 24) := by
    simp only [ptRows, PT2, List.map_cons, List.map_nil, pow_unpack', mul_unpackW']
  have hPT : PT2.length = 7 := rfl
  obtain ⟨hl, hall⟩ := kT2'
  rw [z_eq, t1_eq, t2_eq, hpt, colsOf, List.map_toArray, List.map_map]
  refine congrArg List.toArray ?_
  apply List.ext_getElem (by simp [hl, hPT])
  intro i h1 h2
  have hi : i < 7 := by simpa [hPT] using h1
  have e := beq_of_eqK (hall i hi)
  rw [CFSG.KC.Co1B.getL_eq, CFSG.KC.Co1B.getL_eq, List.getElem?_eq_getElem (by rw [hl]; exact hi),
    List.getElem?_eq_getElem (by rw [hPT]; exact hi), Option.getD_some, Option.getD_some] at e
  rw [List.getElem_map, List.getElem_map, Function.comp_apply, CFSG.KC.F2W.transposeRows_unpackR, e]

theorem kN2F {i : Nat} (hi : i < 4) : memK XB (base2.getD i 0) = true ∧
    (KC.CNs2.getD i []).length = 9 ∧ (KC.CNs2.getD i []).sum ≤ cnts2.getD i 0 := by
  have h := kNs2
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  have h' := allN_true' h.2 i hi
  simp only [Bool.and_eq_true, Nat.beq_eq] at h'
  exact ⟨h'.1.1, h'.1.2, Nat.le_of_ble_eq_true h'.2⟩

theorem chunks2 : ∀ n < 36,
    lvlChunkP 7 XB KC.T2 KC.CFs2 KC.NP2 CertificateChecks.KernelCo1B.CV.F KC.CNs2 n = true := by
  intro n hn
  interval_cases n
  exacts [ch17326pB0, ch17326pB1, ch17326pB2, ch17326pB3, ch17326pB4, ch17326pB5, ch17326pB6,
    ch17326pB7, ch17326pB8, ch17326pB9, ch17326pB10, ch17326pB11, ch17326pB12, ch17326pB13,
    ch17326pB14, ch17326pB15, ch17326pB16, ch17326pB17, ch17326pB18, ch17326pB19, ch17326pB20,
    ch17326pB21, ch17326pB22, ch17326pB23, ch17326pB24, ch17326pB25, ch17326pB26,
    ch17326pB27, ch17326pB28, ch17326pB29, ch17326pB30, ch17326pB31, ch17326pB32,
    ch17326pB33, ch17326pB34, ch17326pB35]

theorem c_bound2 : boundOK (colsOf (ptRows (nd (kDag ext) 88) (nd (kDag ext) 89)
    (nd (kDag ext) 90))) 7 base2 conds2 cnts2 span2 comb2 = true := by
  rw [cs2]
  exact boundOK_of_sel (m := 4) kT2'.1 rfl rfl rfl (of_decide_eq_true kCFs2)
    (fun i hi => kN2F hi) chunks2 kSpan2

theorem c_prod1 : decide (cnts.prod ≤ 15000) = true := by decide
theorem c_prod2 : decide (cnts2.prod ≤ 5) = true := by decide

open Certificates in
open CFSG.HardMathSupport.Dickson.I271.TabCo1FiveC in
theorem c17326 : fiveCCheck () = true := by
  unfold fiveCCheck
  simp only [hflag, c_wfz, c_wf1, c_rep, c_pow, c_ne, c_zt1, c_zt2, c_zs1, c_zs2, c_comm, c_gtT,
    c_sizeT, c_n1, c_n2, c_n3, c_n4, c_n5, c_n6, c_n7, c_n8, c_gtC, c_sizeC, c_bound1, c_bound2,
    c_prod1, c_prod2, Bool.and_self]

end CertificateChecks.KernelCo1B.Bound17326

end
