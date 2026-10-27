module

public import Certificates.Data.TabCo1FiveB
public meta import Certificates.Data.TabCo1FiveB
public import Certificates.Kernel.Co1B.Chk17325
public import Certificates.Kernel.Co1B.Tree17325
public import Certificates.Kernel.Co1B.Lvl17325A
public import Certificates.Kernel.Co1B.Lvl17325B
public import Certificates.Kernel.Co1B.C17330
public import CFSG.Certificates.Kernel.SporSch.Co1BfsSegSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Monster.B.TwoA.Par3.Main
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points
public import CFSG.Monster.B.TwoA.Unitary.Semilinear

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.Bound17325

open CFSG.KC.Co1BBoundP (lvlChunkP)
open CFSG.KC.Co1BBoundN CFSG.KC.Co1BBound CFSG.KC.Co1BSpin CFSG.KC.Co1B CFSG.KC.Co1F2 CFSG.KC.M1F2
  CFSG.KLie.CT CFSG.KC.Enum CFSG.HardMathSupport.Dickson.I271.TabCo1FiveB
  CFSG.HardMathSupport.Dickson.I271.TabCo1 CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1.TwoBNative
open CertificateChecks.KernelCo1B.Bound17591 (XB)
open CertificateChecks.KernelCo1B.Bound17330 (boundOK_of_sel wf_unpackR not_of_notB mul_unpackW')
open CFSG.KS.SporSch.M24 (unpackR_eq_unpack dagWK_sound gtBFS_of_K bfsTree gensArr gtPinK
  gtPinK_of_seg invOKW invOKW_sound)

theorem DB_base : [aR, bR] = (List.range 2).map fun i => CFSG.KS.Raw.unpack 24 24 (DB.M i) := by
  have h := kDBB
  simp only [Bool.and_eq_true] at h
  have e0 : DB.M 0 = CertificateChecks.KernelCo1ThreeK.SM 0 := Nat.eq_of_beq_eq_true h.1
  have e1 : DB.M 1 = CertificateChecks.KernelCo1ThreeK.SM 1 := Nat.eq_of_beq_eq_true h.2
  rw [CertificateChecks.KernelCo1ThreeK.base_eq]
  refine List.map_congr_left fun i hi => ?_
  have hi2 : i < 2 := List.mem_range.1 hi
  interval_cases i
  · rw [e0]
  · rw [e1]

theorem kDagB_eq : kDag ext = ((List.range 91).map fun i => CFSG.KS.Raw.unpack 24 24 (DB.M i),
    (List.range 91).map fun i => CFSG.KS.Raw.unpack 24 24 (DB.MI i), true) := by
  rw [kDag, ← kDBW]
  exact dagWK_sound DB_base kDB

theorem hflag : (kDag ext).2.2 = true := by
  rw [kDagB_eq]

theorem nd_eq {i : Nat} (h1 : 0 < i) (h2 : i ≤ 91) : nd (kDag ext) i = unpackR 24 (DB.M (i - 1)) := by
  rw [nd, kDagB_eq,
    List.getD_eq_getElem _ _ (by simp only [List.length_map, List.length_range]; omega),
    List.getElem_map, List.getElem_range, unpackR_eq_unpack]

theorem ndI_eq {i : Nat} (h1 : 0 < i) (h2 : i ≤ 91) :
    ndI (kDag ext) i = unpackR 24 (DB.MI (i - 1)) := by
  rw [ndI, kDagB_eq,
    List.getD_eq_getElem _ _ (by simp only [List.length_map, List.length_range]; omega),
    List.getElem_map, List.getElem_range, unpackR_eq_unpack]

theorem k_eq : nd (kDag ext) 88 = unpackR 24 KK := nd_eq (by decide) (by decide)
theorem x1_eq : nd (kDag ext) 89 = unpackR 24 X1K := nd_eq (by decide) (by decide)
theorem y1_eq : nd (kDag ext) 90 = unpackR 24 Y1K := nd_eq (by decide) (by decide)
theorem t_eq : nd (kDag ext) 91 = unpackR 24 TK := nd_eq (by decide) (by decide)
theorem tI_eq : ndI (kDag ext) 91 = unpackR 24 TI := ndI_eq (by decide) (by decide)

theorem repD1_eq : repD1 = unpackR 24 KB.D1 := by decide +kernel

theorem kSmall' : eqK KK KB.D1 = true ∧ eqK (powWK KK 5) oneK = true ∧
    notB (eqK KK oneK) = true ∧ eqK (mulWK KK X1K) (mulWK X1K KK) = true ∧
    eqK (mulWK KK Y1K) (mulWK Y1K KK) = true ∧ eqK (mulWK KK TK) (mulWK TK KK) = true ∧
    eqK (mulWK TK TK) oneK = true ∧ eqK (mulWK X1K X2K) (mulWK X2K X1K) = true ∧
    eqK (mulWK X1K Y2K) (mulWK Y2K X1K) = true ∧ eqK (mulWK Y1K X2K) (mulWK X2K Y1K) = true ∧
    eqK (mulWK Y1K Y2K) (mulWK Y2K Y1K) = true := by
  have h := kSmall
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1.1.1.1.1.1, h.1.1.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.1.2,
    h.1.1.1.1.1.1.2, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem c_wfk : wf (nd (kDag ext) 88) = true := by
  rw [k_eq]
  exact wf_unpackR _

theorem c_wf1 : wf (one ()) = true := by
  rw [CFSG.KC.Co1B.one_eq]
  exact wf_unpackR _

theorem c_rep : (nd (kDag ext) 88 == repD1) = true := by
  rw [k_eq, repD1_eq, beq_unpack]
  exact kSmall'.1

theorem c_pow : (pow (nd (kDag ext) 88) 5 == one ()) = true := by
  rw [k_eq, pow_unpack', CFSG.KC.Co1B.one_eq, beq_unpack]
  exact kSmall'.2.1

theorem c_ne : (nd (kDag ext) 88 != one ()) = true := by
  rw [k_eq, CFSG.KC.Co1B.one_eq, bne, beq_unpack]
  exact not_of_notB kSmall'.2.2.1

theorem c_kx : (mul (nd (kDag ext) 88) (nd (kDag ext) 89) ==
    mul (nd (kDag ext) 89) (nd (kDag ext) 88)) = true := by
  rw [k_eq, x1_eq, mul_unpackW', mul_unpackW', beq_unpack]
  exact kSmall'.2.2.2.1

theorem c_ky : (mul (nd (kDag ext) 88) (nd (kDag ext) 90) ==
    mul (nd (kDag ext) 90) (nd (kDag ext) 88)) = true := by
  rw [k_eq, y1_eq, mul_unpackW', mul_unpackW', beq_unpack]
  exact kSmall'.2.2.2.2.1

theorem c_kt : (mul (nd (kDag ext) 88) (nd (kDag ext) 91) ==
    mul (nd (kDag ext) 91) (nd (kDag ext) 88)) = true := by
  rw [k_eq, t_eq, mul_unpackW', mul_unpackW', beq_unpack]
  exact kSmall'.2.2.2.2.2.1

theorem c_tt : (mul (nd (kDag ext) 91) (nd (kDag ext) 91) == one ()) = true := by
  rw [t_eq, mul_unpackW', CFSG.KC.Co1B.one_eq, beq_unpack]
  exact kSmall'.2.2.2.2.2.2.1

theorem x2_eq : mul (mul (nd (kDag ext) 91) (nd (kDag ext) 89)) (ndI (kDag ext) 91) =
    unpackR 24 X2K := by
  rw [t_eq, x1_eq, tI_eq, mul_unpackW', mul_unpackW']
  rfl

theorem y2_eq : mul (mul (nd (kDag ext) 91) (nd (kDag ext) 90)) (ndI (kDag ext) 91) =
    unpackR 24 Y2K := by
  rw [t_eq, y1_eq, tI_eq, mul_unpackW', mul_unpackW']
  rfl

theorem c_xx : (mul (nd (kDag ext) 89) (mul (mul (nd (kDag ext) 91) (nd (kDag ext) 89))
    (ndI (kDag ext) 91)) == mul (mul (mul (nd (kDag ext) 91) (nd (kDag ext) 89))
    (ndI (kDag ext) 91)) (nd (kDag ext) 89)) = true := by
  rw [x2_eq, x1_eq, mul_unpackW', mul_unpackW', beq_unpack]
  exact kSmall'.2.2.2.2.2.2.2.1

theorem c_xy : (mul (nd (kDag ext) 89) (mul (mul (nd (kDag ext) 91) (nd (kDag ext) 90))
    (ndI (kDag ext) 91)) == mul (mul (mul (nd (kDag ext) 91) (nd (kDag ext) 90))
    (ndI (kDag ext) 91)) (nd (kDag ext) 89)) = true := by
  rw [y2_eq, x1_eq, mul_unpackW', mul_unpackW', beq_unpack]
  exact kSmall'.2.2.2.2.2.2.2.2.1

theorem c_yx : (mul (nd (kDag ext) 90) (mul (mul (nd (kDag ext) 91) (nd (kDag ext) 89))
    (ndI (kDag ext) 91)) == mul (mul (mul (nd (kDag ext) 91) (nd (kDag ext) 89))
    (ndI (kDag ext) 91)) (nd (kDag ext) 90)) = true := by
  rw [x2_eq, y1_eq, mul_unpackW', mul_unpackW', beq_unpack]
  exact kSmall'.2.2.2.2.2.2.2.2.2.1

theorem c_yy : (mul (nd (kDag ext) 90) (mul (mul (nd (kDag ext) 91) (nd (kDag ext) 90))
    (ndI (kDag ext) 91)) == mul (mul (mul (nd (kDag ext) 91) (nd (kDag ext) 90))
    (ndI (kDag ext) 91)) (nd (kDag ext) 90)) = true := by
  rw [y2_eq, y1_eq, mul_unpackW', mul_unpackW', beq_unpack]
  exact kSmall'.2.2.2.2.2.2.2.2.2.2

theorem kLT' : gtPinK LM 2 200 LT.N LT.P LT.PAR LT.LAB LT.W LT.S = true ∧ LT.N = 60 := by
  have h := kLT
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  exact h

theorem kET' : gtPinK EM 4 40000 ET.N ET.P ET.PAR ET.LAB ET.W ET.S = true ∧ ET.N = 36000 := by
  refine ⟨gtPinK_of_seg kETh kETs, Nat.eq_of_beq_eq_true ?_⟩
  quickRfl

theorem LG_eq : [nd (kDag ext) 89, nd (kDag ext) 90].toArray = gensArr 2 LM := by
  rw [x1_eq, y1_eq]
  apply Array.ext (by simp [gensArr])
  intro i h1 h2
  have hi : i < 2 := by simpa using h1
  interval_cases i <;> simp [gensArr, LM, X1K, Y1K, unpackR_eq_unpack]

theorem EG_eq : [nd (kDag ext) 88, nd (kDag ext) 89, nd (kDag ext) 90, nd (kDag ext) 91].toArray =
    gensArr 4 EM := by
  rw [k_eq, x1_eq, y1_eq, t_eq]
  apply Array.ext (by simp [gensArr])
  intro i h1 h2
  have hi : i < 4 := by simpa using h1
  interval_cases i <;> simp [gensArr, EM, KK, X1K, Y1K, TK, unpackR_eq_unpack]

theorem gtL_eq : gtBFS [nd (kDag ext) 89, nd (kDag ext) 90].toArray 200 =
    bfsTree LT.N LT.P LT.PAR LT.LAB := by
  rw [LG_eq]
  exact (gtBFS_of_K kLT'.1).1

theorem gtE_eq : gtBFS [nd (kDag ext) 88, nd (kDag ext) 89, nd (kDag ext) 90,
    nd (kDag ext) 91].toArray 40000 = bfsTree ET.N ET.P ET.PAR ET.LAB := by
  rw [EG_eq]
  exact (gtBFS_of_K kET'.1).1

theorem c_gtL : gtOK [nd (kDag ext) 89, nd (kDag ext) 90].toArray
    (gtBFS [nd (kDag ext) 89, nd (kDag ext) 90].toArray 200) = true := by
  rw [gtL_eq, LG_eq]
  exact (gtBFS_of_K kLT'.1).2

theorem c_gtE : gtOK [nd (kDag ext) 88, nd (kDag ext) 89, nd (kDag ext) 90, nd (kDag ext) 91].toArray
    (gtBFS [nd (kDag ext) 88, nd (kDag ext) 89, nd (kDag ext) 90, nd (kDag ext) 91].toArray 40000) =
    true := by
  rw [gtE_eq, EG_eq]
  exact (gtBFS_of_K kET'.1).2

theorem c_sizeL : decide ((gtBFS [nd (kDag ext) 89, nd (kDag ext) 90].toArray 200).pts.size = 60) =
    true := by
  rw [gtL_eq, decide_eq_true_iff]
  simp [bfsTree, kLT'.2]

theorem c_sizeE : decide ((gtBFS [nd (kDag ext) 88, nd (kDag ext) 89, nd (kDag ext) 90,
    nd (kDag ext) 91].toArray 40000).pts.size = 36000) = true := by
  rw [gtE_eq, decide_eq_true_iff]
  simp [bfsTree, kET'.2]

theorem sizeL : (bfsTree LT.N LT.P LT.PAR LT.LAB).pts.size = 60 := by
  simp [bfsTree, kLT'.2]

theorem ptL {i : Nat} (hi : i < 60) :
    (bfsTree LT.N LT.P LT.PAR LT.LAB).pts[i]! = unpackR 24 (LT.P i) := by
  rw [getElem!_pos _ _ (by rw [sizeL]; exact hi), unpackR_eq_unpack]
  simp [bfsTree]

theorem invL {i : Nat} (hi : i < 60) :
    mul (unpackR 24 (LT.P i)) (unpackR 24 (LI i)) = one () ∧
      inv (unpackR 24 (LT.P i)) = unpackR 24 (LI i) := by
  rw [unpackR_eq_unpack, unpackR_eq_unpack]
  exact invOKW_sound (allN_true' kInv i hi)

theorem c_inv : invOK (gtBFS [nd (kDag ext) 89, nd (kDag ext) 90].toArray 200).pts = true := by
  rw [gtL_eq]
  unfold invOK
  rw [List.all_eq_true]
  intro i hi
  have hi' : i < 60 := by
    have := List.mem_range.1 hi
    rwa [sizeL] at this
  rw [ptL hi', (invL hi').2, (invL hi').1, CFSG.KC.Co1B.one_eq, beq_self_eq_true]

theorem kCW' : getL 0 KB.CW 0 < 60 ∧ getL 0 KB.CW 1 < 60 ∧ getL 0 KB.CW 2 < 60 ∧
    getL 0 KB.CW 3 < 60 ∧
    eqK (mulWK (mulWK (LT.P (getL 0 KB.CW 0)) (LT.P (getL 0 KB.CW 1)))
      (mulWK (LI (getL 0 KB.CW 0)) (LI (getL 0 KB.CW 1)))) X1K = true ∧
    eqK (mulWK (mulWK (LT.P (getL 0 KB.CW 2)) (LT.P (getL 0 KB.CW 3)))
      (mulWK (LI (getL 0 KB.CW 2)) (LI (getL 0 KB.CW 3)))) Y1K = true := by
  have h := kCW
  simp only [Bool.and_eq_true, Nat.blt_eq] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem comm_of {a b X : Nat} (ha : a < 60) (hb : b < 60)
    (h : eqK (mulWK (mulWK (LT.P a) (LT.P b)) (mulWK (LI a) (LI b))) X = true) :
    commRows (bfsTree LT.N LT.P LT.PAR LT.LAB).pts (unpackR 24 X) = true := by
  unfold commRows
  rw [List.any_eq_true]
  refine ⟨a, List.mem_range.2 (by rw [sizeL]; exact ha), ?_⟩
  rw [List.any_eq_true]
  refine ⟨b, List.mem_range.2 (by rw [sizeL]; exact hb), ?_⟩
  rw [ptL ha, ptL hb, (invL ha).2, (invL hb).2, mul_unpackW', mul_unpackW', mul_unpackW',
    beq_unpack]
  exact h

theorem c_cx : commRows (gtBFS [nd (kDag ext) 89, nd (kDag ext) 90].toArray 200).pts
    (nd (kDag ext) 89) = true := by
  rw [gtL_eq, x1_eq]
  exact comm_of kCW'.1 kCW'.2.1 kCW'.2.2.2.2.1

theorem c_cy : commRows (gtBFS [nd (kDag ext) 89, nd (kDag ext) 90].toArray 200).pts
    (nd (kDag ext) 90) = true := by
  rw [gtL_eq, y1_eq]
  exact comm_of kCW'.2.2.1 kCW'.2.2.2.1 kCW'.2.2.2.2.2

theorem kT' : KB.T.length = 5 ∧ ∀ i < 5, eqK (getL 0 KB.T i) (trK 24 (powWK KK i)) = true := by
  have h := kT
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  exact ⟨h.1, allN_true' h.2⟩

theorem cs1 : colsOf (powList (nd (kDag ext) 88) 5) = (KB.T.map (unpackR 24)).toArray := by
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

theorem kNF {i : Nat} (hi : i < 8) : memK XB (base.getD i 0) = true ∧
    (KB.CNs.getD i []).length = 9 ∧ (KB.CNs.getD i []).sum ≤ cnts.getD i 0 := by
  have h := kNs
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  have h' := allN_true' h.2 i hi
  simp only [Bool.and_eq_true, Nat.beq_eq] at h'
  exact ⟨h'.1.1, h'.1.2, Nat.le_of_ble_eq_true h'.2⟩

theorem chunks1 : ∀ n < 72,
    lvlChunkP 5 XB KB.T KB.CFs KB.NP CertificateChecks.KernelCo1B.CV.F KB.CNs n = true := by
  intro n hn
  rcases Nat.lt_or_ge n 36 with h | h
  · interval_cases n
    exacts [ch17325pA0, ch17325pA1, ch17325pA2, ch17325pA3, ch17325pA4, ch17325pA5, ch17325pA6,
      ch17325pA7, ch17325pA8, ch17325pA9, ch17325pA10, ch17325pA11, ch17325pA12, ch17325pA13,
      ch17325pA14, ch17325pA15, ch17325pA16, ch17325pA17, ch17325pA18, ch17325pA19, ch17325pA20,
      ch17325pA21, ch17325pA22, ch17325pA23, ch17325pA24, ch17325pA25, ch17325pA26,
      ch17325pA27, ch17325pA28, ch17325pA29, ch17325pA30, ch17325pA31, ch17325pA32,
      ch17325pA33, ch17325pA34, ch17325pA35]
  · interval_cases n
    exacts [ch17325pA36, ch17325pA37, ch17325pA38, ch17325pA39, ch17325pA40, ch17325pA41,
      ch17325pA42, ch17325pA43, ch17325pA44, ch17325pA45, ch17325pA46, ch17325pA47,
      ch17325pA48, ch17325pA49, ch17325pA50, ch17325pA51, ch17325pA52, ch17325pA53,
      ch17325pA54, ch17325pA55, ch17325pA56, ch17325pA57, ch17325pA58, ch17325pA59,
      ch17325pA60, ch17325pA61, ch17325pA62, ch17325pA63, ch17325pA64, ch17325pA65,
      ch17325pA66, ch17325pA67, ch17325pA68, ch17325pA69, ch17325pA70, ch17325pA71]

theorem c_bound1 : boundOK (colsOf (powList (nd (kDag ext) 88) 5)) 5 base conds cnts span comb =
    true := by
  rw [cs1]
  exact boundOK_of_sel (m := 8) kT'.1 rfl rfl rfl (of_decide_eq_true kCFs)
    (fun i hi => kNF hi) chunks1 kSpan

theorem kT2' : KB.T2.length = 5 ∧ ∀ i < 5, eqK (getL 0 KB.T2 i) (trK 24 (getL 0 PTB i)) = true := by
  have h := kT2
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  exact ⟨h.1, allN_true' h.2⟩

theorem cs2 : colsOf (ptRowsB (nd (kDag ext) 88) (nd (kDag ext) 89) (nd (kDag ext) 90)
    (nd (kDag ext) 91) (ndI (kDag ext) 91)) = (KB.T2.map (unpackR 24)).toArray := by
  have hpt : ptRowsB (unpackR 24 KK) (unpackR 24 X1K) (unpackR 24 Y1K) (unpackR 24 TK)
      (unpackR 24 TI) = PTB.map (unpackR 24) := by
    simp only [ptRowsB, PTB, X2K, Y2K, List.map_cons, List.map_nil, mul_unpackW']
  have hPT : PTB.length = 5 := rfl
  obtain ⟨hl, hall⟩ := kT2'
  rw [k_eq, x1_eq, y1_eq, t_eq, tI_eq, hpt, colsOf, List.map_toArray, List.map_map]
  refine congrArg List.toArray ?_
  apply List.ext_getElem (by simp [hl, hPT])
  intro i h1 h2
  have hi : i < 5 := by simpa [hPT] using h1
  have e := beq_of_eqK (hall i hi)
  rw [CFSG.KC.Co1B.getL_eq, CFSG.KC.Co1B.getL_eq, List.getElem?_eq_getElem (by rw [hl]; exact hi),
    List.getElem?_eq_getElem (by rw [hPT]; exact hi), Option.getD_some, Option.getD_some] at e
  rw [List.getElem_map, List.getElem_map, Function.comp_apply, CFSG.KC.F2W.transposeRows_unpackR, e]

theorem kN2F {i : Nat} (hi : i < 6) : memK XB (base2.getD i 0) = true ∧
    (KB.CNs2.getD i []).length = 9 ∧ (KB.CNs2.getD i []).sum ≤ cnts2.getD i 0 := by
  have h := kNs2
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  have h' := allN_true' h.2 i hi
  simp only [Bool.and_eq_true, Nat.beq_eq] at h'
  exact ⟨h'.1.1, h'.1.2, Nat.le_of_ble_eq_true h'.2⟩

theorem chunks2 : ∀ n < 54,
    lvlChunkP 5 XB KB.T2 KB.CFs2 KB.NP2 CertificateChecks.KernelCo1B.CV.F KB.CNs2 n = true := by
  intro n hn
  rcases Nat.lt_or_ge n 27 with h | h
  · interval_cases n
    exacts [ch17325pB0, ch17325pB1, ch17325pB2, ch17325pB3, ch17325pB4, ch17325pB5, ch17325pB6,
      ch17325pB7, ch17325pB8, ch17325pB9, ch17325pB10, ch17325pB11, ch17325pB12, ch17325pB13,
      ch17325pB14, ch17325pB15, ch17325pB16, ch17325pB17, ch17325pB18, ch17325pB19, ch17325pB20,
      ch17325pB21, ch17325pB22, ch17325pB23, ch17325pB24, ch17325pB25, ch17325pB26]
  · interval_cases n
    exacts [ch17325pB27, ch17325pB28, ch17325pB29, ch17325pB30, ch17325pB31, ch17325pB32,
      ch17325pB33, ch17325pB34, ch17325pB35, ch17325pB36, ch17325pB37, ch17325pB38,
      ch17325pB39, ch17325pB40, ch17325pB41, ch17325pB42, ch17325pB43, ch17325pB44,
      ch17325pB45, ch17325pB46, ch17325pB47, ch17325pB48, ch17325pB49, ch17325pB50,
      ch17325pB51, ch17325pB52, ch17325pB53]

theorem c_bound2 : boundOK (colsOf (ptRowsB (nd (kDag ext) 88) (nd (kDag ext) 89) (nd (kDag ext) 90)
    (nd (kDag ext) 91) (ndI (kDag ext) 91))) 5 base2 conds2 cnts2 span2 comb2 = true := by
  rw [cs2]
  exact boundOK_of_sel (m := 6) kT2'.1 rfl rfl rfl (of_decide_eq_true kCFs2)
    (fun i hi => kN2F hi) chunks2 kSpan2

theorem c_prod1 : decide (cnts.prod ≤ 36000) = true := by decide
theorem c_prod2 : decide (cnts2.prod ≤ 5) = true := by decide

open Certificates in
open CFSG.HardMathSupport.Dickson.I271.TabCo1FiveB in
theorem c17325 : fiveBCheck () = true := by
  unfold fiveBCheck
  simp only [hflag, c_wfk, c_wf1, c_rep, c_pow, c_ne, c_kx, c_ky, c_kt, c_tt, c_xx, c_xy, c_yx,
    c_yy, c_gtL, c_sizeL, c_inv, c_cx, c_cy, c_gtE, c_sizeE, c_bound1, c_bound2, c_prod1, c_prod2,
    Bool.and_self]

end CertificateChecks.KernelCo1B.Bound17325

end
