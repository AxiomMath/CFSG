module

public import Certificates.Data.TabCo1ThreeA
public meta import Certificates.Data.TabCo1ThreeA
public import Certificates.Kernel.Co1B.Chk17620
public import Certificates.Kernel.Co1B.Lvl17620A
public import Certificates.Kernel.Co1B.Lvl17620B
public import Certificates.Kernel.Co1B.Lvl17620C
public import Certificates.Kernel.Co1B.C17330
import Mathlib.Tactic.IntervalCases
public import CFSG.Monster.B.TwoA.Par3.Main

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.Bound17620

open CFSG.KC.Co1BBoundP (lvlChunkP)
open CFSG.KC.Co1BBoundN CFSG.KC.Co1BBound CFSG.KC.Co1BSpin CFSG.KC.Co1B CFSG.KC.Co1F2 CFSG.KC.M1F2
  CFSG.KLie.CT CFSG.KC.Enum CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeA
  CFSG.HardMathSupport.Dickson.I271.TabCo1 CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1.TwoBNative
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

theorem kDagA_eq : kDag ext = ((List.range 97).map fun i => CFSG.KS.Raw.unpack 24 24 (DA.M i),
    (List.range 97).map fun i => CFSG.KS.Raw.unpack 24 24 (DA.MI i), true) := by
  rw [kDag, ← kDAW]
  exact dagWK_sound DA_base kDA

theorem hflag : (kDag ext).2.2 = true := by
  rw [kDagA_eq]

theorem nd_eq {i : Nat} (h1 : 0 < i) (h2 : i ≤ 97) : nd (kDag ext) i = unpackR 24 (DA.M (i - 1)) := by
  rw [nd, kDagA_eq,
    List.getD_eq_getElem _ _ (by simp only [List.length_map, List.length_range]; omega),
    List.getElem_map, List.getElem_range, unpackR_eq_unpack]

theorem ndI_eq {i : Nat} (h1 : 0 < i) (h2 : i ≤ 97) :
    ndI (kDag ext) i = unpackR 24 (DA.MI (i - 1)) := by
  rw [ndI, kDagA_eq,
    List.getD_eq_getElem _ _ (by simp only [List.length_map, List.length_range]; omega),
    List.getElem_map, List.getElem_range, unpackR_eq_unpack]

theorem x_eq : nd (kDag ext) 95 = unpackR 24 XK := nd_eq (by decide) (by decide)
theorem u_eq : nd (kDag ext) 96 = unpackR 24 UK := nd_eq (by decide) (by decide)
theorem w_eq : nd (kDag ext) 97 = unpackR 24 WK := nd_eq (by decide) (by decide)
theorem uI_eq : ndI (kDag ext) 96 = unpackR 24 UI := ndI_eq (by decide) (by decide)
theorem wI_eq : ndI (kDag ext) 97 = unpackR 24 WI := ndI_eq (by decide) (by decide)
theorem g0_eq : nd (kDag ext) 88 = unpackR 24 (EK 0) := nd_eq (by decide) (by decide)
theorem g1_eq : nd (kDag ext) 89 = unpackR 24 (EK 1) := nd_eq (by decide) (by decide)

theorem evalW_eq (w : List Int) :
    evalW (kDag ext) [88, 89, 90, 91, 92, 93, 94] w = unpackR 24 (wordK RS7 IS7 w) := by
  have h1 : [88, 89, 90, 91, 92, 93, 94].map (nd (kDag ext)) = RS7.map (unpackR 24) := by
    simp only [List.map_cons, List.map_nil, nd_eq (i := 88) (by decide) (by decide),
      nd_eq (i := 89) (by decide) (by decide), nd_eq (i := 90) (by decide) (by decide),
      nd_eq (i := 91) (by decide) (by decide), nd_eq (i := 92) (by decide) (by decide),
      nd_eq (i := 93) (by decide) (by decide), nd_eq (i := 94) (by decide) (by decide)]
    rfl
  have h2 : [88, 89, 90, 91, 92, 93, 94].map (ndI (kDag ext)) = IS7.map (unpackR 24) := by
    simp only [List.map_cons, List.map_nil, ndI_eq (i := 88) (by decide) (by decide),
      ndI_eq (i := 89) (by decide) (by decide), ndI_eq (i := 90) (by decide) (by decide),
      ndI_eq (i := 91) (by decide) (by decide), ndI_eq (i := 92) (by decide) (by decide),
      ndI_eq (i := 93) (by decide) (by decide), ndI_eq (i := 94) (by decide) (by decide)]
    rfl
  rw [evalW, h1, h2, word_sound]

theorem kOrd' : eqK (powWK XK 3) oneK = true ∧ notB (eqK XK oneK) = true ∧ eqK XK RA = true := by
  have h := kOrd
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem kCom' : (∀ j < 10, eqK (mulWK XK (EK j)) (mulWK (EK j) XK) = true) ∧
    notB (eqK (mulWK (EK 0) (EK 1)) (mulWK (EK 1) (EK 0))) = true := by
  have h := kCom
  simp only [Bool.and_eq_true] at h
  exact ⟨allN_true' h.1, h.2⟩

theorem c_wfx : wf (nd (kDag ext) 95) = true := by
  rw [x_eq]
  exact wf_unpackR _

theorem c_wf1 : wf (one ()) = true := by
  rw [CFSG.KC.Co1B.one_eq]
  exact wf_unpackR _

theorem c_root : (nd (kDag ext) 95 == rootRows3A ()) = true := by
  unfold rootRows3A
  rw [x_eq, CertificateChecks.KernelSporSch.Co1Elem.aRows_eq]
  simp only [← unpackR_eq_unpack, mul_unpackW', beq_unpack]
  exact kOrd'.2.2

theorem c_ne : (nd (kDag ext) 95 != one ()) = true := by
  rw [x_eq, CFSG.KC.Co1B.one_eq, bne, beq_unpack]
  exact not_of_notB kOrd'.2.1

theorem c_pow : (pow (nd (kDag ext) 95) 3 == one ()) = true := by
  rw [x_eq, pow_unpack', CFSG.KC.Co1B.one_eq, beq_unpack]
  exact kOrd'.1

theorem com_j {i : Nat} (h1 : 88 ≤ i) (h2 : i ≤ 97) :
    (mul (nd (kDag ext) 95) (nd (kDag ext) i) == mul (nd (kDag ext) i) (nd (kDag ext) 95)) =
      true := by
  have h := kCom'.1 (i - 88) (by omega)
  have e : Nat.add 87 (i - 88) = i - 1 := by
    change 87 + (i - 88) = i - 1
    omega
  unfold EK at h
  rw [e] at h
  rw [x_eq, nd_eq (by omega) h2, mul_unpackW', mul_unpackW', beq_unpack]
  exact h

theorem c_com : ([88, 89, 90, 91, 92, 93, 94].all fun i =>
    mul (nd (kDag ext) 95) (nd (kDag ext) i) == mul (nd (kDag ext) i) (nd (kDag ext) 95)) =
      true := by
  rw [List.all_eq_true]
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  exact com_j (by omega) (by omega)

theorem c_xu : (mul (nd (kDag ext) 95) (nd (kDag ext) 96) ==
    mul (nd (kDag ext) 96) (nd (kDag ext) 95)) = true := com_j (by decide) (by decide)

theorem c_xw : (mul (nd (kDag ext) 95) (nd (kDag ext) 97) ==
    mul (nd (kDag ext) 97) (nd (kDag ext) 95)) = true := com_j (by decide) (by decide)

theorem c_wf01 : wf (mul (nd (kDag ext) 88) (nd (kDag ext) 89)) = true := by
  rw [g0_eq, g1_eq, mul_unpackW']
  exact wf_unpackR _

theorem c_wf10 : wf (mul (nd (kDag ext) 89) (nd (kDag ext) 88)) = true := by
  rw [g0_eq, g1_eq, mul_unpackW']
  exact wf_unpackR _

theorem c_01 : (mul (nd (kDag ext) 88) (nd (kDag ext) 89) !=
    mul (nd (kDag ext) 89) (nd (kDag ext) 88)) = true := by
  rw [g0_eq, g1_eq, mul_unpackW', mul_unpackW', bne, beq_unpack]
  exact not_of_notB kCom'.2

theorem c_rels : (relsS.all fun w =>
    evalW (kDag ext) [88, 89, 90, 91, 92, 93, 94] w == one () ||
      evalW (kDag ext) [88, 89, 90, 91, 92, 93, 94] w == nd (kDag ext) 95 ||
      evalW (kDag ext) [88, 89, 90, 91, 92, 93, 94] w == pow (nd (kDag ext) 95) 2) = true := by
  rw [List.all_eq_true]
  intro w hw
  have h := List.all_eq_true.1 kRel w hw
  unfold relOK at h
  rw [evalW_eq, x_eq, CFSG.KC.Co1B.one_eq, pow_unpack']
  simp only [beq_unpack]
  exact h

theorem c_cm : (mul (mul (ndI (kDag ext) 96) (ndI (kDag ext) 97))
    (mul (nd (kDag ext) 96) (nd (kDag ext) 97)) == nd (kDag ext) 95) = true := by
  rw [uI_eq, wI_eq, u_eq, w_eq, x_eq, mul_unpackW', mul_unpackW', mul_unpackW', beq_unpack]
  exact kCm

theorem kT' : KA.T.length = 3 ∧ ∀ i < 3, eqK (getL 0 KA.T i) (trK 24 (powWK XK i)) = true := by
  have h := kT
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  exact ⟨h.1, allN_true' h.2⟩

theorem cs1 : colsOf (powList (nd (kDag ext) 95) 3) = (KA.T.map (unpackR 24)).toArray := by
  obtain ⟨hl, hall⟩ := kT'
  rw [x_eq, colsOf, powList, List.map_toArray, List.map_map]
  refine congrArg List.toArray ?_
  apply List.ext_getElem (by simp [hl])
  intro i h1 h2
  have hi : i < 3 := by simpa using h1
  have e := beq_of_eqK (hall i hi)
  rw [CFSG.KC.Co1B.getL_eq, List.getElem?_eq_getElem (by rw [hl]; exact hi), Option.getD_some] at e
  rw [List.getElem_map, List.getElem_map, List.getElem_range, Function.comp_apply, pow_unpack',
    CFSG.KC.F2W.transposeRows_unpackR, e]

theorem kNF {i : Nat} (hi : i < 12) : memK XB (base.getD i 0) = true ∧
    (KA.CNs.getD i []).length = 9 ∧ (KA.CNs.getD i []).sum ≤ cnts.getD i 0 := by
  have h := kNs
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  have h' := allN_true' h.2 i hi
  simp only [Bool.and_eq_true, Nat.beq_eq] at h'
  exact ⟨h'.1.1, h'.1.2, Nat.le_of_ble_eq_true h'.2⟩

theorem chunks : ∀ n < 108,
    lvlChunkP 3 XB KA.T ([] :: KA.CFt) KA.NP CertificateChecks.KernelCo1B.CV.F KA.CNs n = true := by
  intro n hn
  rcases Nat.lt_or_ge n 36 with h | h
  · interval_cases n
    exacts [ch17620p0, ch17620p1, ch17620p2, ch17620p3, ch17620p4, ch17620p5, ch17620p6,
      ch17620p7, ch17620p8, ch17620p9, ch17620p10, ch17620p11, ch17620p12, ch17620p13,
      ch17620p14, ch17620p15, ch17620p16, ch17620p17, ch17620p18, ch17620p19, ch17620p20,
      ch17620p21, ch17620p22, ch17620p23, ch17620p24, ch17620p25, ch17620p26, ch17620p27,
      ch17620p28, ch17620p29, ch17620p30, ch17620p31, ch17620p32, ch17620p33, ch17620p34,
      ch17620p35]
  rcases Nat.lt_or_ge n 72 with h' | h'
  · interval_cases n
    exacts [ch17620q36, ch17620q37, ch17620q38, ch17620q39, ch17620q40, ch17620q41,
      ch17620q42, ch17620q43, ch17620q44, ch17620q45, ch17620q46, ch17620q47, ch17620q48,
      ch17620q49, ch17620q50, ch17620q51, ch17620q52, ch17620q53, ch17620q54, ch17620q55,
      ch17620q56, ch17620q57, ch17620q58, ch17620q59, ch17620q60, ch17620q61, ch17620q62,
      ch17620q63, ch17620q64, ch17620q65, ch17620q66, ch17620q67, ch17620q68, ch17620q69,
      ch17620q70, ch17620q71]
  · interval_cases n
    exacts [ch17620r72, ch17620r73, ch17620r74, ch17620r75, ch17620r76, ch17620r77,
      ch17620r78, ch17620r79, ch17620r80, ch17620r81, ch17620r82, ch17620r83, ch17620r84,
      ch17620r85, ch17620r86, ch17620r87, ch17620r88, ch17620r89, ch17620r90, ch17620r91,
      ch17620r92, ch17620r93, ch17620r94, ch17620r95, ch17620r96, ch17620r97, ch17620r98,
      ch17620r99, ch17620r100, ch17620r101, ch17620r102, ch17620r103, ch17620r104,
      ch17620r105, ch17620r106, ch17620r107]

theorem c_bound : boundOK (colsOf (powList (nd (kDag ext) 95) 3)) 3 base conds cnts span comb =
    true := by
  rw [cs1]
  exact boundOK_of_sel (m := 12) kT'.1 rfl rfl rfl (of_decide_eq_true kCFs)
    (fun i hi => kNF hi) chunks kSpan

theorem c_prod : decide (cnts.prod ≤ 1345036492800) = true := by decide

open Certificates in
open CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeA in
theorem c17620 : threeACheck () = true := by
  unfold threeACheck
  simp only [hflag, c_wfx, c_wf1, c_root, c_ne, c_pow, c_com, c_xu, c_xw, c_wf01, c_wf10, c_01,
    c_rels, c_cm, c_bound, c_prod, Bool.and_self]

end CertificateChecks.KernelCo1B.Bound17620

end
