module

public import Certificates.Data.TabCo1ThreeDRoot
public meta import Certificates.Data.TabCo1ThreeDRoot
public import Certificates.Kernel.Co1B.Chk17592
public import Certificates.Kernel.Co1B.Lvl17592A
public import Certificates.Kernel.Co1B.Lvl17592B
public import Certificates.Kernel.Co1B.C17330
public import Certificates.Kernel.Co1ThreeK.LettersEq
import Mathlib.Tactic.IntervalCases
public import CFSG.Monster.B.TwoA.Par3.Main

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.Bound17592

open CFSG.KC.Co1BBoundP (lvlChunkP)
open CFSG.KC.Co1BBoundN CFSG.KC.Co1BBound CFSG.KC.Co1BSpin CFSG.KC.Co1B CFSG.KC.Co1F2 CFSG.KC.M1F2
  CFSG.KLie.CT CFSG.KC.Enum CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeDRoot
  CFSG.HardMathSupport.Dickson.I271.TabCo1 CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Block
open CertificateChecks.KernelCo1B.Bound17591 (XB)
open CertificateChecks.KernelCo1B.Bound17330 (boundOK_of_sel)
open CFSG.KS.SporSch.M24 (unpackR_eq_unpack)

theorem root_eq : rootRows3D () = unpackR 24 RR := by
  unfold rootRows3D RR
  rw [CertificateChecks.KernelCo1ThreeK.rootRows_eq (by decide), ← unpackR_eq_unpack]

theorem kT' : KD.T.length = 3 ∧ ∀ i < 3, eqK (getL 0 KD.T i) (trK 24 (powWK RR i)) = true := by
  have h := kT
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  exact ⟨h.1, allN_true' h.2⟩

theorem cs1 : colsOf (powList (rootRows3D ()) 3) = (KD.T.map (unpackR 24)).toArray := by
  obtain ⟨hl, hall⟩ := kT'
  rw [root_eq, colsOf, powList, List.map_toArray, List.map_map]
  refine congrArg List.toArray ?_
  apply List.ext_getElem (by simp [hl])
  intro i h1 h2
  have hi : i < 3 := by simpa using h1
  have e := beq_of_eqK (hall i hi)
  rw [CFSG.KC.Co1B.getL_eq, List.getElem?_eq_getElem (by rw [hl]; exact hi), Option.getD_some] at e
  rw [List.getElem_map, List.getElem_map, List.getElem_range, Function.comp_apply, pow_unpack',
    CFSG.KC.F2W.transposeRows_unpackR, e]

theorem kNF {i : Nat} (hi : i < 8) : memK XB (base.getD i 0) = true ∧
    (KD.CNs.getD i []).length = 9 ∧ (KD.CNs.getD i []).sum ≤ cnts.getD i 0 := by
  have h := kNs
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  have h' := allN_true' h.2 i hi
  simp only [Bool.and_eq_true, Nat.beq_eq] at h'
  exact ⟨h'.1.1, h'.1.2, Nat.le_of_ble_eq_true h'.2⟩

theorem chunks : ∀ n < 72,
    lvlChunkP 3 XB KD.T KD.CFs KD.NP CertificateChecks.KernelCo1B.CV.F KD.CNs n = true := by
  intro n hn
  rcases Nat.lt_or_ge n 36 with h | h
  · interval_cases n
    exacts [ch17592p0, ch17592p1, ch17592p2, ch17592p3, ch17592p4, ch17592p5, ch17592p6,
      ch17592p7, ch17592p8, ch17592p9, ch17592p10, ch17592p11, ch17592p12, ch17592p13,
      ch17592p14, ch17592p15, ch17592p16, ch17592p17, ch17592p18, ch17592p19, ch17592p20,
      ch17592p21, ch17592p22, ch17592p23, ch17592p24, ch17592p25, ch17592p26, ch17592p27,
      ch17592p28, ch17592p29, ch17592p30, ch17592p31, ch17592p32, ch17592p33, ch17592p34,
      ch17592p35]
  · interval_cases n
    exacts [ch17592q36, ch17592q37, ch17592q38, ch17592q39, ch17592q40, ch17592q41,
      ch17592q42, ch17592q43, ch17592q44, ch17592q45, ch17592q46, ch17592q47, ch17592q48,
      ch17592q49, ch17592q50, ch17592q51, ch17592q52, ch17592q53, ch17592q54, ch17592q55,
      ch17592q56, ch17592q57, ch17592q58, ch17592q59, ch17592q60, ch17592q61, ch17592q62,
      ch17592q63, ch17592q64, ch17592q65, ch17592q66, ch17592q67, ch17592q68, ch17592q69,
      ch17592q70, ch17592q71]

theorem c_bound : boundOK (colsOf (powList (rootRows3D ()) 3)) 3 base conds cnts span comb =
    true := by
  rw [cs1]
  exact boundOK_of_sel (m := 8) kT'.1 rfl rfl rfl (of_decide_eq_true kCFs)
    (fun i hi => kNF hi) chunks kSpan

open Certificates in
open CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeDRoot in
theorem c17592 : rootCheck () = true := by
  unfold rootCheck
  rw [c_bound, Bool.true_and]
  decide

end CertificateChecks.KernelCo1B.Bound17592

end
