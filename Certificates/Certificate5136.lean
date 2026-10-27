module

public import CFSG.GH74.Uniqueness.SU.KI1r4F61J2Inputs
public import Certificates.Data.Kernel.J2PairK
import Certificates.Kernel.J2Cover.K21
import Certificates.Kernel.J2Cover.AutChains
import Certificates.Kernel.J2Cover.ModelsBind
import Certificates.Kernel.LocalComp.Child3Lemmas
import CFSG.Certificates.Kernel.Child3Sound
import CFSG.Certificates.Kernel.Spor.PrimSound
import CFSG.Certificates.Kernel.Spor.RawSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

set_option maxRecDepth 400000

open CFSG.GH74.Uniqueness.SU.K.R4.J2M
open CFSG.ComponentClassification.J2Cover CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Certificates.Native CFSG.Sporadic.Th.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Child3 CFSG.KC.J2PairK
open CertificateChecks.KernelJ2Cover

namespace CertificateChecks.Batch5136

open CFSG.GH74.Uniqueness.SU.K.R4.J2M
open CFSG.ComponentClassification.J2Cover CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Certificates.Native CFSG.Sporadic.Th.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Child3 CFSG.KC.J2PairK
open CertificateChecks.KernelJ2Cover

theorem word_eq {S : Array (Array Nat)} {PS : Nat → Nat} :
    ∀ w : List Nat, (∀ i ∈ w, S[i]! = unpack 315 9 (PS i) ∧ CnN 315 9 (PS i)) →
      wordArr S w = unpack 315 9 (pw PS w) ∧ CnN 315 9 (pw PS w)
  | [], _ => ⟨hId.symm, cId⟩
  | i :: w, h => by
    obtain ⟨e, c⟩ := word_eq w fun j hj => h j (List.mem_cons_of_mem i hj)
    obtain ⟨ei, ci⟩ := h i List.mem_cons_self
    refine ⟨?_, canon_pcN ci c⟩
    rw [wordArr, ei, e, compA_unpackN ci c]
    rfl

theorem gens01 {S : Array (Array Nat)} {base : Array Nat} {PS : Nat → Nat} {kS nb BP : Nat}
    (hb : Binds 315 9 PS kS nb BP S base) (hk : 2 ≤ kS) (c0 : CnN 315 9 (PS 0))
    (c1 : CnN 315 9 (PS 1)) (w : List Nat) (hw : ∀ i ∈ w, i < 2) :
    ∀ i ∈ w, S[i]! = unpack 315 9 (PS i) ∧ CnN 315 9 (PS i) := by
  intro i hi
  have hi2 := hw i hi
  refine ⟨hb.2.2.2.2.1 i (by omega), ?_⟩
  interval_cases i
  · exact c0
  · exact c1

theorem pairCheck_of {R U V : Nat} (cR : CnN 315 9 R) (cU : CnN 315 9 U) (cV : CnN 315 9 V)
    (hiU : invEqK 315 9 (mask 9) (315 * 9) U U = true)
    (hiV : invEqK 315 9 (mask 9) (315 * 9) V V = true)
    (pU : inP (unpack 315 9 U) = true) (pV : inP (unpack 315 9 V) = true)
    (h : pairK R U V = true) :
    pairCheck (unpack 315 9 R) (unpack 315 9 U) (unpack 315 9 V) = true := by
  obtain ⟨eU, iU⟩ := invEqK_sound hiU
  obtain ⟨eV, iV⟩ := invEqK_sound hiV
  unfold pairCheck CFSG.ComponentClassification.J2Cover.commA
  rw [eU, eV, iU, iV, pU, pV, ← hId, compA_unpackN cU cR, compA_unpackN cR cU,
    compA_unpackN cV cR, compA_unpackN cR cV, compA_unpackN cU cU, compA_unpackN cV cV,
    compA_unpackN cU cV, compA_unpackN cV cU,
    eqA_unpackN (canon_pcN cU cR) (canon_pcN cR cU), eqA_unpackN (canon_pcN cV cR) (canon_pcN cR cV),
    eqA_unpackN (canon_pcN cU cU) cId, eqA_unpackN (canon_pcN cV cV) cId, eqA_unpackN cU cId,
    eqA_unpackN cV cId, eqA_unpackN cU cV, eqA_unpackN (canon_pcN cU cV) (canon_pcN cV cU)]
  unfold pairK at h
  simpa using h

theorem inP_pw {G : Nat} (c : CnN 315 9 G)
    (hz : Nat.beq (Nat.shiftRight G (315 * 9)) 0 = true)
    (hs : siftK 315 9 (mask 9) (315 * 9) (pidn 315 9) PA.LR PA.TRI PA.BP 3 0 G = true) :
    inP (unpack 315 9 G) = true :=
  inP_of rfl hz (range_of_canonK c) hs

theorem check_A : pairCheck autStrong[0]! (wordArr cent2BStrong [1, 0])
    (wordArr cent2BStrong [1, 1, 1]) = true := by
  have g := gens01 c2B_binds (by norm_num) (by quickRfl) (by quickRfl)
  obtain ⟨eU, cU⟩ := word_eq [1, 0] (g _ (by decide))
  obtain ⟨eV, cV⟩ := word_eq [1, 1, 1] (g _ (by decide))
  rw [ha, eU, eV]
  exact pairCheck_of cA cU cV (by quickRfl) (by quickRfl) (inP_pw cU (by quickRfl) (by quickRfl))
    (inP_pw cV (by quickRfl) (by quickRfl)) (by quickRfl)

theorem check_TwoA : pairCheck twoAArr (wordArr cent2AStrong [0, 0, 0, 0, 0])
    (wordArr cent2AStrong [1, 0, 1, 0, 1, 1]) = true := by
  have g := gens01 c2A_binds (by norm_num) (by quickRfl) (by quickRfl)
  obtain ⟨eU, cU⟩ := word_eq [0, 0, 0, 0, 0] (g _ (by decide))
  obtain ⟨eV, cV⟩ := word_eq [1, 0, 1, 0, 1, 1] (g _ (by decide))
  rw [hta, eU, eV]
  exact pairCheck_of (by quickRfl) cU cV (by quickRfl) (by quickRfl)
    (inP_pw cU (by quickRfl) (by quickRfl)) (inP_pw cV (by quickRfl) (by quickRfl)) (by quickRfl)

theorem check_U : pairCheck outerArr (wordArr centOuterStrong [0, 1, 1, 0, 0, 1, 1, 0])
    (wordArr centOuterStrong [1, 1, 1]) = true := by
  have g := gens01 cOu_binds (by norm_num) (by quickRfl) (by quickRfl)
  obtain ⟨eU, cU⟩ := word_eq [0, 1, 1, 0, 0, 1, 1, 0] (g _ (by decide))
  obtain ⟨eV, cV⟩ := word_eq [1, 1, 1] (g _ (by decide))
  rw [hou, eU, eV]
  exact pairCheck_of (by quickRfl) cU cV (by quickRfl) (by quickRfl)
    (inP_pw cU (by quickRfl) (by quickRfl)) (inP_pw cV (by quickRfl) (by quickRfl)) (by quickRfl)

end CertificateChecks.Batch5136

public section

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.Uniqueness in
open CFSG.GH74.Uniqueness.SU in
open CFSG.GH74.Uniqueness.SU.K in
open CFSG.GH74.Uniqueness.SU.K.R4 in
open CFSG.GH74.Uniqueness.SU.K.R4.J2M in
open CFSG.ComponentClassification.J2Cover CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native in
open CFSG.Certificates.Native CFSG.Sporadic.Th.Native in
theorem certificate5136 : (pairCheck autStrong[0]! (CFSG.GH74.Uniqueness.SU.K.R4.J2M.wordArr cent2BStrong [1, 0])
    (CFSG.GH74.Uniqueness.SU.K.R4.J2M.wordArr cent2BStrong [1, 1, 1]) = true)
    ∧ (pairCheck twoAArr (CFSG.GH74.Uniqueness.SU.K.R4.J2M.wordArr cent2AStrong [0, 0, 0, 0, 0])
    (CFSG.GH74.Uniqueness.SU.K.R4.J2M.wordArr cent2AStrong [1, 0, 1, 0, 1, 1]) = true)
    ∧ (pairCheck outerArr (CFSG.GH74.Uniqueness.SU.K.R4.J2M.wordArr centOuterStrong [0, 1, 1, 0, 0, 1, 1, 0])
    (CFSG.GH74.Uniqueness.SU.K.R4.J2M.wordArr centOuterStrong [1, 1, 1]) = true) :=
  ⟨CertificateChecks.Batch5136.check_A, CertificateChecks.Batch5136.check_TwoA, CertificateChecks.Batch5136.check_U⟩

end Certificates
