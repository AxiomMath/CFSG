module

public import CFSG.ClassicalInvolution.SmallCases.Sporadic.J2Inputs
import Certificates.Kernel.SchreierFam.J2UN
import CFSG.Certificates.Kernel.SchreierFam.All3Sound
import CFSG.Certificates.Kernel.Spor.RawSound
import CFSG.Certificates.Kernel.Spor.SiftRSound
import CFSG.Certificates.Kernel.Spor.SiftEq
import CFSG.Certificates.Kernel.Spor.PrimSound
import CFSG.Certificates.Kernel.Spor.PackWord
import CFSG.Certificates.Kernel.Spor.PackFld
import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.Misc.ArrBind
import Mathlib.Tactic.IntervalCases
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.Basic
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.ChainTools
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.Normalizer
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutOddCore
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.Sporadic.J2
public import CFSG.Sporadic.Th.F2Spec

set_option maxRecDepth 400000

namespace CertificateChecks.Batch9308

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.J2Proof CFSG.Certificates
  CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.ComponentClassification.J2Cover CFSG.Sporadic.RuSchreier CFSG.ClassicalInvolution.J2Data
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.Misc.ArrEnum
  CFSG.KS.SchreierFam CertificateChecks.KernelSchreierFam CertificateChecks.KernelJ2Cover
  CFSG.KC.BfsPin

theorem uBinds : Binds 315 9 JU.S 4 1 JU.BP uStrong uBase :=
  ⟨by norm_num, by norm_num, by norm_num, Nat.eq_of_beq_eq_true J2.uSize,
    J2.uS, rfl, J2.uBaseK⟩

theorem nBinds : Binds 315 9 JN.S 4 2 JN.BP nStrong nBase :=
  ⟨by norm_num, by norm_num, by norm_num, Nat.eq_of_beq_eq_true J2.nSize,
    J2.nS, rfl, J2.nBaseK⟩

theorem uChain : rawChainOK 315 (uStrong.extract 0 4) uStrong uBase uWords 4 = true ∧
    rawOrbitSizes 315 uStrong uBase = [32] := by
  refine ⟨?_, ?_⟩
  · have e : uWords = CFSG.Sporadic.Schreier.Co3.Native.wordsArr 4 4 dU := by decide
    rw [e]
    exact rawChainK_sound uBinds JU.head JU.hl J2.uNS JU.hs
  · rw [rawOrbitSizesK_sound uBinds J2.uPerm JU.hl]
    exact J2.uOrb

theorem nChain : rawChainOK 315 (nStrong.extract 0 3) nStrong nBase nWords 4 = true ∧
    rawOrbitSizes 315 nStrong nBase = [60, 2] := by
  refine ⟨?_, ?_⟩
  · have e : nWords = CFSG.Sporadic.Schreier.Co3.Native.wordsArr 3 4 dN := by decide
    rw [e]
    exact rawChainK_sound nBinds JN.head JN.hl J2.nNS JN.hs
  · rw [rawOrbitSizesK_sound nBinds J2.nPerm JN.hl]
    exact J2.nOrb

theorem canonU {k : Nat} (hk : k < 4) : canonK 315 9 (mask 9) (315 * 9) (JU.S k) = true :=
  allN_spec J2.canon.1 k hk

theorem canonA {k : Nat} (hk : k < 2) : canonK 315 9 (mask 9) (315 * 9) (C2A.S k) = true ∧
    canonK 315 9 (mask 9) (315 * 9) (C2A.SI k) = true :=
  (bAnd_iff _ _).1 (allN_spec J2.canon.2 k hk)

theorem sift_of {kS nb BP : Nat} {PS PSI LR TR TRI : Nat → Nat} {S : Array (Array Nat)}
    {base : Array Nat} (hb : Binds 315 9 PS kS nb BP S base)
    (hp : allN kS (fun j => permOK 315 9 (mask 9) (315 * 9) (PS j) (PSI j)) = true)
    (hl : LevelsOK 315 9 PS PSI LR TR TRI kS nb BP) {G : Nat}
    (hc : canonK 315 9 (mask 9) (315 * 9) G = true)
    (h : siftK 315 9 (mask 9) (315 * 9) (pidn 315 9) LR TRI BP nb 0 G = true) :
    siftA 315 (rawLevels 315 S base) base 0 (unpack 315 9 G) = true :=
  siftK_soundR hb hp hl rfl (canonK_facts hc).2.2.1 (range_of_canonK hc) h

theorem sifts : (∀ k < 4, siftA 315 cent2ALevels cent2ABase 0 uStrong[k]! = true) ∧
    (∀ k < 2, ∀ i < 4,
      siftA 315 uLevels uBase 0 (conjA 315 cent2AStrong[k]! uStrong[i]!) = true) ∧
    (∀ k < 3, siftA 315 cent2BLevels cent2BBase 0 nStrong[k]! = true) := by
  refine ⟨fun k hk => ?_, fun k hk i hi => ?_, fun k hk => ?_⟩
  · rw [uBinds.2.2.2.2.1 k hk]
    exact sift_of c2A_binds c2A_perm C2A.hl (canonU hk) (allN_spec J2.sA k hk)
  · obtain ⟨ck, cki⟩ := canonA hk
    have ek : cent2AStrong[k]! = unpack 315 9 (C2A.S k) := c2A_binds.2.2.2.2.1 k (by omega)
    have ei : invCand 315 (unpack 315 9 (C2A.S k)) = unpack 315 9 (C2A.SI k) :=
      (invEqK_sound (allN_spec c2A_perm k (by omega))).1
    rw [conjA, ek, uBinds.2.2.2.2.1 i hi, ei, compA_unpack ck (canonU hi),
      compA_unpack (canonK_pcomp ck (canonU hi)) cki]
    exact sift_of uBinds J2.uPerm JU.hl (canonK_pcomp (canonK_pcomp ck (canonU hi)) cki)
      (allN_spec (allN_spec J2.sC k hk) i hi)
  · have hc : canonK 315 9 (mask 9) (315 * 9) (JN.S k) = true := allN_spec J2.nCanon k hk
    rw [nBinds.2.2.2.2.1 k (by omega)]
    exact sift_of c2B_binds c2B_perm C2B.hl hc (allN_spec J2.sB k hk)

theorem autNot : siftA 315 nLevels nBase 0 autStrong[0]! = false := by
  rw [binds.2.2.2.2.1 0 (by norm_num)]
  unfold nLevels
  rw [siftK_eq nBinds J2.nPerm JN.hl rfl (canonK_facts J2.dCanon).2.2.1
    (range_of_canonK J2.dCanon)]
  exact J2.sD

theorem comm_of {G U : Nat} (hG : canonK 315 9 (mask 9) (315 * 9) G = true)
    (hU : canonK 315 9 (mask 9) (315 * 9) U = true) (h : commA (unpack 315 9 G) (unpack 315 9 U) = true) :
    pcomp 315 9 (mask 9) G U = pcomp 315 9 (mask 9) U G := by
  unfold commA at h
  rw [compA_unpack hG hU, compA_unpack hU hG] at h
  unfold eqA at h
  refine CFSG.KS.PF.eq_of_fields (by norm_num) (PackFld.pcomp_shr (by norm_num) (by norm_num))
    (PackFld.pcomp_shr (by norm_num) (by norm_num)) fun i hi => ?_
  have := CFSG.Monster.B.Co2.allLt_iff.1 h i hi
  rw [beq_iff_eq, unpack_getT hi, unpack_getT hi] at this
  exact this

theorem selfK_sound (G : Nat) (hG : canonK 315 9 (mask 9) (315 * 9) G = true)
    (h : J2.selfK G = true) : selfCentTest (unpack 315 9 G) = true := by
  unfold J2.selfK at h
  unfold selfCentTest
  cases hc : allN 4 (fun k => Nat.beq (pcomp 315 9 (mask 9) G (JU.S k))
      (pcomp 315 9 (mask 9) (JU.S k) G))
  · have hn : ((List.range 4).all fun i => commA (unpack 315 9 G) uStrong[i]!) = false := by
      rw [Bool.eq_false_iff]
      intro H
      rw [List.all_eq_true] at H
      have : allN 4 (fun k => Nat.beq (pcomp 315 9 (mask 9) G (JU.S k))
          (pcomp 315 9 (mask 9) (JU.S k) G)) = true := allN_of_forall fun k hk => by
        have H' := H k (List.mem_range.2 hk)
        rw [uBinds.2.2.2.2.1 k hk] at H'
        rw [comm_of hG (canonU hk) H']
        exact Nat.beq_refl _
      rw [hc] at this
      exact Bool.false_ne_true this
    rw [hn]
    rfl
  · rw [hc] at h
    unfold uLevels
    rw [sift_of uBinds J2.uPerm JU.hl hG h, Bool.or_true]

theorem centTest : all3 315 cent2ALevels selfCentTest = true :=
  all3_of_K c2A_binds c2A_perm C2A.hl (by norm_num) selfK_sound J2.sE

end CertificateChecks.Batch9308

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.J2Proof in
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.ComponentClassification.J2Cover CFSG.Sporadic.RuSchreier CFSG.ClassicalInvolution.J2Data in
theorem certificate9308 : (rawChainOK 315 (uStrong.extract 0 4) uStrong uBase uWords 4 = true ∧
      rawOrbitSizes 315 uStrong uBase = [32])
    ∧ (rawChainOK 315 (nStrong.extract 0 3) nStrong nBase nWords 4 = true ∧
      rawOrbitSizes 315 nStrong nBase = [60, 2])
    ∧ ((∀ k < 4, siftA 315 cent2ALevels cent2ABase 0 uStrong[k]! = true) ∧
      (∀ k < 2, ∀ i < 4,
        siftA 315 uLevels uBase 0 (conjA 315 cent2AStrong[k]! uStrong[i]!) = true) ∧
      all3 315 cent2ALevels selfCentTest = true)
    ∧ ((∀ k < 3, siftA 315 cent2BLevels cent2BBase 0 nStrong[k]! = true) ∧
      siftA 315 nLevels nBase 0 autStrong[0]! = false) :=
  ⟨CertificateChecks.Batch9308.uChain, CertificateChecks.Batch9308.nChain,
    ⟨CertificateChecks.Batch9308.sifts.1, CertificateChecks.Batch9308.sifts.2.1, CertificateChecks.Batch9308.centTest⟩,
    ⟨CertificateChecks.Batch9308.sifts.2.2, CertificateChecks.Batch9308.autNot⟩⟩

end Certificates
