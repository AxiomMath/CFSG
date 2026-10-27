module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HNSideFacts.F4Inputs
import Certificates.Kernel.SchreierFam.C26777K
import Certificates.Kernel.Sporadic.OddCore.HN2089
import CFSG.Sporadic.Schreier.ONPermArr
import CFSG.Certificates.Kernel.BfsPinUnpack
import CFSG.Certificates.Kernel.Common.Harness
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import all Init.Data.Array.Basic
import all Certificates.Data.CFSGNative.MonsterB.Co2Chain
import all Certificates.Data.CFSGNative.Schreier.Check

set_option maxRecDepth 400000
set_option maxHeartbeats 0

namespace CertificateChecks.Batch26777

open CFSG.EvenSporadicStandard.HNRecog.SideF4 CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw
  CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore CFSG.Sporadic.HNOddCore.Native
  CFSG.Monster.B.Co2.Native CertificateChecks.KernelSpor CertificateChecks.KernelSpor.HN2089
  CertificateChecks.KernelSchreierFam.F4Side CFSG.KC.BfsPin

theorem q_words : (allBelowN 8 fun i => plettersOK 10 qWordsJ[i]! &&
    peq 800 (pword 800 s800 (pinvs 800 s800) qWordsJ[i]!) InvData.qPerms[i]!) = true := by
  rw [allBelowN_iff]
  intro i hi
  rw [Bool.and_eq_true]
  have hw := wordEqK_sound (r := HQQ i) s_get pS (allN_spec wqJ i hi)
  have hl : ∀ i < 8, plettersOK 10 qWordsJ[i]! = true := by decide +kernel
  refine ⟨hl i hi, ?_⟩
  have hc := allN_spec cQ i hi
  rw [peq_eq, pword_eq_wordA, pinvs_eq_rawInvs, s800, hw.1, q_get.2 i hi, eqA_unpack hc hc]
  exact Nat.beq_refl _

theorem e_words : (allBelowN 5 fun i => plettersOK 9 eWords[i]! && decide (eMasks[i]! < 256) &&
    peq 800 (pword 800 s800 (pinvs 800 s800) eWords[i]!)
      (qbList 800 InvData.qPerms)[eMasks[i]!]!) = true := by
  rw [allBelowN_iff]
  intro i hi
  have hm : ∀ i < 5, plettersOK 9 eWords[i]! = true ∧ eMasks[i]! < 256 := by decide +kernel
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨(hm i hi).1, (hm i hi).2⟩, ?_⟩
  have hw := wordEqK_sound (r := HQB eMasks[i]!) s_get pS (allN_spec weE.1 i hi)
  have hc := allN_spec cB _ (hm i hi).2
  rw [peq_eq, pword_eq_wordA, pinvs_eq_rawInvs, s800, hw.1, b_get.2 _ (hm i hi).2,
    eqA_unpack hc hc]
  exact Nat.beq_refl _

theorem b_word : peq 800 (pword 800 s800 (pinvs 800 s800) bWord)
    (qbList 800 InvData.qPerms)[bMask]! = true := by
  have hw := wordEqK_sound (r := HQB bMask) s_get pS weE.2
  have hb : bMask < 256 := by decide
  have hc := allN_spec cB _ hb
  rw [peq_eq, pword_eq_wordA, pinvs_eq_rawInvs, s800, hw.1, b_get.2 _ hb, eqA_unpack hc hc]
  exact Nat.beq_refl _

theorem q_ok : sideF4QOK = true := by
  unfold sideF4QOK
  dsimp only
  rw [q_words, q_get.1, show s800.size = 11 from s_get.1]
  decide +kernel

theorem plus_ok : sideF4PlusOK = true := by
  unfold sideF4PlusOK
  dsimp only
  rw [e_words, b_word]
  decide +kernel

theorem class_ok : sideF4ClassOK = true := by decide +kernel

theorem fam_ok : sideF4FamOK = true := by decide +kernel

end CertificateChecks.Batch26777

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.HNRecog.SideF4 in
theorem certificate26777 : sideF4QOK = true ∧ sideF4PlusOK = true ∧ sideF4ClassOK = true ∧ sideF4FamOK = true :=
  ⟨CertificateChecks.Batch26777.q_ok, CertificateChecks.Batch26777.plus_ok, CertificateChecks.Batch26777.class_ok, CertificateChecks.Batch26777.fam_ok⟩

end Certificates
