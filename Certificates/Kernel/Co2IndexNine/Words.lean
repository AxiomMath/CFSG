module

public import Certificates.Kernel.SporSch.Co2M.EnumQ
public import CFSG.Certificates.Kernel.SporSch.MatInj
public import CFSG.Sporadic.Co2Schreier.IndexNineInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.Co2I301.SpecSixAux

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2IndexNine

open CFSG.KS.Co2M CFSG.KS.MatRep CFSG.KS.MatInj CFSG.RankThree.Native.F2
open CFSG.Sporadic.Co2Schreier CFSG.Sporadic.Co2Cert CFSG.Monster.B.Co2.Native
open CertificateChecks.KernelSporSch.Co2M

@[expose] noncomputable def cP : List (ℕ × ℕ) := [(QC 0, QC 2), (QC 1, QC 3)]

@[expose] noncomputable def wM (w : List ℤ) : ℕ := (wordP mmK I22 cP w).1

theorem cP_rep : RepT 22 co2PackedVecs cArrs cP := by
  refine ⟨by rw [cRep.1, c_len'']; rfl, fun k hk => ?_⟩
  have hk2 : k < 2 := hk
  interval_cases k
  · exact qcrep 0 (by norm_num)
  · exact qcrep 1 (by norm_num)

theorem word_rep {w : List ℤ} (hw : lettersOK 2 w = true) :
    Rep 22 co2PackedVecs (wordArr cArrs w) (wM w) (wordP mmK I22 cP w).2 :=
  rep_wordArr good V_size mmK_eq I22_eq cP_rep hw

theorem eqA_words {w₁ w₂ : List ℤ} (h₁ : lettersOK 2 w₁ = true) (h₂ : lettersOK 2 w₂ = true) :
    eqA 2300 (wordArr cArrs w₁) (wordArr cArrs w₂) =
      Nat.beq (wM w₁ % 2 ^ (22 * 22)) (wM w₂ % 2 ^ (22 * 22)) := by
  have r₁ := word_rep h₁
  have r₂ := word_rep h₂
  rw [r₁.1, r₂.1, ← V_size]
  exact eqA_permOfMat_mod spans r₁.2.1 r₂.2.1

theorem eqA_word_id {w : List ℤ} (h : lettersOK 2 w = true) :
    eqA 2300 (wordArr cArrs w) (idA 2300) =
      Nat.beq (wM w % 2 ^ (22 * 22)) (I22 % 2 ^ (22 * 22)) := by
  have r := word_rep h
  have ri := rep_idA good
  rw [← I22_eq] at ri
  rw [r.1, ← V_size, ri.1]
  exact eqA_permOfMat_mod spans r.2.1 ri.2.1

theorem letters : lettersOK 2 nineXSig = true ∧ lettersOK 2 nineYSig = true ∧
    lettersOK 2 nineX2Sig = true ∧ lettersOK 2 nineX3Sig = true ∧ lettersOK 2 nineY3Sig = true ∧
    lettersOK 2 nineXYSig = true ∧ lettersOK 2 nineYXSig = true := by
  decide +kernel

theorem check : co2IndexNineWordCheck () = true := by
  obtain ⟨hx, hy, hx2, hx3, hy3, hxy, hyx⟩ := letters
  unfold co2IndexNineWordCheck co2IdxNineX3Check co2IdxNineY3Check co2IdxNineCommCheck
    co2IdxNineXNeCheck co2IdxNineYNeCheck co2IdxNineYXCheck co2IdxNineYX2Check
  rw [eqA_word_id hx3, eqA_word_id hy3, eqA_words hxy hyx, eqA_word_id hx, eqA_word_id hy,
    eqA_words hy hx, eqA_words hy hx2]
  decide +kernel

end CertificateChecks.KernelCo2IndexNine

end
