module

public import Certificates.Kernel.Co2Smith.ChainJcK
public import CFSG.Certificates.Kernel.Spor.RawSound
public import CFSG.Certificates.Kernel.Spor.RawOrbHead
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.Co2Smith.Native CFSG.Certificates.Native

theorem chainJc_ok : glNJChainOK = true := by
  have h := jcBind_k
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hs, hS⟩, h0⟩, h1⟩, hW⟩ := h
  have hget : ∀ k < 8, glNJChS[k]! = unpack 77 7 (CJc.S k) := fun k hk => by
    rw [← toArray_eq_of_bindListK (allN_spec hS k hk), Array.toArray_toList]
  have hb : Binds 77 7 CJc.S 8 7 CJc.BP glNJChS glNJChBase.toArray :=
    ⟨by norm_num, by norm_num, by norm_num, hs, hget, by decide, by decide +kernel⟩
  have hp : allN 8 (fun j => permOK 77 7 (mask 7) (77 * 7) (CJc.S j) (CJc.SI j)) = true := by
    have h := CJc.head
    unfold headK at h
    simp only [Orb.bAnd_eq, Bool.and_eq_true] at h
    exact h.2.2.2.2.1
  have hc := rawChainK_sound (chunks := 4) hb CJc.head CJc.hl (by norm_num) CJc.hs
  have hWe : glNJChW = CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 8 chJcD := by decide +kernel
  have e0 : glNJChS[0]! = glNJPerm[0]! := by
    rw [hget 0 (by decide), ← toArray_eq_of_bindListK h0, Array.toArray_toList]
  have e1 : glNJChS[1]! = glNJPerm[1]! := by
    rw [hget 1 (by decide), ← toArray_eq_of_bindListK h1, Array.toArray_toList]
  unfold glNJChainOK
  rw [hs, e0, e1, beq_self_eq_true, beq_self_eq_true, hWe, hc, rawOrbitSizesK_sound hb hp CJc.hl]
  decide +kernel

end CertificateChecks.KernelCo2Smith
