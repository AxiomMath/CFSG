module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.I22Four
import Certificates.Kernel.EvenSporM22.I22FourChecks
import CFSG.Certificates.Kernel.EvenSporM22.I22FourSound
import CFSG.Certificates.Kernel.LocalQTCovSound

public section

namespace Certificates

open CFSG.KD.I22F CFSG.KD.LQT.C4101 CFSG.KC.LQT.Cov CFSG.KC.LQT.W CFSG.Sporadic.Mathieu
  CFSG.QuasithinUnique.Ch1.M22Cover CFSG.EvenSporadicStandard.M22Std

theorem certificate7286 : CFSG.EvenSporadicStandard.M22Std.i22fCheck () = true := by
  have hA : codeP m22gA = 228952723507329932679484465855724 := by decide +kernel
  have hB : codeP m22gB = 81506110577382089737470578414133 := by decide +kernel
  have hct : covData = parseData (String.ofList CT.chars) := by
    rw [← CT.eq]
    rfl
  have hT := CFSG.KC.I22F.i22fCheckT_of hA hB hct kDigA kDigB kTabA kTabB kPermA kPermB kR0 kR1 kR2
    kR3 kR4 kR5 kZA kZB kCwA kCwB kWits kCnt
  rw [← CA.eq, ← CB.eq] at hT
  have hC := cov_sound CT.chars H 128 [189] hA hB kC
  rw [← CT.eq] at hC
  obtain ⟨hcov, hnV, -⟩ := hC
  unfold covCheck at hcov
  simp only [Bool.and_eq_true] at hcov
  unfold i22fCheck
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨hnV, hcov.1.1.1⟩, hT⟩

end Certificates
