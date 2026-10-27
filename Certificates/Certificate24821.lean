module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.Cov8
import Certificates.Kernel.EvenSporM22.M22StdTwChecks
import CFSG.Certificates.Kernel.EvenSporM22.M22StdSound
import CFSG.Certificates.Kernel.LocalQTWordSound

public section

namespace Certificates

open CFSG.KD.LQT.C4101 CFSG.KD.M22S CFSG.KC.M22S CFSG.KC.LQT.W CFSG.Sporadic.Mathieu

theorem certificate24821 : CFSG.EvenSporadicStandard.M22Std.twCheck CFSG.QuasithinUnique.Ch1.M22Cover.covData = true := by
  have hA : codeP m22gA = 228952723507329932679484465855724 := by decide +kernel
  have hB : codeP m22gB = 81506110577382089737470578414133 := by decide +kernel
  have h := twHK_sound hA hB kTw
  rw [← CT.eq] at h
  exact h

end Certificates
