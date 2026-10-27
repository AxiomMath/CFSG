module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.I22Check
import Certificates.Kernel.EvenSporM22.M22StdI22Checks
import CFSG.Certificates.Kernel.EvenSporM22.M22StdSound
import CFSG.Certificates.Kernel.LocalQTWordSound

public section

namespace Certificates

open CFSG.KD.LQT.C4101 CFSG.KD.M22S CFSG.KC.M22S CFSG.KC.LQT.W CFSG.Sporadic.Mathieu

theorem certificate7285 : CFSG.EvenSporadicStandard.M22Std.i22Check () = true := by
  have hA : codeP m22gA = 228952723507329932679484465855724 := by decide +kernel
  have hB : codeP m22gB = 81506110577382089737470578414133 := by decide +kernel
  have hcs : CFSG.QuasithinUnique.Ch1.M22Cover.covData =
      CFSG.QuasithinUnique.Ch1.M22Cover.parseData (String.ofList CT.chars) := by
    rw [← CT.eq]
    rfl
  exact i22K_sound hA hB hcs kI22

end Certificates
