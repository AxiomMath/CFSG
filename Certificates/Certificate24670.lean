module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.FrameJPt
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.FrameJHom
import Certificates.Kernel.Fi23Frame.Sound

public section

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.TwoFi22.FrameJ CFSG.EvenSporadicStandard.Wong77.Module in
theorem certificate24670 : 
    (∀ i j : Fin 23, fjPt i * fjPt j = fjPt j * fjPt i) ∧
    (∀ i j k : Fin 23, i ≠ j → k ≠ i → k ≠ j → fjPt i * fjPt j ≠ fjPt k) ∧
    ∀ r : Fin 12, ((CFSG.EvenSporadicStandard.TwoFi22.FrameJ.rowList (golayMask r)).map fjPt).prod = 1 :=
  by
    exact KernelFi23Frame.frame_facts

end Certificates

end

end
