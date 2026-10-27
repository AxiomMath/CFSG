module

public import CFSG.Sporadic.ONOddCore.InvolutionCheckInputs
public meta import CFSG.Sporadic.Schreier.ONCheckAux
public meta import CFSG.Sporadic.Schreier.ONCheckSmallAux
import Certificates.Kernel.Sporadic.OddCore.ON2119AF
import Certificates.Kernel.Sporadic.OddCore.ON2119B
import Certificates.Certificate2212
import Certificates.Certificate2217
import Certificates.Certificate3171

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.ONOddCore CFSG.ONSchreier CFSG.ONSchreier.Native in
open CFSG.Sporadic.ON.Native in
theorem certificate2119 : (CFSG.PSL3Four.Native.invsOK 32 Data.T32Chain.generators
        (Data.T32Chain.generators.map (CFSG.PSL3Four.Native.invTab 32)) = true ∧
      repOrbits32.size = 7 ∧
      allBelowN 7 (fun i => CFSG.PSL3Four.Native.orbitOK 32 Data.T32Chain.generators
        (Data.T32Chain.generators.map (CFSG.PSL3Four.Native.invTab 32)) repTabs32[i]!
        repOrbits32[i]!) = true ∧
      CFSG.PSL3Four.Native.coverOK 32 t32Enum.tabs (repOrbits32.map (·.tabs)) = true
    )
    ∧ (fusionCheck (wordArrs Data.TWords) (wordArrs Data.MWords ++ #[cArr])
      (pinvs nPts (wordArrs Data.MWords ++ #[cArr])) zArr = true
    ) :=
  ⟨KernelSpor.ON2119.classes2119, KernelSpor.ON2119.fusion2119⟩

end Certificates
