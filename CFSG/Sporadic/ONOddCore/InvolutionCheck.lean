module

public import CFSG.Sporadic.Schreier.ONCheckAux
public import CFSG.Sporadic.Schreier.ONCheckSmallAux
public meta import CFSG.Sporadic.Schreier.ONCheckAux
public meta import CFSG.Sporadic.Schreier.ONCheckSmallAux
public import CFSG.Sporadic.ONOddCore.InvolutionCheckInputs
public import Certificates.Certificate2119

public section

namespace CFSG.Sporadic.ONOddCore

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native

theorem inv_classes_cert :
    CFSG.PSL3Four.Native.invsOK 32 Data.T32Chain.generators
        (Data.T32Chain.generators.map (CFSG.PSL3Four.Native.invTab 32)) = true ∧
      repOrbits32.size = 7 ∧
      allBelowN 7 (fun i => CFSG.PSL3Four.Native.orbitOK 32 Data.T32Chain.generators
        (Data.T32Chain.generators.map (CFSG.PSL3Four.Native.invTab 32)) repTabs32[i]!
        repOrbits32[i]!) = true ∧
      CFSG.PSL3Four.Native.coverOK 32 t32Enum.tabs (repOrbits32.map (·.tabs)) = true :=
  Certificates.certificate2119.1

theorem inv_fusion_cert :
    fusionCheck (wordArrs Data.TWords) (wordArrs Data.MWords ++ #[cArr])
      (pinvs nPts (wordArrs Data.MWords ++ #[cArr])) zArr = true :=
  Certificates.certificate2119.2

end CFSG.Sporadic.ONOddCore
