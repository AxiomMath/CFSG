
module

public import Certificates.Kernel.Co1B.C2045Base

public import CFSG.Sporadic.Co1Block.TwoBCheckInputs
public meta import CFSG.Sporadic.Co1Block.TwoBData
public meta import CFSG.Sporadic.Co1Block.TwoBCheckDefs
public meta import CFSG.Sporadic.Co1Block.CentCheck
public meta import CFSG.Sporadic.Schreier.TitsBasic
public meta import CFSG.Sporadic.Co2Schreier.ThirdCheck
public meta import CFSG.Sporadic.Schreier.Co1ChainCheck
public meta import CFSG.Sporadic.Schreier.Co1ThreeLocal
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import Certificates.Data.CFSGNative.Co1.Data
public meta import Certificates.Data.CFSGNative.Co1.Involutions
public meta import Certificates.Data.CFSGNative.Co1.TwoB
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.Schreier.Merge
public meta import Certificates.Data.CFSGNative.ONSchreier.Compact
public import Certificates.Kernel.Co1B.Cent2045
public import Certificates.Kernel.Co1B.Tri2045
public import Certificates.Kernel.Co1B.Prim2045

public section

namespace CertificateChecks.KernelCo1B

open CFSG CFSG.Sporadic CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Schreier.Native in
open CFSG.Sporadic.SmallF2.Native CFSG.Monster.B.Co2.Native CFSG.Certificates.Native in
open CFSG.ONSchreier.Native CFSG.Sporadic.Co1Block.Native in
theorem c2045 :
 (centCheckOf aR twoBD1 twoBBray twoBD2 twoBVBase twoBVGens
      twoBVSizes = true
    )
    ∧ (twoBTriCheckOf twoBTris twoBStrong
      (brayElts (brayRows aR twoBD1) twoBBray) twoBXYRows.1 twoBXYRows.2 twoBChainBase.toArray
      (CFSG.Sporadic.Schreier.Tits.wordsArr 2 6 twoBChainWords) = true
    )
    ∧ (twoBPrimCheckOf twoBStrong twoBHSteps twoBHTrees twoBSubReps = true) :=
  ⟨Cent2045.twoB_cent_check, Tri2045.twoB_tri_check, Prim2045.twoB_prim_check⟩

end CertificateChecks.KernelCo1B

end
