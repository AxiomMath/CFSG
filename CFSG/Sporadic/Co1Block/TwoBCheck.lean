
module

public import CFSG.Sporadic.Co1Block.TwoBCheckBase

public import CFSG.Sporadic.Co1Block.TwoBData
public import CFSG.Sporadic.Co1Block.TwoBCheckDefs
public import CFSG.Sporadic.Schreier.TitsBasic
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
public import CFSG.Sporadic.Co1Block.TwoBCheckInputs
public import Certificates.Certificate2045

public section

namespace CFSG.Sporadic.Co1Block

open CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.SmallF2.Native CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native CFSG.ONSchreier.Native CFSG.Sporadic.Co1Block.Native

theorem twoB_cent_check : centCheckOf aR twoBD1 twoBBray twoBD2 twoBVBase twoBVGens
    twoBVSizes = true :=
  Certificates.certificate2045.1

theorem twoB_tri_check : twoBTriCheckOf twoBTris twoBStrong
    (brayElts (brayRows aR twoBD1) twoBBray) twoBXYRows.1 twoBXYRows.2 twoBChainBase.toArray
    (CFSG.Sporadic.Schreier.Tits.wordsArr 2 6 twoBChainWords) = true :=
  Certificates.certificate2045.2.1

theorem twoB_prim_check : twoBPrimCheckOf twoBStrong twoBHSteps twoBHTrees twoBSubReps = true :=
  Certificates.certificate2045.2.2

end CFSG.Sporadic.Co1Block
