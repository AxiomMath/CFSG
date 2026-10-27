
module

public import CFSG.Sporadic.Co1Block.TwoBTriBase

public import CFSG.Sporadic.Co1Block.TwoBCentBase1
public import CFSG.Sporadic.Co1Block.XFix
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
public import CFSG.Sporadic.Co1Block.TwoBExtraCheckInputs
public meta import CFSG.Sporadic.Co1Block.ConjBData
public meta import CFSG.Sporadic.Co1.Module.InvData
public meta import CFSG.Sporadic.Co1.Module.FormsBase1
public meta import CFSG.Sporadic.Co1.Module.OrbitsBase
public import CFSG.Sporadic.Schreier.Co1ThreeLocalInputs
public import Certificates.Data.CFSGNative.Co1.Data
public import Certificates.Certificate10070
public import CFSG.Sporadic.Co1.Module.TwoBFrameInputs

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Block

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.SmallF2 Matrix CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

end CFSG.Sporadic.Co1Block
