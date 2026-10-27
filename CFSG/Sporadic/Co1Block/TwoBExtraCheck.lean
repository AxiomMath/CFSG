
module

public import CFSG.Sporadic.Co1Block.TwoBExtraCheckBase

public import CFSG.Sporadic.Co1Block.ConjBData
public import CFSG.Sporadic.Co1Block.TwoBCheckBase
public import CFSG.Sporadic.Co1.Module.InvData
public meta import CFSG.Sporadic.Co1Block.ConjBData
public meta import CFSG.Sporadic.Co1Block.TwoBData
public meta import CFSG.Sporadic.Co1Block.TwoBCheckDefs
public meta import CFSG.Sporadic.Co1.Module.InvData
public meta import CFSG.Sporadic.Co1.Module.FormsBase1
public meta import CFSG.Sporadic.Co1.Module.OrbitsBase
public meta import CFSG.Sporadic.Schreier.Co1ThreeLocal
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import Certificates.Data.CFSGNative.Co1.Data
public meta import Certificates.Data.CFSGNative.Co1.Involutions
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import CFSG.Sporadic.Co1Block.TwoBExtraCheckInputs
public import Certificates.Certificate2046

public section

namespace CFSG.Sporadic.Co1Block

open CFSG.Sporadic.Co1Schreier.Native CFSG.Monster.B.Co2.Native

theorem conjB_check : conjBCheckOf [aR, bR] conjBDerivs CFSG.Sporadic.Co1.Module.rowsSB = true :=
  Certificates.certificate2046.1

theorem twoB_tab_check : tabSoundOf (Native.triTable twoBTris) twoBTris.toArray = true :=
  Certificates.certificate2046.2

end CFSG.Sporadic.Co1Block
