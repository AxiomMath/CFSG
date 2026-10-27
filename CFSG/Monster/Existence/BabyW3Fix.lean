module

public import CFSG.Monster.Existence.ELevelBits
public meta import CFSG.Monster.Existence.ELevelBits
public meta import CFSG.Monster.B.TwoA.Census.CosetEnumBits
public meta import CFSG.Monster.B.TwoA.Census.CosetEnumCheck
public meta import CFSG.Monster.B.TwoA.Census.NatCert
public meta import CFSG.Monster.B.TwoA.Census.CosetCertData
public meta import CFSG.Monster.B.TwoA.Census.MonoCert
public meta import CFSG.Monster.B.Rep4371.GlueDefs
public meta import Certificates.Data.CFSGNative.MonsterB.CosetEnum
public import Certificates.Certificate6020
public meta import CFSG.Monster.B.TwoA.Base.Flags
public import CFSG.Monster.B.TwoA.Base.Flags
public meta import CFSG.Monster.B.TwoA.Base.Par45A
public import CFSG.Monster.B.TwoA.Base.Par45A
public import CFSG.Monster.B.TwoA.Par3.Main
public meta import CFSG.Monster.B.TwoA.Par3.Main
public meta import CFSG.Monster.B.TwoA.Par3.MainBase
public import CFSG.Monster.B.TwoA.Par3.MainBase
public import CFSG.Monster.B.TwoA.Unitary.Semilinear
public meta import CFSG.Monster.B.TwoA.Unitary.Semilinear
public meta import CFSG.Open.MonsterY443Defs
public import CFSG.Open.MonsterY443Defs
public import CFSG.Sporadic.Co1Base
public meta import CFSG.Sporadic.Co1Base
public import CFSG.Sporadic.Th.F2Spec
public meta import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.Monster.Existence

open CFSG.Monster.B.TwoA.Census

theorem fix_count_kap_one :
    ((Finset.range (2 ^ 24)).filter fun x => kapX (tT 1) (tD 1) x = x).card = 2 ^ 16 :=
  Certificates.certificate6020

end CFSG.Monster.Existence
