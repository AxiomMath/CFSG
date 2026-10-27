module

public import CFSG.Monster.Existence.EbCheck
public meta import CFSG.Monster.Existence.EbCheck
public meta import CFSG.Monster.Existence.ELevelBits
public meta import CFSG.Monster.Existence.ELevelConv
public meta import CFSG.Monster.Existence.ELevelCheck
public meta import CFSG.Monster.VisCert.Basis
public meta import CFSG.Monster.B.TwoA.Census.CosetEnumBits
public meta import CFSG.Monster.B.TwoA.Census.CosetEnumCheck
public meta import CFSG.Monster.B.TwoA.Census.NatCert
public meta import CFSG.Monster.B.TwoA.Census.CosetCertData
public meta import CFSG.Monster.B.TwoA.Census.MonoCert
public meta import CFSG.Monster.B.Rep4371.GlueDefs
public meta import Certificates.Data.CFSGNative.MonsterB.CosetEnum
public meta import Certificates.Data.CFSGNative.MonsterB.Short
public meta import Certificates.Data.CFSGNative.MonsterVis.Frame
public import Certificates.Certificate6026
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

theorem case1OK_eq_true : case1OK = true :=
  Certificates.certificate6026.1

theorem class0OK_eq_true : class0OK = true :=
  Certificates.certificate6026.2.1

theorem witness_packed_shortness :
    isShortX (packP (false, 3, 60)) = true ∧ isShortX (packP (false, 60, 60)) = false ∧
      isShortX (packP (false, 3, 48)) = false ∧ isShortX (packP (false, 734, 0)) = false :=
  Certificates.certificate6026.2.2

end CFSG.Monster.Existence
