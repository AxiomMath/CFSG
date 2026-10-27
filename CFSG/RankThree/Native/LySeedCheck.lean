
module

public import CFSG.RankThree.Native.LySeedCheckBase

public import CFSG.RankThree.Native.LyOperatorData
public meta import Certificates.Data.CFSGNative.Ly.Certificate
public import CFSG.RankThree.Native.LySeedCheckInputs
public import Certificates.Certificate8132

public section

namespace CFSG.RankThree.Native

open CFSG.Sporadic.He.Native CFSG.Sporadic.Ly.Native

theorem ly_seed_check : lySeedChecks = true :=
  Certificates.certificate8132

end CFSG.RankThree.Native
