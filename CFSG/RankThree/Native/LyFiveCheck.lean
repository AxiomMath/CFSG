module

public import CFSG.RankThree.Native.LyFiveArrays
public import CFSG.RankThree.Native.LySeedCheck
public meta import Certificates.Data.CFSGNative.Ly.Certificate
public meta import CFSG.Monster.B.Fischer.InducedData
public meta import CFSG.RankThree.Native.LyFiveArrays
public meta import CFSG.RankThree.Native.LyFiveData
public meta import CFSG.RankThree.Native.LySeedCheck
public import CFSG.RankThree.Native.LyFiveCheckInputs
public import Certificates.Certificate8130

public section

namespace CFSG.RankThree.Native

open CFSG.Sporadic.He.Native CFSG.Sporadic.Ly.Native CFSG.Monster.B.Fischer

theorem ly_five_small_check : lyFiveSmallCheck = true :=
  Certificates.certificate8130.1

theorem ly_five_tree_check : lyFiveTreeCheck = true :=
  Certificates.certificate8130.2.1

theorem ly_five_rels_check : lyFiveRelsCheck = true :=
  Certificates.certificate8130.2.2

end CFSG.RankThree.Native
