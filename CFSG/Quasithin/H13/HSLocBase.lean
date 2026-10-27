
module

public import CFSG.Quasithin.H13.HSLocBaseBase

public import Certificates.Certificate589206

public section

namespace CFSG.Quasithin.H13.LocDbl.HSLoc

open CFSG.QuasithinUnique.K1.SporadicPerm hiding img keyNat
open CFSG.Quasithin.H13.LocDbl.DcNative CFSG.Quasithin.H13.LocDbl.DcRank CFSG.Quasithin.H13.LocDbl.Dc
open CFSG.RankThree.Native

theorem mSpec :
    SubSpec Mg mElems 11520 :=
  subSpec_words mWords_lt Certificates.certificate589206.1

end CFSG.Quasithin.H13.LocDbl.HSLoc
