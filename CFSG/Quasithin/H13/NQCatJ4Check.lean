module

public import CFSG.Quasithin.H13.NQCatJ4Native
public meta import CFSG.Quasithin.H13.NQCatJ4Native
public import Certificates.Certificate7020

public section

namespace CFSG.Quasithin.H13.NQCat

open CFSG.Quasithin.H13.NQCat.Native CFSG.SectionRank.Native CFSG.Sporadic.SmallF2.Native

theorem j4H_pow :
    (ops2 112).eq ((ops2 112).pow j4H 40) (ops2 112).one = true :=
  Certificates.certificate7020.1

theorem j4H_conjX :
    (ops2 112).conjOK j4H j4X (j4Word 0 7 1) = true :=
  Certificates.certificate7020.2.1

theorem j4H_conjY :
    (ops2 112).conjOK j4H j4Y (j4Word 6 9 6) = true :=
  Certificates.certificate7020.2.2.1

theorem j4_fix_noncentral : j4FixNoncentralOK = true :=
  Certificates.certificate7020.2.2.2.2.1

theorem j4_fix_central : j4FixCentralOK = true :=
  Certificates.certificate7020.2.2.2.2.2.1

theorem j4_pow_xy : j4PowXYOK = true :=
  Certificates.certificate7020.2.2.2.2.2.2

end CFSG.Quasithin.H13.NQCat
