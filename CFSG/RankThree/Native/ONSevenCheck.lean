module

public import CFSG.RankThree.Native.ONSevenArrays
public meta import CFSG.RankThree.Native.ONSevenArrays
public import Certificates.Certificate8133
public meta import CFSG.Certificates.NativeSchreierCard
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.Sporadic.Schreier.ONCheckChain
public meta import CFSG.Sporadic.Schreier.ONCheckChain
public meta import Mathlib.GroupTheory.Schreier
public import Mathlib.GroupTheory.Schreier

public section

namespace CFSG.RankThree.Native

theorem onSeven_Q_check :
    onSevenQCheck onSevenQR onSevenQTabs onSevenLineTabs onSevenQCert = true :=
  Certificates.certificate8133.1

theorem onSeven_C_check_0 :
    onSevenCCheck (onSevenCR 0) (onSevenRepArr 0) (onSevenCArrs 0)
    (onSevenCTabs 0) (onSevenCCert 0) 1372 = true :=
  Certificates.certificate8133.2.1

theorem onSeven_C_check_1 :
    onSevenCCheck (onSevenCR 1) (onSevenRepArr 1) (onSevenCArrs 1)
    (onSevenCTabs 1) (onSevenCCert 1) 1372 = true :=
  Certificates.certificate8133.2.2.1

theorem onSeven_C_check_2 :
    onSevenCCheck (onSevenCR 2) (onSevenRepArr 2) (onSevenCArrs 2)
    (onSevenCTabs 2) (onSevenCCert 2) 1372 = true :=
  Certificates.certificate8133.2.2.2.1

theorem onSeven_C_check_3 :
    onSevenCCheck (onSevenCR 3) (onSevenRepArr 3) (onSevenCArrs 3)
    (onSevenCTabs 3) (onSevenCCert 3) 49 = true :=
  Certificates.certificate8133.2.2.2.2.1

theorem onSeven_C_check_4 :
    onSevenCCheck (onSevenCR 4) (onSevenRepArr 4) (onSevenCArrs 4)
    (onSevenCTabs 4) (onSevenCCert 4) 49 = true :=
  Certificates.certificate8133.2.2.2.2.2.1

theorem onSeven_F_check_0 :
    onSevenFCheck (onSevenCR 0) (onSevenCTabs 0) (onSevenCCert 0)
    (onSevenFArrs 0) (onSevenFTabs 0) (onSevenRepTab 0) (onSevenFCert 0) = true :=
  Certificates.certificate8133.2.2.2.2.2.2.1

theorem onSeven_F_check_1 :
    onSevenFCheck (onSevenCR 1) (onSevenCTabs 1) (onSevenCCert 1)
    (onSevenFArrs 1) (onSevenFTabs 1) (onSevenRepTab 1) (onSevenFCert 1) = true :=
  Certificates.certificate8133.2.2.2.2.2.2.2.1

theorem onSeven_F_check_2 :
    onSevenFCheck (onSevenCR 2) (onSevenCTabs 2) (onSevenCCert 2)
    (onSevenFArrs 2) (onSevenFTabs 2) (onSevenRepTab 2) (onSevenFCert 2) = true :=
  Certificates.certificate8133.2.2.2.2.2.2.2.2

end CFSG.RankThree.Native
