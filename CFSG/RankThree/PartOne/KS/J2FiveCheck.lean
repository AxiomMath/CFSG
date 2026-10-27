module

public import CFSG.RankThree.PartOne.KS.J2FiveData
public import CFSG.RankThree.PartOne.KS.OrbitCert
public import CFSG.RankThree.Native.PermEnumeration
public import CFSG.RankThree.Native.ChainCentralizer
public import CFSG.Sporadic.SmallOddCore.J2Data
public import CFSG.Sporadic.Schreier.PairJ2Check
public import CFSG.Monster.B.Mathieu.SylowCore
public import CFSG.RankThree.PartOne.KS.J2FiveCheckInputs
public import Certificates.Certificate10056
public meta import CFSG.RankThree.PartOne.KS.J2FiveData
public meta import CFSG.RankThree.Native.PermEnumeration
public meta import CFSG.RankThree.Native.ChainCentralizer
public meta import CFSG.Sporadic.SmallOddCore.J2Data
public meta import CFSG.Sporadic.Schreier.PairJ2Check
public meta import CFSG.Monster.B.Mathieu.SylowCore
public meta import CFSG.Certificates.NativeSchreierCard
public import CFSG.RankThree.PartOne.KS.PKitLines

public section

namespace CFSG.RankThree.PartOne

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.SmallOddCore
  CFSG.Monster.B.Mathieu CFSG.Sporadic.SmallOddCore.Native

theorem j2Five_gensR_valid :
    (List.range 3).all (fun k => validA 315 j2FiveGensR[k]!) = true :=
  Certificates.certificate10056.1

theorem j2Five_Q_check : j2FiveQCheck j2FiveQCert = true :=
  Certificates.certificate10056.2.1

theorem j2Five_cent_check_0 : j2FiveCentCheck 0 50 = true :=
  Certificates.certificate10056.2.2.1

theorem j2Five_cent_check_1 : j2FiveCentCheck 1 50 = true :=
  Certificates.certificate10056.2.2.2.1

theorem j2Five_cent_check_2 : j2FiveCentCheck 2 300 = true :=
  Certificates.certificate10056.2.2.2.2.1

theorem j2Five_cent_check_3 : j2FiveCentCheck 3 300 = true :=
  Certificates.certificate10056.2.2.2.2.2.1

theorem j2Five_cent_check_4 : j2FiveCentCheck 4 50 = true :=
  Certificates.certificate10056.2.2.2.2.2.2.1

theorem j2Five_cent_check_5 : j2FiveCentCheck 5 300 = true :=
  Certificates.certificate10056.2.2.2.2.2.2.2.1

theorem j2Five_good_check_0 :
    j2FiveGoodCheck 0 (j2FiveCCert 0) j2FiveQCert = true :=
  Certificates.certificate10056.2.2.2.2.2.2.2.2.1

theorem j2Five_good_check_1 :
    j2FiveGoodCheck 1 (j2FiveCCert 1) j2FiveQCert = true :=
  Certificates.certificate10056.2.2.2.2.2.2.2.2.2.1

theorem j2Five_good_check_4 :
    j2FiveGoodCheck 4 (j2FiveCCert 4) j2FiveQCert = true :=
  Certificates.certificate10056.2.2.2.2.2.2.2.2.2.2.1

theorem j2Five_bad_check_2 :
    j2FiveBadCheck 2 (j2FiveCCert 2) (j2FiveDCert 2) j2FiveQCert = true :=
  Certificates.certificate10056.2.2.2.2.2.2.2.2.2.2.2.1

theorem j2Five_bad_check_3 :
    j2FiveBadCheck 3 (j2FiveCCert 3) (j2FiveDCert 3) j2FiveQCert = true :=
  Certificates.certificate10056.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem j2Five_bad_check_5 :
    j2FiveBadCheck 5 (j2FiveCCert 5) (j2FiveDCert 5) j2FiveQCert = true :=
  Certificates.certificate10056.2.2.2.2.2.2.2.2.2.2.2.2.2

end CFSG.RankThree.PartOne
