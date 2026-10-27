module

public import CFSG.RankThree.Native.Co3FiveArrays
public import CFSG.RankThree.Native.ChainCentralizer
public import CFSG.Sporadic.Schreier.Co3OrderCheck
public import CFSG.Monster.B.Mathieu.SylowCore
public meta import CFSG.RankThree.Native.Co3FiveArrays
public meta import CFSG.RankThree.Native.ChainCentralizer
public meta import CFSG.Sporadic.Schreier.Co3OrderCheck
public meta import CFSG.Monster.B.Mathieu.SylowCore
public import CFSG.RankThree.Native.Co3FiveCheckInputs
public import Certificates.Certificate8122

public section

namespace CFSG.RankThree.Native

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Schreier.Co3
  CFSG.Monster.B.Mathieu CFSG.Monster.B.Fischer

theorem co3Five_chain_check :
    co3FiveChainCheck (rawLevels 276 co3ChainArrs co3ChainBaseArr) co3FiveC25Cert = true :=
  Certificates.certificate8122.1

theorem co3Five_Q_check :
    co3FiveQCheck co3FiveQCert co3FiveLines = true :=
  Certificates.certificate8122.2.1

theorem co3Five_C25_check :
    co3FiveC25Check co3FiveC25Cert co3FiveQCert = true :=
  Certificates.certificate8122.2.2.1

theorem co3Five_C0_check :
    co3FiveC0Check co3FiveC0GenArrs co3FiveDGenArrs co3FiveC0Cert co3FiveDCert = true :=
  Certificates.certificate8122.2.2.2

end CFSG.RankThree.Native
