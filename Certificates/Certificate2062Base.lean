
module

public import CFSG.Assembly.Defs
public import CFSG.Sporadic.Co2Cert.Text5
public import CFSG.Sporadic.Co2Schreier.LocalLit
public import CFSG.Sporadic.Schreier.RuBlocks
public import Certificates.Certificate2256Base
public import Certificates.Data.CFSGNative.HS.SmallF2

@[expose] public section

open CFSG CFSG.Sporadic CFSG.Sporadic.Co2Schreier CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Mathieu CFSG.Sporadic.Co2Cert
open CFSG.Sporadic.RuSchreier CFSG.Sporadic.SmallF2.Native

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace Certificates

open CFSG.Sporadic.Co2Schreier

end Certificates
