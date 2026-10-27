
module


public import CFSG.Assembly.Defs
public import CFSG.Sporadic.Co2Cert.Text5
public import CFSG.Sporadic.Co2Schreier.WitText
public import CFSG.Sporadic.Schreier.RuBlocks
public import Certificates.Certificate2256Base
public import Certificates.Data.CFSGNative.HS.SmallF2

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG CFSG.Sporadic CFSG.Sporadic.Co2Schreier CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Mathieu CFSG.Sporadic.Co2Cert
open CFSG.Sporadic.RuSchreier CFSG.Sporadic.SmallF2.Native

public section

namespace Certificates

open CFSG.Sporadic.Co2Schreier

set_option maxRecDepth 100000 in
open CFSG CFSG.Sporadic CFSG.Sporadic.Co2Schreier CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native in
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Mathieu CFSG.Sporadic.Co2Cert in
open CFSG.Sporadic.RuSchreier CFSG.Sporadic.SmallF2.Native in
theorem certificate2062 : (witRec.third.baseIndices.Nodup)
    ∧ (∀ x ∈ witRec.third.baseIndices, x < 2300) := ⟨by decide +kernel, by decide +kernel⟩

end Certificates
