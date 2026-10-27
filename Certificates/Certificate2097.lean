
module

public import Certificates.Certificate2097Base

public import CFSG.Sporadic.HNSchreier.FALocalCheckInputs
public meta import CFSG.Sporadic.HNSchreier.LocalCheckBase
public meta import CFSG.Sporadic.HNSchreier.FAData
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import all Init.Data.Array.Basic

public section

namespace Certificates

set_option maxRecDepth 100000 in
open CFSG CFSG.Sporadic CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native in
open CFSG.ONSchreier.Native CFSG.Sporadic.Th.Native in
theorem certificate2097 : faNatChecks = true :=
  by decide +kernel

end Certificates
