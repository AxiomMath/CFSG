module

public import Certificates.Data.CFSGNative.F4.Unitary

public section

namespace CFSG.Fischer.Native

open CFSG.F4.Native CFSG.Sporadic.Th.Native

set_option compiler.extract_closed false

@[expose] def tvTabs (_ : Unit := ()) : Array Table := Array.ofFn (n := 693) fun p => tvTable uPts[p.val]!

@[expose] def commPerpOK (T : Array Table) : Bool :=
  allIn 0 693 fun p => allIn 0 693 fun q =>
    (compT 693 T[p]! T[q]! == compT 693 T[q]! T[p]!) == (hermC uPts[p]! uPts[q]! == 0)

@[expose] def tvInjOK (T : Array Table) : Bool :=
  allIn 0 693 fun p => allIn 0 693 fun q => p == q || T[p]! != T[q]!

@[expose] def tvNontrivOK (T : Array Table) : Bool := allIn 0 693 fun p => T[p]! != idT 693

@[expose] def tvConjOK (T : Array Table) : Bool :=
  allIn 0 693 fun p => allIn 0 693 fun q =>
    compT 693 (compT 693 T[p]! T[q]!) T[p]! == T[ap T[p]! q]!

@[expose] def polarCertificate (_ : Unit) : Bool :=
  let T := tvTabs
  T.size == 693 && commPerpOK T && tvInjOK T && tvNontrivOK T && tvConjOK T

end CFSG.Fischer.Native
