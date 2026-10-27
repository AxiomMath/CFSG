module

public import CFSG.Sporadic.ONOddCore.LocalAutPayload
public import Certificates.Data.CFSGNative.ONSchreier.Compact
public meta import CFSG.Sporadic.ONOddCore.LocalAutPayload
public meta import Certificates.Data.CFSGNative.ONSchreier.Compact
public meta import Mathlib.Init
public import Mathlib.Init

public section

namespace CFSG.Sporadic.ONOddCore

open CFSG.ONSchreier.Native

@[expose] def permArr120 (a : Array Nat) : Bool := a.size == 120 && pisInv 120 a (pinvCand 120 a)

@[expose] def tripleList : List (Nat × Nat × Nat) :=
  [(0, 0, 0), (0, 0, 1), (0, 1, 0), (0, 1, 1), (1, 0, 0), (1, 0, 1), (1, 1, 0), (1, 1, 1),
    (2, 0, 0), (2, 0, 1), (2, 1, 0), (2, 1, 1)]

@[expose] def liftFormOK (e : LiftEntry) : Bool :=
  e.words.length == 3 && e.words.all (fun w => w.all fun l => 1 ≤ l && l ≤ 3) &&
    (e.power == 1 || e.power == 3)

@[expose] def localFormOK (c : LocalCert) : Bool :=
  c.quotGens.length == 2 && c.quotGens.all permArr120 &&
    c.records.map (fun r => (r.diag, r.field, r.graph)) == tripleList &&
    c.records.all (fun r => r.images.length == 2 && r.images.all permArr120 &&
      r.lifts.all liftFormOK) &&
    c.records.map (fun r => r.lifts.length) == [4, 0, 0, 4, 0, 0, 0, 0, 0, 4, 4, 0]

end CFSG.Sporadic.ONOddCore
