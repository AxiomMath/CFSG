module

public import CFSG.Sporadic.FischerOddCore.Fi22RelBoundCheck
public import CFSG.Sporadic.FischerOddCore.Fi22CentOrderCheck
public meta import CFSG.Sporadic.FischerOddCore.Fi22RelBoundCheck
public meta import CFSG.Sporadic.FischerOddCore.Fi22CentOrderCheck

public section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Fischer
open CFSG.Sporadic.FischerOddCore.Native

@[expose] def fi22SearchNodes : Array SNode :=
  (fi22SearchNodeData.map fun N => (⟨N.1, N.2.1, N.2.2.1, N.2.2.2.1, N.2.2.2.2⟩ : SNode)).toArray

@[expose] def fi22SearchPoolArr : Array (Array Nat) :=
  Array.ofFn (n := 64) fun j => fi22CentArr (240 + j.val)

@[expose] def fi22SearchAccArr : Array (Array Nat) :=
  Array.ofFn (n := 2) fun i => fi22CentArr (304 + i.val)

end CFSG.Sporadic.FischerOddCore
