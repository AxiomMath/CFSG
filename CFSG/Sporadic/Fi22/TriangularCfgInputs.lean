module

public import Certificates.Data.CFSGNative.Fi22.Centralizer
public meta import Certificates.Data.CFSGNative.Fi22.Centralizer

@[expose] public section

namespace CFSG.Sporadic.Fi22.Native

open CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.F3.Native

set_option compiler.extract_closed false

def rank3CfgPts : Array Nat := #[0, 1, 63, 369, 322, 2441, 2488, 3427]

def rank3CfgTab (O : COrbit) (i : Nat) : Table := cTab O (genTables O (-2)) rank3CfgPts[i]!

def rank3CfgBraid (O : COrbit) (i : Nat) : Bool :=
  compT 3510 (compT 3510 (rank3CfgTab O (2 * i)) (rank3CfgTab O (2 * i + 1)))
      (rank3CfgTab O (2 * i)) ==
    compT 3510 (compT 3510 (rank3CfgTab O (2 * i + 1)) (rank3CfgTab O (2 * i)))
      (rank3CfgTab O (2 * i + 1))

def rank3CfgComm (O : COrbit) (a b : Nat) : Bool :=
  compT 3510 (rank3CfgTab O a) (rank3CfgTab O b) == compT 3510 (rank3CfgTab O b) (rank3CfgTab O a)

def rank3CfgChecks (O : COrbit) : Bool :=
  allIn 0 8 (fun i => decide (rank3CfgPts[i]! < 3510)) &&
    allIn 0 4 (fun i => rank3CfgBraid O i) &&
    allIn 0 8 (fun a => allIn 0 8 (fun b => decide (a / 2 = b / 2) || rank3CfgComm O a b))

def rank3CfgCheck (_ : Unit := ()) : Bool := rank3CfgChecks (orbitData ())

end CFSG.Sporadic.Fi22.Native
