
module

public import CFSG.Sporadic.FischerOddCore.Fi22ExtSylowCheckBase
public import Certificates.Data.CFSGNative.FischerOddCore.Checks
public meta import CFSG.Sporadic.FischerOddCore.Fi22ExtSylowCheckBase
public meta import Certificates.Data.CFSGNative.FischerOddCore.Checks
public import CFSG.Sporadic.FischerOddCore.Fi22ExtCoverRecords
public meta import CFSG.Sporadic.FischerOddCore.Fi22ExtCoverRecords
public meta import CFSG.Sporadic.FischerOddCore.Fi24R2Data
public import CFSG.Sporadic.FischerOddCore.Fi24R2Data

public section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Fischer
open CFSG.Sporadic.FischerOddCore.Native

@[expose] def fi22ExtQArr : Array Nat := fi22ExtArr 0

@[expose] def fi22ExtVArr : Array Nat := fi22ExtArr 1

@[expose] def fi22ExtFullArr (I : Nat) : Array Nat :=
  let c := unidxS fi22TLevels I
  Array.ofFn (n := 3510) fun p => fi22ExtQArr[tr3 fi22TLevels c.1.1 c.1.2.1 c.1.2.2
    fi22ExtQiArr[if c.2 then fi22ExtVArr[p.val]! else p.val]!]!

@[expose] def fi22ExtSteps : Array (Array Nat) := Array.ofFn (n := 10) fun k => fi22ExtArr256 k.val

@[expose] def fi22ExtStepsInv : Array (Array Nat) := fi22ExtSteps.map (invCand 256)

@[expose] def fi22ExtRoots : Array Nat := fi22ExtRootsRec

@[expose] def fi22ExtLabels : LabelCert := fi22ExtLabelsRec

@[expose] def fixCount (n : Nat) (g : Array Nat) : Nat := (List.range n).countP fun p => g[p]! == p

end CFSG.Sporadic.FischerOddCore
