module

public import CFSG.RankThree.Native.ChainCentralizer
public import CFSG.Monster.B.Fischer.Fi22OrderCheckInputs
public import CFSG.Sporadic.FischerOddCore.Fi22ExtCheckInputs
public import Certificates.Data.Fi22TwistData
public import CFSG.Certificates.NativeSchreierCard
public import Mathlib.GroupTheory.Schreier
public import Std.Data.HashMap

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017.Fi22TwistNative

open CFSG.Sporadic.FischerOddCore

@[expose] def hexVal (c : Char) : Nat :=
  if c.isDigit then c.toNat - 48 else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 87 else 16

@[expose] def hexNums (d : Nat) (s : String) : Array Nat :=
  (s.foldl (fun (acc : Array Nat × Nat × Nat) c =>
    let v := hexVal c
    if v < 16 then
      if acc.2.2 + 1 = d then (acc.1.push (acc.2.1 * 16 + v), 0, 0)
      else (acc.1, acc.2.1 * 16 + v, acc.2.2 + 1)
    else acc) (#[], 0, 0)).1

@[expose] def rowsOf (m : Nat) (a : Array Nat) : Array (Array Nat) :=
  Array.ofFn (n := a.size / m) fun i => a.extract (i.val * m) (i.val * m + m)

@[expose] def permsOf (s : String) : Array (Array Nat) := rowsOf 3510 (hexNums 3 s)

@[expose] def qGens (k : Nat) : Array (Array Nat) :=
  permsOf (#[qGensHex0, qGensHex1, qGensHex2][k]!)

@[expose] def tArr (k : Nat) : Array Nat := fi22ExtArr (21 + k)

@[expose] def repXYZ : Array (Array Nat) := permsOf repXYZHex

@[expose] def repX (j : Nat) : Array Nat := repXYZ[3 * j]!

@[expose] def repY (j : Nat) : Array Nat := repXYZ[3 * j + 1]!

@[expose] def repZ (j : Nat) : Array Nat := repXYZ[3 * j + 2]!

end CFSG.LocalAnalysis.GLTheoremA.H1017.Fi22TwistNative
