module

public import Certificates.Data.CFSGNative.Recognition.HSPinnedData
public import CFSG.Sporadic.Recognition.HSPinnedIdentInputs
public import CFSG.Sporadic.Recognition.HSGraphModelInputs
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignWittAut
public import CFSG.Sporadic.Recognition.HSGraphStab

public section

namespace Certificates.Kernel.HSIdent

open CFSG.ComponentClassification.WittDesign CFSG.Monster.B.Classical.Plane

@[expose] def lmask : List Nat → Nat
  | [] => 0
  | t :: l => 2 ^ t ||| lmask l

@[expose] def allBelow (p : Nat → Bool) : Nat → Bool
  | 0 => true
  | n + 1 => allBelow p n && p n

@[expose] def hexMask (k : Nat) : Nat := mask (hexadList.getD k hexad0)

@[expose] def modelAdjN (n m : Nat) : Bool :=
  if n = 0 then decide (1 ≤ m) && decide (m ≤ 22)
  else if n ≤ 22 then
    decide (m = 0) || (decide (23 ≤ m) && (hexMask (m - 23)).testBit (n - 1))
  else
    (decide (1 ≤ m) && decide (m ≤ 22) && (hexMask (n - 23)).testBit (m - 1)) ||
      (decide (23 ≤ m) && decide (hexMask (n - 23) ≠ hexMask (m - 23)) &&
        decide (hexMask (n - 23) &&& hexMask (m - 23) = 0))

@[expose] def identCheckOn (iso : List Nat) (st : Array (List Nat)) : Bool :=
  allBelow (fun x => allBelow (fun y =>
    (x != y && decide (lmask st[x]! &&& lmask st[y]! ≠ 0)) ==
      modelAdjN (iso.getD x 0 % 100) (iso.getD y 0 % 100)) 100) 100

@[expose] def injCheckOn (iso : List Nat) : Bool :=
  allBelow (fun i => allBelow (fun j =>
    i == j || iso.getD i 0 % 100 != iso.getD j 0 % 100) 100) 100

end Certificates.Kernel.HSIdent
