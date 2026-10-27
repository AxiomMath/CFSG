module

public import CFSG.Sporadic.SuzOddCore.GraphArraysCheck
public import CFSG.Sporadic.SuzOddCore.CertChainCheck
public import Certificates.Data.CFSGNative.Schreier.Refine
public import Mathlib.Data.Fintype.Card
public meta import CFSG.Sporadic.SuzOddCore.GraphArraysCheck
public meta import CFSG.Sporadic.SuzOddCore.CertChainCheck
public meta import Certificates.Data.CFSGNative.Schreier.Refine
public meta import Mathlib.Data.Fintype.Card

public section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def powArr (n : Nat) (t : Array Nat) : Nat → Array Nat
  | 0 => idA n
  | k + 1 => compA n t (powArr n t k)

@[expose] def zArr : Array Nat :=
  powArr 22880 (wordA 22880 certStrongArrs certStrongInvs zWord) zPower

@[expose] def deltaOf (z : Array Nat) : List Nat :=
  (List.range 22880).filter fun i => i != 0 && z[i]! == i

@[expose] def gammaNbr : Array (List Nat) :=
  adjSearch 22880 #[certArr 0, certArr 1] (deltaOf zArr)

@[expose] def indivAt (c : Array Nat) (p j : Nat) : Array Nat := c.set! p (2 + j)

@[expose] def gammaClassCount (c : Array Nat) (v : Nat) : Nat :=
  (Finset.univ.filter fun w : Fin 22880 => c[w.val]! = c[v]!).card

@[expose] def gammaAllOK : Bool :=
  let nbr := gammaNbr
  let c0 : Array Nat := Array.replicate 22880 1
  let c1 := refineIter 22880 nbr (indivAt c0 0 0) 4
  let c2 := refineIter 22880 nbr (indivAt c1 1 1) 5
  let c3 := refineIter 22880 nbr (indivAt c2 2 2) 5
  let c4 := refineIter 22880 nbr (indivAt c3 3 3) 5
  adjOK 22880 #[certArr 0, certArr 1] nbr (deltaOf zArr) &&
    decide (gammaClassCount c0 0 ≤ 22880) && decide (gammaClassCount c1 1 ≤ 8505) &&
    decide (gammaClassCount c2 2 ≤ 1152) && decide (gammaClassCount c3 3 ≤ 4) &&
    decide (c4.toList.Nodup) && c4.size == 22880

end CFSG.Sporadic.SuzOddCore
