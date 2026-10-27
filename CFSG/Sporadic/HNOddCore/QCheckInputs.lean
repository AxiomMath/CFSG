module

public import CFSG.Sporadic.HNOddCore.QData
public import CFSG.Sporadic.HNOddCore.InvArrays
public import CFSG.Sporadic.HNOddCore.ChainUtil
public meta import CFSG.Sporadic.HNOddCore.QData
public meta import CFSG.Sporadic.HNOddCore.InvArrays
public meta import CFSG.Sporadic.HNOddCore.ChainUtil
public meta import Mathlib.GroupTheory.Schreier
public import Mathlib.GroupTheory.Schreier

public section

namespace CFSG.Sporadic.HNOddCore.Native

open CFSG.ONSchreier.Native

@[expose] def cvGens (S : Array (Array Nat)) : Array (Array Nat) := (S.extract 0 9).push S[10]!

@[expose] def subQ (n : Nat) (Q : Array (Array Nat)) (m : Nat) : Array Nat :=
  (List.range Q.size).foldl (fun acc i => if m.testBit i then pcomp n acc Q[i]! else acc) (pid n)

@[expose] def qbList (n : Nat) (Q : Array (Array Nat)) : Array (Array Nat) :=
  Array.ofFn (n := 256) fun m => subQ n Q m.val

@[expose] def colPerm (c : List Nat) : Array Nat :=
  Array.ofFn (n := 256) fun m =>
    (List.range 8).foldl (fun acc i => if m.val.testBit i then acc ^^^ c[i]! else acc) 0

@[expose] def colPerms : Array (Array Nat) := InvData.qColumns.map colPerm

@[noinline, expose] def qChecksH (S Q B K : Array (Array Nat)) : Bool :=
  let Si := pinvs 800 S
  S.size == 11 && Q.size == 8 && B.size == 256 && K.size == 11 &&
    (allBelowN 11 fun g => pisInv 800 S[g]! Si[g]!) &&
    (allBelowN 8 fun i =>
      plettersOK 11 QData.qFlat[i]! && peq 800 (pword 800 S Si QData.qFlat[i]!) Q[i]!) &&
    (allBelowN 8 fun i => allBelowN 8 fun j =>
      peq 800 (pcomp 800 Q[i]! Q[j]!) (pcomp 800 Q[j]! Q[i]!)) &&
    (allBelowN 8 fun i => peq 800 (pcomp 800 Q[i]! Q[i]!) (pid 800)) &&
    (allBelowN 8 fun i => allBelowN 256 fun m =>
      decide (m ^^^ (1 <<< i) < 256) && peq 800 (pcomp 800 Q[i]! B[m]!) B[m ^^^ (1 <<< i)]!) &&
    (allBelowN 11 fun g => pisInv 256 K[g]! (pinvCand 256 K[g]!) && allBelowN 256 fun m =>
      decide ((K[g]!)[m]! < 256) &&
        peq 800 (pcomp 800 Si[g]! (pcomp 800 B[m]! S[g]!)) B[(K[g]!)[m]!]!) &&
    chainCheck 800 (cvGens S) QData.cvWords QData.cvBase QData.cvSizes &&
    chainCheck 800 Q QData.qWords QData.qBase QData.qSizes &&
    chainCheck 256 K QData.conjWords QData.conjBase QData.conjSizes

@[noinline, expose] def qChecks : Bool :=
  qChecksH InvData.s4Perms InvData.qPerms (qbList 800 InvData.qPerms) colPerms

end CFSG.Sporadic.HNOddCore.Native
