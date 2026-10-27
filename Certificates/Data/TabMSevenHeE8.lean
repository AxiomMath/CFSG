module

public import CFSG.Sporadic.HeldB.CertPChainData

@[expose] public section

namespace CFSG.HardMathSupport.Dickson.I271.TabMSeven

open CFSG.Sporadic.HeldB

def evPt (A B : Array Nat) (w : List Nat) (p : Nat) : Nat :=
  w.foldr (fun k q => if k = 0 then A[q]! else B[q]!) p

def baseImg (A B : Array Nat) (w : List Nat) : List Nat :=
  (List.range 5).map (evPt A B w)

def fixesBase (A B : Array Nat) (w : List Nat) : Bool :=
  (List.range 5).all fun b => evPt A B w b == b

def heE8Word1 : List Nat := [0]

def heE8Word2 : List Nat :=
  [1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1]

def heE8Word3 : List Nat :=
  [1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1]

def heE8Word (v : Bool × Bool × Bool) : List Nat :=
  (if v.1 then heE8Word1 else []) ++ (if v.2.1 then heE8Word2 else []) ++
    (if v.2.2 then heE8Word3 else [])

def boolTriples : List (Bool × Bool × Bool) :=
  [(false, false, false), (false, false, true), (false, true, false), (false, true, true),
    (true, false, false), (true, false, true), (true, true, false), (true, true, true)]

def heE8OK (A B : Array Nat) : Bool :=
  (heE8Word1 ++ heE8Word2 ++ heE8Word3).all (fun k => decide (k < 2)) &&
    fixesBase A B (heE8Word1 ++ heE8Word1) && fixesBase A B (heE8Word2 ++ heE8Word2) &&
    fixesBase A B (heE8Word3 ++ heE8Word3) &&
    fixesBase A B (heE8Word1 ++ heE8Word2 ++ heE8Word1 ++ heE8Word2) &&
    fixesBase A B (heE8Word1 ++ heE8Word3 ++ heE8Word1 ++ heE8Word3) &&
    fixesBase A B (heE8Word2 ++ heE8Word3 ++ heE8Word2 ++ heE8Word3) &&
    decide (boolTriples.map fun v => baseImg A B (heE8Word v)).Nodup

def heE8Check (_ : Unit := ()) : Bool :=
  let A := heGen 0
  let B := heGen 1
  heE8OK A B

end CFSG.HardMathSupport.Dickson.I271.TabMSeven
