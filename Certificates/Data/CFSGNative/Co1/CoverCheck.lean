module

public import Certificates.Data.CFSGNative.Co1.Involutions

public section

namespace CFSG.Sporadic.Co1.CoverNative

open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.InvNative

@[expose] def letterRows (ga gb gaI gbI : Array Nat) (l : Nat × Bool) : Array Nat :=
  if l.1 == 0 then (if l.2 then ga else gaI) else (if l.2 then gb else gbI)

@[expose] def wordRowsAB (d : Nat) (ga gb gaI gbI : Array Nat) (w : List (Nat × Bool)) :
    Array Nat :=
  w.foldl (fun acc l => mulRows d acc (letterRows ga gb gaI gbI l)) (idRows d)

@[expose] def relCheckAB (d : Nat) (ga gb gaI gbI : Array Nat)
    (rels : List (List (Nat × Bool))) : Bool :=
  mulRows d ga gaI == idRows d && mulRows d gb gbI == idRows d &&
    rels.all fun w => wordRowsAB d ga gb gaI gbI w == idRows d

@[expose] def eprodRows (eps : Array (Array Nat)) (x : Nat) : Array Nat :=
  (List.range 11).foldl (fun acc i => if x.testBit i then mulRows 24 acc eps[i]! else acc)
    (idRows 24)

@[expose] def epsBasicOK (eps : Array (Array Nat)) : Bool :=
  eps.size == 11 && (List.range 11).all fun i =>
    validRows eps[i]! && mulRows 24 eps[i]! eps[i]! == idRows 24 &&
      (List.range 11).all fun j => mulRows 24 eps[i]! eps[j]! == mulRows 24 eps[j]! eps[i]!

@[expose] def epsInjOK (eps : Array (Array Nat)) : Bool :=
  (List.range 2047).all fun k =>
    validRows (eprodRows eps (k + 1)) && eprodRows eps (k + 1) != idRows 24

@[expose] def normOK (eps : Array (Array Nat)) (g : Array Nat) (cols : Array Nat) : Bool :=
  cols.size == 11 && (List.range 11).all fun i =>
    mulRows 24 g eps[i]! == mulRows 24 (eprodRows eps cols[i]!) g

end CFSG.Sporadic.Co1.CoverNative
