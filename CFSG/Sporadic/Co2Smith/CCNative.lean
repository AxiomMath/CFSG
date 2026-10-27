module

public import Certificates.Data.CFSGNative.Co2Smith.Census

public section

namespace CFSG.Sporadic.Co2Smith.Native

open CFSG.Sporadic.SmallF2.Native

set_option compiler.extract_closed false

@[expose] def hashC (R : Array Nat) : Nat :=
  R.foldl (fun acc x => (acc * 1000003 + x) % 18446744073709551557) 0

@[expose] def conjC (g gi y : Array Nat) : Array Nat := mulRowsF (mulRowsF g y) gi

@[expose] def treeC (G Gi : Array (Array Nat)) (start : Array Nat) (n : Nat)
    (rec_ : Array (Array Nat) × Array Nat × Array Nat) : Bool :=
  let pts := rec_.1
  let par := rec_.2.1
  let let_ := rec_.2.2
  let pm : Std.HashMap Nat Nat := Id.run do
    let mut m : Std.HashMap Nat Nat := ∅
    for i in [0:pts.size] do
      m := m.insert (hashC pts[i]!) i
    return m
  pts.size == n && par.size == n && let_.size == n && pts[0]! == start &&
    (List.range n).all fun i =>
      pm.getD (hashC pts[i]!) n == i &&
      (i == 0 || (par[i]! < i && let_[i]! < G.size &&
        pts[i]! == conjC G[let_[i]!]! Gi[let_[i]!]! pts[par[i]!]!))

@[expose] def ccReps : List (Nat × Nat) :=
  [(1, 0), (0, 26805), (32, 26805), (0, 2331), (2, 2331), (80, 2331), (0, 1082), (13, 1082),
    (0, 144)]

@[expose] def ccSqZ : List Nat := [1792, 0, 0, 384, 192, 384, 0, 0, 0]

@[expose] def ccSqR : List Nat := [5376, 0, 0, 1152, 128, 384, 512, 0, 0]

@[expose] def ccCls : List Nat := [270, 1008, 1008, 1260, 22680, 1260, 15120, 15120, 120960]

@[expose] def ccCE : List Nat := [256, 32, 32, 128, 64, 128, 32, 32, 16]

@[expose] def ccInvE : List Nat := [272, 32, 32, 80, 80, 80, 32, 32, 32]

@[expose] def treeM (G : Array (Array Nat)) (n : Nat)
    (rec_ : Array (Array Nat) × Array Nat × Array Nat) : Bool :=
  let pts := rec_.1
  let par := rec_.2.1
  let let_ := rec_.2.2
  let pm : Std.HashMap Nat Nat := Id.run do
    let mut m : Std.HashMap Nat Nat := ∅
    for i in [0:pts.size] do
      m := m.insert (hashC pts[i]!) i
    return m
  pts.size == n && par.size == n && let_.size == n && pts[0]! == idRows 22 &&
    (List.range n).all fun i =>
      pm.getD (hashC pts[i]!) n == i &&
      (i == 0 || (par[i]! < i && let_[i]! < G.size &&
        pts[i]! == mulRowsF pts[par[i]!]! G[let_[i]!]!)) &&
      (List.range G.size).all fun l =>
        let y := mulRowsF pts[i]! G[l]!
        let p := pm.getD (hashC y) n
        p < n && pts[p]! == y

@[expose] def ccSylSize : List Nat := [65536, 32768, 65536]

end CFSG.Sporadic.Co2Smith.Native
