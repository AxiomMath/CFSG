module

public import Certificates.Data.CFSGNative.SectionRank.TitsChain

public section

namespace CFSG.SectionRank.Native.Tits

open CFSG.Sporadic.Th.Native CFSG.Perm.Native

set_option compiler.extract_closed false

@[expose] def isManifest (w : List Int) : Bool :=
  w == [1] || w == [-1] || w == [2, 2] || w == [-2, -2] ||
    (w.length == 4 && w[2]! == -w[0]! && w[3]! == -w[1]!)

@[expose] def tLetters (_ : Unit := ()) : Array (List Int) := #[
  [1], [-1], [2, 2], [-2, -2], [1, 2, -1, -2], [1, 3, -1, -3], [1, 4, -1, -4], [1, -2, -1, 2],
  [1, -3, -1, 3], [1, -4, -1, 4], [2, 1, -2, -1], [2, 3, -2, -3], [2, 4, -2, -4], [2, -1, -2, 1],
  [2, -3, -2, 3], [2, -4, -2, 4], [3, 1, -3, -1], [3, 2, -3, -2], [3, 4, -3, -4], [3, -1, -3, 1],
  [3, -2, -3, 2], [3, -4, -3, 4], [4, 1, -4, -1], [4, 2, -4, -2], [4, 3, -4, -3], [4, -1, -4, 1],
  [4, -2, -4, 2], [4, -3, -4, 3], [-1, 2, 1, -2], [-1, 3, 1, -3], [-1, 4, 1, -4], [-1, -2, 1, 2],
  [-1, -3, 1, 3], [-1, -4, 1, 4], [-2, 1, 2, -1], [-2, 3, 2, -3], [-2, 4, 2, -4], [-2, -1, 2, 1],
  [-2, -3, 2, 3], [-2, -4, 2, 4], [-3, 1, 3, -1], [-3, 2, 3, -2], [-3, 4, 3, -4], [-3, -1, 3, 1],
  [-3, -2, 3, 2], [-3, -4, 3, 4], [-4, 1, 4, -1], [-4, 2, 4, -2], [-4, 3, 4, -3], [-4, -1, 4, 1],
  [-4, -2, 4, 2], [-4, -3, 4, 3]]

@[expose] def texpand (tw : List Nat) : List Int := tw.flatMap fun k => tLetters[k]!

@[expose] def wT (w : List Int) : Table := wordT nPts (letterT nPts genTables) w

@[expose] def eqOn (P Q : Table) : Bool :=
  allIn 0 checkPts.size fun t => ap P checkPts[t]! == ap Q checkPts[t]!

structure TitsWitness where
  wx : List Nat
  wy : List Nat
  wh : List Nat
  nums : List Nat

@[expose] def lettersOK (D : TitsWitness) : Bool :=
  allIn 0 tLetters.size (fun k => isManifest tLetters[k]!) &&
    (D.wx ++ D.wy ++ D.wh).all (· < tLetters.size)

@[expose] def nfT (X Y Z : Table) (i j k : Nat) : Table :=
  compT nPts (compT nPts (powT nPts i X) (powT nPts j Y)) (powT nPts k Z)

@[expose] def cubicOK (D : TitsWitness) : Bool :=
  let X := wT (texpand D.wx)
  let Y := wT (texpand D.wy)
  let H := wT (texpand D.wh)
  let Xi := invT nPts X
  let Yi := invT nPts Y
  let Z := compT nPts (compT nPts (compT nPts X Y) Xi) Yi
  let n := D.nums
  lettersOK D && n.length == 7 && invOK nPts X Xi && invOK nPts Y Yi &&
    eqOn (powT nPts 3 X) (idT nPts) && eqOn (powT nPts 3 Y) (idT nPts) &&
    !eqOn Z (idT nPts) && eqOn (compT nPts Z X) (compT nPts X Z) &&
    eqOn (compT nPts Z Y) (compT nPts Y Z) &&
    allIn 0 27 (fun u => allIn 0 27 fun v => u == v ||
      !eqOn (nfT X Y Z (u % 3) (u / 3 % 3) (u / 9)) (nfT X Y Z (v % 3) (v / 3 % 3) (v / 9))) &&
    eqOn (compT nPts H X) (compT nPts (nfT X Y Z n[0]! n[1]! n[4]!) H) &&
    eqOn (compT nPts H Y) (compT nPts (nfT X Y Z n[2]! n[3]! n[5]!) H) &&
    eqOn (compT nPts H Z) (compT nPts (powT nPts n[6]! Z) H)

@[expose] def squareOK (D : TitsWitness) : Bool :=
  let X := wT (texpand D.wx)
  let Y := wT (texpand D.wy)
  let H := wT (texpand D.wh)
  let n := D.nums
  lettersOK D && n.length == 4 &&
    eqOn (powT nPts 5 X) (idT nPts) && eqOn (powT nPts 5 Y) (idT nPts) &&
    eqOn (compT nPts X Y) (compT nPts Y X) &&
    allIn 0 25 (fun u => allIn 0 25 fun v => u == v ||
      !eqOn (nfT X Y (idT nPts) (u % 5) (u / 5) 0) (nfT X Y (idT nPts) (v % 5) (v / 5) 0)) &&
    eqOn (compT nPts H X) (compT nPts (nfT X Y (idT nPts) n[0]! n[2]! 0) H) &&
    eqOn (compT nPts H Y) (compT nPts (nfT X Y (idT nPts) n[1]! n[3]! 0) H)

@[expose] def titsSylow3 (_ : Unit := ()) : TitsWitness where
  wx := [2, 23, 3, 24, 3, 0, 3, 0, 3, 10, 0, 10, 11, 4, 0, 18, 24, 0, 4, 11, 0, 12, 12, 23, 3, 18,
      18, 18, 0, 3, 23, 2, 2, 17]
  wy := [2, 23, 3, 24, 3, 0, 3, 0, 3, 10, 0, 10, 11, 4, 0, 18, 24, 2, 23, 0, 18, 11, 11, 23, 0, 2,
      18, 2, 1, 11, 24, 11, 12, 2, 23, 0, 18, 11, 11, 23, 0, 2, 18, 2, 1, 11, 24, 11, 12]
  wh := [2, 23, 0, 18, 11, 11, 23, 0, 2, 18, 2, 1, 11, 24, 11, 12]
  nums := [1, 2, 2, 2, 0, 0, 1]

@[expose] def titsSylow5 (_ : Unit := ()) : TitsWitness where
  wx := [23, 1, 4, 1]
  wy := [12, 2, 23, 24, 17, 11, 0, 11, 11, 23, 10, 23, 17, 11, 24, 0]
  wh := [18, 0, 24, 23, 17, 10, 23, 0, 0, 4, 18, 12, 12, 2]
  nums := [3, 4, 3, 2]

end CFSG.SectionRank.Native.Tits
