module

public import Certificates.Data.FusD2Perm

public section

namespace Certificates.MaxD2Perm

open CFSG.PSL3Four.Native
open Certificates.FusD2Perm (powT wordT)

structure Data where
  n : Nat
  p : Nat
  gT : Array Tab
  gOrder : Nat
  uW : List Int
  vW : List Int
  nW : List (List Int)
  nOrder : Nat
  fpPts : List Nat
  repW : List (List Int)
  genW : List (List (List Int))
  tW : List Int
  tm : Nat
  tlam : Nat
  te : Nat
deriving Inhabited

@[expose] def giT (D : Data) : Array Tab := D.gT.map (invTab D.n)

@[expose] def wT (D : Data) (w : List Int) : Tab := wordT D.n D.gT (giT D) w

@[expose] def rWs (D : Data) : List (List Int) := [D.uW, D.vW]

@[expose] def rGens (D : Data) : Array Tab := ((rWs D).map (wT D)).toArray

@[expose] def rEnum (D : Data) : Enum := enumBFS D.n (rGens D) (D.p ^ 2)

@[expose] def nGens (D : Data) : Array Tab := (D.nW.map (wT D)).toArray

@[expose] def nGensI (D : Data) : Array Tab := (nGens D).map (invTab D.n)

@[expose] def nEnum (D : Data) : Enum := enumBFS D.n (nGens D) D.nOrder

@[expose] def repT (D : Data) : Array Tab := #[idTab D.n] ++ (D.repW.map (wT D)).toArray

@[expose] def repI (D : Data) : Array Tab := (repT D).map (invTab D.n)

@[expose] def checkInv (D : Data) : Bool :=
  allBelow D.gT.size fun j => (giT D)[j]!.size == D.n && comp D.n (giT D)[j]! D.gT[j]! == idTab D.n

@[expose] def checkR (D : Data) : Bool :=
  enumOK D.n (rGens D) (rEnum D) && (rEnum D).tabs.size == D.p ^ 2

@[expose] def checkN (D : Data) : Bool :=
  enumOK D.n (nGens D) (nEnum D) && (nEnum D).tabs.size == D.nOrder

@[expose] def checkNormal (D : Data) : Bool :=
  normalOK D.n (rEnum D).tabs (nGens D) (nGensI D) (rGens D)

@[expose] def checkMoves (D : Data) : Bool :=
  let rT := (rEnum D).tabs
  let rIdx := indexOf rT
  anyBelow D.gT.size fun j =>
    !(allBelow (rGens D).size fun i =>
      found rIdx rT (conjTab D.n D.gT[j]! (giT D)[j]! (rGens D)[i]!))

@[expose] def checkTorus (D : Data) : Bool :=
  let nT := (nEnum D).tabs
  let nIdx := indexOf nT
  let rT := (rEnum D).tabs
  let tT := wT D D.tW
  let tI := invTab D.n tT
  tI.size == D.n && comp D.n tI tT == idTab D.n && found nIdx nT tT &&
    (let tm := powT D.n tT D.tm
     let tmI := powT D.n tI D.tm
     allBelow rT.size fun k => comp D.n (comp D.n tm rT[k]!) tmI == powT D.n rT[k]! D.tlam) &&
    (let te := powT D.n tT D.te
     let teI := powT D.n tI D.te
     allBelow rT.size fun k => comp D.n (comp D.n (comp D.n te rT[k]!) teI) rT[k]! == idTab D.n) &&
    allBelow (D.tm - 1) fun k =>
      let tk := powT D.n tT (k + 1)
      let tkI := powT D.n tI (k + 1)
      allBelow rT.size fun i => rT[i]! == idTab D.n ||
        allBelow D.p fun j => !(comp D.n (comp D.n tk rT[i]!) tkI == powT D.n rT[i]! j)

@[expose] def checkCent (D : Data) : Bool :=
  let nT := (nEnum D).tabs
  let rT := (rEnum D).tabs
  let rIdx := indexOf rT
  let u := (rGens D)[0]!
  let v := (rGens D)[1]!
  allBelow nT.size fun k =>
    !(comp D.n nT[k]! u == comp D.n u nT[k]! && comp D.n nT[k]! v == comp D.n v nT[k]!) ||
      found rIdx rT nT[k]!

@[expose] def fpTab (pts : List Nat) (y : Tab) : Tab := (pts.map fun b => y[b]!).toArray

@[expose] def fpOK (pts : List Nat) (T : Array Tab) : Bool :=
  let fpT := T.map (fpTab pts)
  let fpIdx := indexOf fpT
  allBelow fpT.size fun k => posOf fpIdx fpT fpT[k]! == k

@[expose] def memFp (pts : List Nat) (fpIdx : Std.HashMap Tab Nat) (fpT T : Array Tab) (y : Tab) :
    Bool :=
  let pos := posOf fpIdx fpT (fpTab pts y)
  decide (pos < T.size) && T[pos]! == y

@[expose] def conjCount (n : Nat) (pts : List Nat) (fpIdx : Std.HashMap Tab Nat)
    (fpT T : Array Tab) (xi x : Tab) : Nat :=
  countBelow T.size fun k => memFp pts fpIdx fpT T (comp n (comp n xi T[k]!) x)

@[expose] def dcSum (n k : Nat) (pts : List Nat) (fpIdx : Std.HashMap Tab Nat)
    (fpT T rep repi : Array Tab) : Nat :=
  (List.range rep.size).foldl
    (fun s i => s + k * k / conjCount n pts fpIdx fpT T repi[i]! rep[i]!) 0

@[expose] def dcDisjoint (n : Nat) (pts : List Nat) (fpIdx : Std.HashMap Tab Nat)
    (fpT T rep repi : Array Tab) : Bool :=
  allBelow rep.size fun i => allBelow rep.size fun j =>
    !decide (i < j) ||
      (let ri := repi[i]!
       let rj := rep[j]!
       allBelow T.size fun k => !memFp pts fpIdx fpT T (comp n (comp n ri T[k]!) rj))

@[expose] def dcGenerate (D : Data) (rep repi : Array Tab) : Bool :=
  D.genW.length == D.repW.length &&
    allBelow D.repW.length fun i =>
      (D.genW[i]!).length == D.gT.size &&
        (let gs := nGens D ++ #[rep[i + 1]!]
         let gi := nGensI D ++ #[repi[i + 1]!]
         allBelow D.gT.size fun j => wordT D.n gs gi (D.genW[i]!)[j]! == D.gT[j]!)

@[expose] def checkMax (D : Data) : Bool :=
  let nT := (nEnum D).tabs
  let fpT := nT.map (fpTab D.fpPts)
  let fpIdx := indexOf fpT
  let rep := repT D
  let repi := repI D
  fpOK D.fpPts nT && invsOK D.n rep repi &&
    dcSum D.n D.nOrder D.fpPts fpIdx fpT nT rep repi == D.gOrder &&
    dcDisjoint D.n D.fpPts fpIdx fpT nT rep repi && dcGenerate D rep repi

@[expose] def check (D : Data) : Bool :=
  checkInv D && checkR D && checkN D && checkNormal D && checkMoves D && checkTorus D &&
    checkCent D && checkMax D

end Certificates.MaxD2Perm
