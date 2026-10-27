module

public import Certificates.Data.MaxD2Perm

public section

namespace CFSG.StandardType.TitsOvergroup

open CFSG.PSL3Four.Native
open Certificates.FusD2Perm (wordT)
open Certificates.MaxD2Perm (fpTab fpOK)

structure PairData where
  n : Nat
  gT : Array Tab
  gOrder : Nat
  pW : List (List Int)
  pOrder : Nat
  nW : List (List Int)
  nOrder : Nat
  fpPts : List Nat
  repW : List (List Int)
  kind : List Nat
  genW : List (List (List Int))
  sideW : List (List (List Int))
  sideOrder : List Nat
deriving Inhabited

@[expose] def invWord (w : List Int) : List Int := (w.map fun z => -z).reverse

@[expose] def conjWord (g w : List Int) : List Int := g ++ w ++ invWord g

variable (D : PairData)

@[expose] def giT : Array Tab := D.gT.map (invTab D.n)

@[expose] def wT (w : List Int) : Tab := wordT D.n D.gT (giT D) w

@[expose] def pGens : Array Tab := (D.pW.map (wT D)).toArray

@[expose] def pEnum : Enum := enumBFS D.n (pGens D) D.pOrder

@[expose] def nGens : Array Tab := (D.nW.map (wT D)).toArray

@[expose] def nGensI : Array Tab := (nGens D).map (invTab D.n)

@[expose] def nEnum : Enum := enumBFS D.n (nGens D) D.nOrder

@[expose] def repT : Array Tab := #[idTab D.n] ++ (D.repW.map (wT D)).toArray

@[expose] def repI : Array Tab := (repT D).map (invTab D.n)

@[expose] def sideGens (k : Nat) : Array Tab := ((D.sideW.getD k []).map (wT D)).toArray

@[expose] def sideEnum (k : Nat) : Enum := enumBFS D.n (sideGens D k) (D.sideOrder.getD k 0)

@[expose] def checkInv : Bool :=
  allBelow D.gT.size fun j => (giT D)[j]!.size == D.n && comp D.n (giT D)[j]! D.gT[j]! == idTab D.n

@[expose] def checkP : Bool := enumOK D.n (pGens D) (pEnum D) && (pEnum D).tabs.size == D.pOrder

@[expose] def checkN : Bool := enumOK D.n (nGens D) (nEnum D) && (nEnum D).tabs.size == D.nOrder

@[expose] def checkNormal : Bool := normalOK D.n (pEnum D).tabs (nGens D) (nGensI D) (pGens D)

@[expose] def checkSide : Bool :=
  D.sideOrder.length == D.sideW.length &&
    allBelow D.sideW.length fun k =>
      enumOK D.n (sideGens D k) (sideEnum D k) && (sideEnum D k).tabs.size == D.sideOrder.getD k 0

@[expose] def fp3 (pts : List Nat) (a b c : Tab) : Tab := (pts.map fun x => a[b[c[x]!]!]!).toArray

@[expose] def memFp3 (n : Nat) (pts : List Nat) (fpIdx : Std.HashMap Tab Nat) (fpT T : Array Tab)
    (a b c : Tab) : Bool :=
  let pos := posOf fpIdx fpT (fp3 pts a b c)
  decide (pos < T.size) && T[pos]! == comp n (comp n a b) c

@[expose] def conjCount3 (n : Nat) (pts : List Nat) (fpIdx : Std.HashMap Tab Nat)
    (fpT T : Array Tab) (xi x : Tab) : Nat :=
  countBelow T.size fun k => memFp3 n pts fpIdx fpT T xi T[k]! x

@[expose] def dcSum3 (n k : Nat) (pts : List Nat) (fpIdx : Std.HashMap Tab Nat)
    (fpT T rep repi : Array Tab) : Nat :=
  (List.range rep.size).foldl
    (fun s i => s + k * k / conjCount3 n pts fpIdx fpT T repi[i]! rep[i]!) 0

@[expose] def dcDisjoint3 (n : Nat) (pts : List Nat) (fpIdx : Std.HashMap Tab Nat)
    (fpT T rep repi : Array Tab) : Bool :=
  allBelow rep.size fun i => allBelow rep.size fun j =>
    !decide (i < j) ||
      (let ri := repi[i]!
       let rj := rep[j]!
       allBelow T.size fun k => !memFp3 n pts fpIdx fpT T ri T[k]! rj)

@[expose] def checkCover : Bool :=
  let nT := (nEnum D).tabs
  let fpT := nT.map (fpTab D.fpPts)
  let fpIdx := indexOf fpT
  let rep := repT D
  let repi := repI D
  D.fpPts.all (· < D.n) && fpOK D.fpPts nT && invsOK D.n rep repi &&
    dcSum3 D.n D.nOrder D.fpPts fpIdx fpT nT rep repi == D.gOrder &&
    dcDisjoint3 D.n D.fpPts fpIdx fpT nT rep repi

@[expose] def pairLetters (g gi : Tab) : Array Tab :=
  pGens D ++ (pGens D).map (conjTab D.n g gi)

@[expose] def checkGen : Bool :=
  let rep := repT D
  let repi := repI D
  D.kind.length == D.repW.length && D.genW.length == D.repW.length &&
    allBelow D.repW.length fun i =>
      D.kind[i]! != 0 ||
        ((D.genW[i]!).length == D.gT.size &&
          (let al := pairLetters D rep[i + 1]! repi[i + 1]!
           let ali := al.map (invTab D.n)
           invsOK D.n al ali &&
             allBelow D.gT.size fun j => wordT D.n al ali (D.genW[i]!)[j]! == D.gT[j]!))

@[expose] def checkSideMem : Bool :=
  let rep := repT D
  allBelow D.repW.length fun i =>
    D.kind[i]! == 0 ||
      (decide (D.kind[i]! - 1 < D.sideW.length) &&
        (let E := sideEnum D (D.kind[i]! - 1)
         found (indexOf E.tabs) E.tabs rep[i + 1]!))

@[expose] def checkSideGen (sg : List (List (List Int))) : Bool :=
  let rep := repT D
  let repi := repI D
  sg.length == D.repW.length &&
    allBelow D.repW.length fun i =>
      D.kind[i]! == 0 ||
        (decide (D.kind[i]! - 1 < D.sideW.length) &&
          (sg[i]!).length == (sideGens D (D.kind[i]! - 1)).size &&
          (let al := pairLetters D rep[i + 1]! repi[i + 1]!
           let ali := al.map (invTab D.n)
           invsOK D.n al ali &&
             allBelow (sideGens D (D.kind[i]! - 1)).size fun j =>
               wordT D.n al ali (sg[i]!)[j]! == (sideGens D (D.kind[i]! - 1))[j]!))

@[expose] def checkSideNorm : Bool :=
  allBelow D.sideW.length fun k =>
    normalOK D.n (sideEnum D k).tabs (nGens D) (nGensI D) (sideGens D k)

@[expose] def checkMemW (memW : List (List (List Int))) : Bool :=
  decide (memW.length ≤ D.sideW.length) &&
    allBelow memW.length fun k =>
      let E := sideEnum D k
      let idx := indexOf E.tabs
      (memW.getD k []).all fun w => found idx E.tabs (wT D w)

@[expose] def pairCheck : Bool :=
  checkInv D && checkP D && checkN D && checkNormal D && checkSide D && checkCover D &&
    checkGen D && checkSideMem D

end CFSG.StandardType.TitsOvergroup
