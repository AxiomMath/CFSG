module

public import Certificates.Data.MaxD2Heis

public section

namespace Certificates.OverD2Perm

open CFSG.PSL3Four.Native
open Certificates.FusD2Perm (powT wordT)
open Certificates.MaxD2Perm
open Certificates.MaxD2Heis (hrEnum checkHR)

@[expose] def genOK (D : Data) (gs gi : Array Tab) (ws : List (List Int)) : Bool :=
  ws.length == D.gT.size &&
    allBelow D.gT.size fun j => wordT D.n gs gi ws[j]! == D.gT[j]!

@[expose] def genAfterOK (D : Data) (k : Nat) (rep repi : Array Tab) : Bool :=
  D.genW.length + k == D.repW.length &&
    allBelow D.genW.length fun i =>
      genOK D (nGens D ++ #[rep[i + k + 1]!]) (nGensI D ++ #[repi[i + k + 1]!]) (D.genW[i]!)

@[expose] def pairOK (D : Data) (pairW : List (List Int)) (rep repi : Array Tab) : Bool :=
  genOK D ((nGens D ++ #[rep[1]!]) ++ #[rep[2]!]) ((nGensI D ++ #[repi[1]!]) ++ #[repi[2]!]) pairW

@[expose] def checkOverMax (D : Data) (pairW : List (List Int)) : Bool :=
  let nT := (nEnum D).tabs
  let fpT := nT.map (fpTab D.fpPts)
  let fpIdx := indexOf fpT
  let rep := repT D
  let repi := repI D
  fpOK D.fpPts nT && invsOK D.n rep repi &&
    dcSum D.n D.nOrder D.fpPts fpIdx fpT nT rep repi == D.gOrder &&
    dcDisjoint D.n D.fpPts fpIdx fpT nT rep repi && genAfterOK D 2 rep repi &&
    pairOK D pairW rep repi

@[expose] def checkOver (D : Data) (pairW : List (List Int)) : Bool :=
  checkInv D && checkN D && invsOK D.n (nGens D) (nGensI D) && checkOverMax D pairW

@[expose] def checkMaximal (D : Data) : Bool :=
  checkInv D && checkN D && invsOK D.n (nGens D) (nGensI D) && checkMax D

@[expose] def closedOK (D : Data) (i c : Nat) : Bool :=
  let nT := (nEnum D).tabs
  let fpT := nT.map (fpTab D.fpPts)
  let fpIdx := indexOf fpT
  let x := (repT D)[i]!
  let xi := (repI D)[i]!
  let xa := nT.map (comp D.n xi)
  decide (0 < i) && decide (i ≤ D.repW.length) && fpOK D.fpPts nT &&
    invsOK D.n (repT D) (repI D) &&
    conjCount D.n D.fpPts fpIdx fpT nT xi x == c && !memFp D.fpPts fpIdx fpT nT x &&
    allBelow nT.size fun k =>
      let y := comp D.n (comp D.n x nT[k]!) x
      memFp D.fpPts fpIdx fpT nT y ||
        anyBelow nT.size fun l => memFp D.fpPts fpIdx fpT nT (comp D.n xa[l]! y)

@[expose] def checkClosedPair (D : Data) (c : Nat) : Bool :=
  checkInv D && checkN D && closedOK D 1 c && closedOK D 2 c

@[expose] def checkW0 (DP DR : Data) (w0W gAW gBW : List Int) : Bool :=
  let n := DP.n
  let nT := (nEnum DP).tabs
  let nIdx := indexOf nT
  let rT := (hrEnum DP).tabs
  let rIdx := indexOf rT
  let w := wT DR w0W
  let wi := invTab n w
  let gB := wT DP gBW
  let gBi := invTab n gB
  let x := conjTab n w wi (wT DP gAW)
  checkInv DP && checkInv DR && checkN DP && checkHR DP && DR.n == n &&
    wi.size == n && comp n wi w == idTab n && gBi.size == n && comp n gBi gB == idTab n &&
    allBelow (rGens DP).size (fun j => found rIdx rT (conjTab n w wi (rGens DP)[j]!)) &&
    !found nIdx nT w &&
    allBelow (nGens DP).size (fun j => found nIdx nT (conjTab n w wi (nGens DP)[j]!)) &&
    anyBelow nT.size fun l => found nIdx nT (comp n (comp n gBi nT[l]!) x)

end Certificates.OverD2Perm
