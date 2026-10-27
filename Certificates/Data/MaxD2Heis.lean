module

public import Certificates.Data.MaxD2Perm

public section

namespace Certificates.MaxD2Heis

open CFSG.PSL3Four.Native
open Certificates.FusD2Perm (powT wordT)
open Certificates.MaxD2Perm

@[expose] def hrEnum (D : Data) : Enum := enumBFS D.n (rGens D) (D.p ^ 3)

@[expose] def checkHR (D : Data) : Bool :=
  enumOK D.n (rGens D) (hrEnum D) && (hrEnum D).tabs.size == D.p ^ 3

@[expose] def checkHNormal (D : Data) : Bool :=
  normalOK D.n (hrEnum D).tabs (nGens D) (nGensI D) (rGens D)

@[expose] def checkHMoves (D : Data) : Bool :=
  let rT := (hrEnum D).tabs
  let rIdx := indexOf rT
  anyBelow D.gT.size fun j =>
    !(allBelow (rGens D).size fun i =>
      found rIdx rT (conjTab D.n D.gT[j]! (giT D)[j]! (rGens D)[i]!))

@[expose] def commutesUV (n : Nat) (u v x : Tab) : Bool :=
  comp n x u == comp n u x && comp n x v == comp n v x

@[expose] def zTabs (D : Data) : Array Tab :=
  let u := (rGens D)[0]!
  let v := (rGens D)[1]!
  (hrEnum D).tabs.filter (commutesUV D.n u v)

@[expose] def checkHZ (D : Data) : Bool := (zTabs D).size == D.p

@[expose] def checkHExp (D : Data) : Bool :=
  let rT := (hrEnum D).tabs
  allBelow rT.size fun k => powT D.n rT[k]! D.p == idTab D.n

@[expose] def checkHComm (D : Data) : Bool :=
  let rT := (hrEnum D).tabs
  let zT := zTabs D
  let u := (rGens D)[0]!
  let v := (rGens D)[1]!
  comp D.n u v != comp D.n v u &&
    allBelow rT.size fun k => allBelow rT.size fun l =>
      let xy := comp D.n rT[k]! rT[l]!
      let yx := comp D.n rT[l]! rT[k]!
      anyBelow zT.size fun j => xy == comp D.n zT[j]! yx

@[expose] def checkHTorus (D : Data) : Bool :=
  let nT := (nEnum D).tabs
  let nIdx := indexOf nT
  let rT := (hrEnum D).tabs
  let zT := zTabs D
  let tT := wT D D.tW
  let tI := invTab D.n tT
  tI.size == D.n && comp D.n tI tT == idTab D.n && found nIdx nT tT &&
    (let tm := powT D.n tT D.tm
     let tmI := powT D.n tI D.tm
     allBelow rT.size fun k =>
       let y := comp D.n (comp D.n tm rT[k]!) tmI
       let xl := powT D.n rT[k]! D.tlam
       anyBelow zT.size fun j => y == comp D.n xl zT[j]!) &&
    (let te := powT D.n tT D.te
     let teI := powT D.n tI D.te
     allBelow rT.size fun k =>
       let y := comp D.n (comp D.n (comp D.n te rT[k]!) teI) rT[k]!
       anyBelow zT.size fun j => y == zT[j]!) &&
    allBelow (D.tm - 1) fun k =>
      let tk := powT D.n tT (k + 1)
      let tkI := powT D.n tI (k + 1)
      allBelow rT.size fun i =>
        let y := comp D.n (comp D.n tk rT[i]!) tkI
        zT.contains rT[i]! ||
          allBelow D.p fun j =>
            let xj := powT D.n rT[i]! j
            allBelow zT.size fun l => !(y == comp D.n xj zT[l]!)

@[expose] def checkHCent (D : Data) : Bool :=
  let nT := (nEnum D).tabs
  let rT := (hrEnum D).tabs
  let rIdx := indexOf rT
  let u := (rGens D)[0]!
  let v := (rGens D)[1]!
  allBelow nT.size fun k => !commutesUV D.n u v nT[k]! || found rIdx rT nT[k]!

@[expose] def checkHeis (D : Data) : Bool :=
  checkInv D && checkHR D && checkN D && checkHNormal D && checkHMoves D && checkHZ D &&
    checkHExp D && checkHComm D && checkHTorus D && checkHCent D && checkMax D

end Certificates.MaxD2Heis
