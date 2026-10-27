module

public import Certificates.Data.TwinPerpSmSp1Wit
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafQ16L34Data
public import Certificates.Data.CFSGNative.PSL3Four.L34Aut
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafQ16Check

public section

namespace Certificates.TwinPerpSmSp1

open CFSG.Monster.B.Co2.Native CFSG.PSL3Four.Native
open CFSG.CGT.PushingUpLit.SolKNA.R4.Check (qCert)

@[expose] def l34Wit : Q8WitData where
  syl := CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.Check.l34Q16
  xg := gensS
  cW := #[
    [1, 0, 1, 0, 0, 0, 0, 2, 0, 0, 1, 0, 2, 0, 1],
    [2, 1, 0, 0, 2, 0, 0, 1, 0, 2, 0, 2, 0, 1, 0, 0, 1, 2, 0, 0, 2, 0, 1],
    [1, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 1]]

@[expose] def q8SqIn (n : ℕ) (pts sq T : Array (Array ℕ)) : Bool :=
  allLt pts.size fun i =>
    eqA n sq[i]! (idA n) || !eqA n (compA n sq[i]! sq[i]!) (idA n) ||
      allLt pts.size fun j =>
        !eqA n sq[j]! sq[i]! ||
          !eqA n (compA n pts[j]! pts[i]!) (compA n (invCand n pts[i]!) pts[j]!) ||
          memTab T sq[i]!

@[expose] def l34SqCheck (_ : Unit := ()) : Bool :=
  q8SqIn 42 (qCert l34Wit.syl).pts ((qCert l34Wit.syl).pts.map fun y => compA 42 y y)
    (enumBFS 42 gensS 20160).tabs

@[expose] def l34CentCheck (_ : Unit := ()) : Bool :=
  let ER := (enumBFS 42 gTabs 241920).tabs
  let C1 := centTabs 42 (enumBFS 42 gensS 20160).tabs r₁T
  allBelow ER.size fun k =>
    !(allBelow C1.size fun a => comp 42 C1[a]! ER[k]! == comp 42 ER[k]! C1[a]!) ||
      powTab 42 ER[k]! 256 == idTab 42

end Certificates.TwinPerpSmSp1
