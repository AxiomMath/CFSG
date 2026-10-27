module

public import CFSG.Monster.GMS.Griess13.DataPacked

@[expose] public section

namespace CFSG.Monster.GMS.Griess13.Co1Data

open scoped Matrix commutatorElement

@[expose] def commCheck : Bool :=
  (List.finRange 6).all fun i => (List.finRange 6).all fun j =>
    PR.eq ((prE i).mul (prE j)) ((prE j).mul (prE i))

@[expose] def cubeCheck :
    Bool := (List.finRange 6).all fun i => PR.eq ((prE i).pow 3) PR.one

@[expose] def prNs : Fin 2 → PR := ![prN1, prN2]

@[expose] def nConjCheck : Bool :=
  (List.finRange 2).all fun s => (List.finRange 6).all fun i =>
    PR.eq ((prNs s).conj (prE i)) (prIota (actN s i))

@[expose] def scal2 : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  Matrix.of fun i j => if i = j then 2 else 0

@[expose] def tauCheck : Bool :=
  PR.eq (prTau.mul prTau) PR.one &&
    (List.finRange 6).all fun i =>
      PR.eq (prTau.conj (prE i)) ((prE i).pow 2) &&
      PR.eq (prTau.conj (prE i)) (prIota (scal2 i))

@[expose] def mSCheck : Bool :=
  (List.finRange 2).all fun i => PR.eq (prM i) (wordPR prS (mInS.getD i.val []))

@[expose] def mConjCheck : Bool :=
  (List.finRange 2).all fun i => (List.finRange 6).all fun j =>
    PR.eq ((prM i).conj (prE j)) (prIota (actP i j))

@[expose] def rConjCheck : Bool :=
  (List.finRange 12).all fun k => (List.finRange 6).all fun j =>
    PR.eq ((prR k).conj (prE j)) (prIota (actR k j))

@[expose] def decCheck : Bool :=
  (List.finRange 2).all fun s => (List.finRange 12).all fun k => (List.finRange 2).all fun j =>
    PR.eq (((prNs s).mul (prR k)).mul (prE0.pow j.val))
      ((((prR (decSigma s k j)).mul (prIota (decU s k j))).mul
        (prTau.pow (decEps s k j))).mul (prWM (decRec s k j).2.2.2))

end CFSG.Monster.GMS.Griess13.Co1Data
