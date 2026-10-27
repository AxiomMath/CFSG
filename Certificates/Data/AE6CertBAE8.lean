module

public import Certificates.Data.AE6ModelSmall
public import Certificates.Data.TwinPerpV3A6iCurtisPerm
public import CFSG.ClassicalInvolution.Q3.AE.Wreath

public section

namespace Certificates.AE6CertB

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.Sporadic.Th.Native CFSG.Monster.B.Co2.Native CFSG.EvenSmallLie.OmegaEight
  Certificates.AE6Model Certificates.S7Twin CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6

@[expose] def wrAct (a : AE.Wr 8) : Equiv.Perm (Fin 8 × ZMod 2) :=
  Equiv.prodShear a.perm fun i => Equiv.addRight (a.vec (a.perm i))

@[expose] def wrPt : Fin 8 × ZMod 2 ≃ Fin 16 := finProdFinEquiv

@[expose] def wr16 (a : AE.Wr 8) : Equiv.Perm (Fin 16) := wrPt.permCongr (wrAct a)

@[expose] def ae8Gen : Fin 7 → AE.Wr 8 :=
  ![⟨![0, 0, 1, 0, 0, 1, 1, 1], 1⟩,
    ⟨![1, 1, 0, 0, 1, 1, 0, 0], Equiv.swap 0 1 * Equiv.swap 2 7 * Equiv.swap 3 6 * Equiv.swap 4 5⟩,
    ⟨![1, 1, 0, 0, 0, 0, 1, 1], Equiv.swap 0 1 * Equiv.swap 2 5 * Equiv.swap 3 4 * Equiv.swap 6 7⟩,
    ⟨![1, 0, 0, 1, 0, 1, 0, 1], Equiv.swap 0 5 * Equiv.swap 1 2 * Equiv.swap 3 7 * Equiv.swap 4 6⟩,
    ⟨![0, 1, 0, 0, 1, 0, 1, 1], Equiv.swap 0 2 * Equiv.swap 1 7 * Equiv.swap 3 5 * Equiv.swap 4 6⟩,
    ⟨![1, 0, 1, 1, 0, 0, 0, 1], Equiv.swap 0 2 * Equiv.swap 1 5 * Equiv.swap 3 7 * Equiv.swap 4 6⟩,
    ⟨![1, 0, 0, 1, 0, 1, 0, 1], Equiv.swap 0 7 * Equiv.swap 1 2 * Equiv.swap 3 5 * Equiv.swap 4 6⟩]

@[expose] def ae8Letter : List ℕ := [0, 2, 3, 4, 5, 6, 7]

@[expose] def ae8Gens16 (_ : Unit := ()) : List (Equiv.Perm (Fin 16)) :=
  (List.ofFn ae8Gen).map fun a => tab (wr16 a)

@[expose] def ae8Derive : List (List ℤ) :=
  [[-4, 7], [-6, 5, 1], [-8, -9, 8, 9, 8], [-1, -2, 1, 2], [-11, -10, -11, -8, -11, 8, 9],
    [-12, -10, 12, 10], [-10, -11, -10, -8, -11, -1, -4, 5, 2], [-13, -12, 14, 12, 14],
    [-12, -14, -10, 14, -8, -9, 14, 9, 8], [-3, 8, 2], [17, 14, 10], [-18, -16, -14, 18]]

@[expose] def ae8Q (_ : Unit := ()) : RawSchreierDatum 16 :=
  certificate (by decide) (ae8Gens16 ()) ae8Derive #v[4, 0, 2, 6, 12, 10, 8] (by decide)

@[expose] def v0Gens (_ : Unit := ()) : List (Equiv.Perm (Fin 360)) :=
  let G := curtisPerms ()
  ae8Letter.map fun i => G.getD i 1

@[expose] def v0Derive : List (List ℤ) :=
  [[-2, 4, 2], [-8, 6, 8], [-6, -2, 6, 2], [-5, 3, 5], [-7, 3, 7]]

@[expose] def v0Q (_ : Unit := ()) : RawSchreierDatum 360 :=
  certificate (by decide) (v0Gens ()) v0Derive #v[0, 2, 1, 4, 24, 8] (by decide)

@[expose] def sumPerm (a : Equiv.Perm (Fin 16)) (b : Equiv.Perm (Fin 360)) :
    Equiv.Perm (Fin 376) :=
  (finSumFinEquiv : Fin 16 ⊕ Fin 360 ≃ Fin 376).permCongr (Equiv.Perm.sumCongr a b)

@[expose] def grGens (_ : Unit := ()) : List (Equiv.Perm (Fin 376)) :=
  let G := curtisPerms ()
  (List.ofFn fun i : Fin 7 => tab (sumPerm (wr16 (ae8Gen i)) (G.getD (ae8Letter.getD i 0) 1))) ++
    [tab (sumPerm (wr16 (AE.Wr.allOnes 8)) 1)]

@[expose] def grDerive : List (List ℤ) :=
  [[-4, 7], [-1, 8], [-10, -6, 5, 1], [-1, -2, 1, 2], [-12, -11, -12, -11, -9, -10, 12, 9],
    [-11, 13, 11], [-9, -10, -1, -4, 5, 2], [-13, -12, -15, 14, 15],
    [-15, -11, -15, -9, -11, 15, 11, 9], [-3, 9, 2], [18, 15, 11], [-19, -15, 17, 19],
    [17, 20, 17]]

@[expose] def grQ (_ : Unit := ()) : RawSchreierDatum 376 :=
  certificate (by decide) (grGens ()) grDerive #v[4, 0, 2, 6, 10, 12, 8] (by decide)

@[expose] def ae8Chains (_ : Unit := ()) : Bool :=
  let A := ae8Q ()
  let V := v0Q ()
  let R := grQ ()
  A.check && A.orderCertificate == 2580480 && V.check && V.orderCertificate == 1290240 &&
    R.check && R.orderCertificate == 2580480

@[expose] def kQ8 (_ : Unit := ()) : Bool :=
  let K := k0Gens ()
  let x := K.getD 0 1
  let y := K.getD 1 1
  q8RelT 360 (toTable x) (toTable x⁻¹) (toTable y) (toTable y⁻¹)

@[expose] def ae8KWords : List (List ℕ) :=
  [[2, 4, 2, 0, 2, 6, 2, 4, 2, 0, 2, 6], [0, 2, 4, 0, 2, 0, 6, 2, 0, 2, 4, 2, 6],
    [2, 4, 2, 0, 2, 6, 2, 4, 2, 0, 2, 6, 0, 2, 4, 0, 2, 0, 6, 2, 0, 2, 4, 2, 6]]

@[expose] def ae8DiagMap : List (List ℕ) := [[4, 5, 2, 3, 0, 1, 6, 7], [6, 7, 2, 3, 4, 5, 0, 1]]

@[expose] def ae8TwinLetter : List ℕ := [6, 4]

@[expose] def diagArrs (d : List ℕ) : Array (Array ℕ) := (d.map fun i => genArrs[i]!).toArray

@[expose] def diagRels (_ : Unit := ()) : Bool :=
  allLt 8 (fun i => isInvA 360 genArrs[i]! (invCand 360 genArrs[i]!)) &&
    ae8DiagMap.all fun d =>
      let gs := diagArrs d
      curtisPG.all fun w => eqA 360 (curtisWordArr gs w) (idA 360)

@[expose] def diagTwins (_ : Unit := ()) : Bool :=
  let G := curtisPerms ()
  let K := k0Gens ()
  let sp := spanQ (toTable (K.getD 0 1)) (toTable (K.getD 1 1))
  (List.range 2).all fun c =>
    let d := ae8DiagMap.getD c []
    let h := G.getD (ae8TwinLetter.getD c 0) 1
    ae8KWords.all fun w => memT 360 sp (toTable (h⁻¹ * aeWord G (w.map fun i => d.getD i 0) * h))

end Certificates.AE6CertB
