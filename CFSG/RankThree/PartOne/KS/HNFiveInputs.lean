module

public import CFSG.Sporadic.GLQ.RegisterProgram
public meta import CFSG.Sporadic.GLQ.RegisterProgram
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsFp
public meta import Certificates.Data.CFSGNative.SectionRank.Fp
public import CFSG.Blueprint.MatrixSeedIdentification
import CFSG.Blueprint.NativeSporadic
public meta import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public meta import CFSG.Open.Defs
public import CFSG.Open.Defs

public section

namespace CFSG.RankThree.PartOne.KS.HNFive

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.Blueprint CFSG.Sporadic.GLQ

@[expose] def hnFiveProg : List Instr := [
  .iv 2 3, .mu 2 1 103, .mu 103 2 103, .mu 103 1 103, .mu 103 3 103, .mu 103 1 103, .mu 103 3 103,
  .mu 103 1 103, .mu 103 2 103, .mu 103 1 103, .mu 103 3 103, .mu 103 1 103, .mu 103 3 103,
  .mu 103 1 103, .mu 103 3 103, .mu 103 1 103, .mu 103 3 103, .mu 103 1 103, .mu 103 2 103,
  .mu 103 1 103, .mu 103 3 103, .mu 103 1 103, .mu 103 2 103, .mu 103 1 103, .mu 103 2 103,
  .mu 103 1 103, .mu 103 2 103, .mu 103 1 103, .mu 103 2 103, .mu 103 1 103, .mu 103 3 103,
  .mu 103 1 103, .mu 103 2 103, .mu 103 1 103, .mu 103 3 103, .mu 103 1 103, .mu 103 2 103,
  .mu 103 1 103, .mu 103 3 103, .mu 103 1 103, .mu 103 3 103, .mu 103 1 103, .mu 103 2 103,
  .mu 103 1 103, .mu 103 3 103, .mu 103 1 103, .mu 103 3 103, .mu 103 1 103, .mu 103 3 103,
  .mu 103 1 103, .mu 103 3 103, .mu 103 1 103, .mu 103 3 103, .mu 103 1 103, .mu 103 3 103,
  .mu 103 1 103, .mu 103 3 103, .mu 103 1 103, .mu 103 3 103, .mu 103 1 103, .mu 103 3 103,
  .mu 103 1 103, .mu 103 2 103, .mu 103 1 103, .mu 103 2 103, .mu 103 1 103, .mu 103 2 103,
  .mu 103 1 103, .mu 103 2 103, .mu 103 1 103, .mu 103 3 103, .mu 103 1 103, .mu 103 3 103,
  .mu 103 1 103, .mu 103 2 103, .mu 103 1 103, .mu 103 3 103, .mu 103 1 103, .mu 103 3 103,
  .mu 103 1 103, .mu 103 3 103, .mu 103 1 103, .mu 103 2 103, .mu 103 1 103, .mu 103 3 103,
  .mu 103 1 103, .mu 103 3 103, .mu 103 1 103, .mu 103 3 103, .mu 103 1 103, .mu 103 2 103,
  .mu 103 1 103, .mu 103 3 103, .mu 103 1 103, .mu 103 2 103, .mu 103 1 103, .mu 103 3 103,
  .mu 103 1 103, .mu 103 3 103, .mu 103 1 103, .mu 103 3 103, .mu 1 3 203, .mu 203 1 203,
  .mu 203 2 203, .mu 203 1 203, .mu 203 2 203, .mu 203 1 203, .mu 203 3 203, .mu 203 1 203,
  .mu 203 2 203, .mu 203 1 203, .mu 203 3 203, .mu 203 1 203, .mu 203 3 203, .mu 203 1 203,
  .mu 203 2 203, .mu 203 1 203, .mu 203 3 203, .mu 203 1 203, .mu 203 2 203, .mu 203 1 203,
  .mu 203 3 203, .mu 203 1 203, .mu 203 3 203, .mu 203 1 203, .mu 203 3 203, .mu 203 1 203,
  .mu 203 3 203, .mu 203 1 203, .mu 203 2 203, .mu 203 1 203, .mu 203 2 203, .mu 203 1 203,
  .mu 203 3 203, .mu 203 1 203, .mu 203 2 203, .mu 203 1 203, .mu 203 2 203, .mu 203 1 203,
  .mu 203 2 203, .mu 203 1 203, .mu 203 2 203, .mu 203 1 203, .mu 203 3 203, .mu 203 1 203,
  .mu 203 3 203, .mu 203 1 203, .mu 203 3 203, .mu 203 1 203, .mu 203 2 203, .mu 203 1 203,
  .mu 203 3 203, .mu 203 1 203, .mu 203 2 203, .mu 203 1 203, .mu 203 2 203, .mu 203 1 203,
  .mu 203 2 203, .mu 203 1 203, .mu 203 3 203, .mu 203 1 203, .mu 203 3 203, .mu 203 1 203,
  .mu 203 3 203, .mu 203 1 203, .mu 203 3 203, .mu 203 1 203, .mu 203 2 203, .mu 203 1 203,
  .mu 203 3 203, .mu 203 1 203, .mu 203 3 203, .mu 203 1 203, .mu 203 2 203, .mu 203 1 203,
  .mu 203 2 203, .mu 203 1 203, .mu 203 2 203, .mu 203 1 203, .mu 203 2 203, .mu 203 1 203,
  .mu 203 3 203, .mu 203 1 203, .mu 203 2 203, .mu 203 1 203, .mu 203 3 203, .mu 203 1 203,
  .mu 203 2 203, .mu 203 1 203, .mu 203 2 203, .mu 203 1 203, .mu 203 3 203, .mu 203 1 203,
  .mu 203 2 203, .mu 203 1 203, .mu 203 3 203, .mu 203 1 203, .mu 203 3 203, .mu 203 1 203,
  .mu 203 2 203, .mu 203 1 203, .iv 103 204, .iv 203 205, .mu 204 203 222, .mu 222 204 222,
  .mu 222 204 222, .mu 222 203 222, .mu 222 204 222, .mu 222 204 222, .mu 222 203 222,
  .mu 222 204 222, .mu 222 203 222, .mu 222 103 222, .mu 222 203 222, .mu 222 204 222,
  .mu 222 204 222, .mu 222 204 222, .mu 222 203 222, .mu 222 204 222, .mu 222 204 222,
  .mu 204 204 241, .mu 241 203 241, .mu 241 204 241, .mu 241 204 241, .mu 241 204 241,
  .mu 241 204 241, .mu 241 203 241, .mu 241 204 241, .mu 241 203 241, .mu 241 103 241,
  .mu 241 103 241, .mu 241 203 241, .mu 241 103 241, .mu 241 103 241, .mu 241 103 241,
  .mu 241 103 241, .mu 241 203 241, .mu 241 103 241, .mu 241 203 241, .mu 203 204 257,
  .mu 257 204 257, .mu 257 203 257, .mu 257 103 257, .mu 257 103 257, .mu 257 103 257,
  .mu 257 203 257, .mu 257 204 257, .mu 257 204 257, .mu 257 204 257, .mu 257 204 257,
  .mu 257 203 257, .mu 257 103 257, .mu 257 103 257, .mu 257 203 257, .mu 257 103 257,
  .mu 204 203 272, .mu 272 204 272, .mu 272 203 272, .mu 272 103 272, .mu 272 103 272,
  .mu 272 103 272, .mu 272 103 272, .mu 272 103 272, .mu 272 203 272, .mu 272 103 272,
  .mu 272 203 272, .mu 272 204 272, .mu 272 204 272, .mu 272 204 272, .mu 272 204 272,
  .pwr 2 103 273, .mu 204 203 275, .mu 275 103 275, .mu 203 275 276, .pwr 2 276 277, .iv 222 278,
  .iv 241 279, .mu 278 279 282, .mu 282 222 282, .mu 282 241 282]

@[expose] def hnFiveN : ℕ := 283

@[expose] def iZ : ℕ := 282

@[expose] def iX : ℕ := 273

@[expose] def iQ : Fin 4 → ℕ := ![222, 241, 257, 272]

@[expose] def iR : Fin 3 → ℕ := ![203, 275, 277]

@[expose] def exM : Fin 4 → Fin 4 → ℕ := ![![0, 1, 0, 0], ![4, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 4, 0]]

@[expose] def exX : Fin 4 → Fin 4 → ℕ := ![![1, 1, 4, 2], ![3, 4, 1, 3], ![3, 0, 0, 2], ![2, 0, 2, 4]]

@[expose] def cx : Fin 4 → ℕ := ![1, 0, 1, 4]

@[expose] def exR : Fin 3 → Fin 4 → Fin 4 → ℕ := ![![![0, 0, 1, 1], ![0, 0, 0, 1], ![1, 4, 0, 0], ![0, 1, 0, 0]], ![![3, 0, 1, 2], ![0, 3, 2, 1], ![1, 3, 2, 0], ![3, 1, 0, 2]], ![![4, 0, 0, 0], ![0, 4, 0, 0], ![0, 0, 4, 0], ![0, 0, 0, 4]]]

@[expose] def cr : Fin 3 → Fin 4 → ℕ := ![![2, 2, 0, 3], ![0, 3, 0, 2], ![4, 0, 3, 1]]

@[expose] def zWit : ℕ := 0

@[expose] def hnFiveRegs : Array (Array (Array ℕ) × Array (Array ℕ)) :=
  runProgN (opsP 5 133) (initRegsN (opsP 5 133) hnFiveN
    ((opsP 5 133).decode NativeSporadic.HNSeed1, (opsP 5 133).decode NativeSporadic.HNSeed1)
    ((opsP 5 133).decode NativeSporadic.HNSeed2,
      (opsP 5 133).pow ((opsP 5 133).decode NativeSporadic.HNSeed2) 2)) hnFiveProg

section Native

variable {M V : Type} (O : Ops M V)

@[expose] def allFin (n : ℕ) (f : Fin n → Bool) : Bool := (List.finRange n).all f

@[expose] def powOK (X : M) (e : ℕ) : Bool := O.eq (O.pow X e) O.one

@[expose] def commOK (X Y : M) : Bool := O.eq (O.mul X Y) (O.mul Y X)

@[expose] def neOne (X : M) (t : ℕ) : Bool := O.vne (O.vmul (O.unit t) X) (O.unit t)

@[expose] def pBcomm (a b : M × M) : M := O.mul (O.mul a.2 b.2) (O.mul a.1 b.1)

@[expose] def pConj (g a : M × M) : M := O.mul (O.mul g.2 a.1) g.1

@[expose] def prodPow (qs : Fin 4 → M) (z : M) (a : Fin 4 → ℕ) (c : ℕ) : M :=
  O.mul (O.mul (O.pow (qs 0) (a 0)) (O.mul (O.pow (qs 1) (a 1))
    (O.mul (O.pow (qs 2) (a 2)) (O.mul (O.pow (qs 3) (a 3)) O.one)))) (O.pow z c)

variable [Inhabited M]

@[expose] def relsOK (R : Array (M × M)) : Bool :=
  powOK O R[iZ]!.1 5 && neOne O R[iZ]!.1 zWit &&
  allFin 4 (fun j => powOK O R[iQ j]!.1 5 && commOK O R[iQ j]!.1 R[iZ]!.1) &&
  allFin 4 (fun i => allFin 4 (fun j =>
    O.eq (pBcomm O R[iQ i]! R[iQ j]!) (O.pow R[iZ]!.1 (exM i j)))) &&
  powOK O R[iX]!.1 5 && commOK O R[iX]!.1 R[iZ]!.1 &&
  allFin 4 (fun i => O.eq (pConj O R[iX]! R[iQ i]!)
    (prodPow O (fun j => R[iQ j]!.1) R[iZ]!.1 (exX i) (cx i))) &&
  allFin 3 (fun j => commOK O R[iR j]!.1 R[iZ]!.1 &&
    allFin 4 (fun i => O.eq (pConj O R[iR j]! R[iQ i]!)
      (prodPow O (fun l => R[iQ l]!.1) R[iZ]!.1 (exR j i) (cr j i))))

end Native

@[expose] def hnFiveCheck : Bool :=
  hnFiveProg.all (Instr.lt hnFiveN) && relsOK (opsP 5 133) hnFiveRegs

end CFSG.RankThree.PartOne.KS.HNFive
