
module

public import Std.Data.HashMap
public import CFSG.Sporadic.Schreier.TitsCentralCheck
public import CFSG.Quasithin.Recognition.CertTitsJCheckBase
public import CFSG.Quasithin.Recognition.CertVertexTable2
public import CFSG.Quasithin.Recognition.CertDataTitsOuter
public meta import Std.Data.HashMap
public meta import CFSG.Sporadic.Schreier.TitsData
public meta import CFSG.Sporadic.Schreier.TitsArrays
public meta import CFSG.Sporadic.Schreier.TitsBasic
public meta import CFSG.Sporadic.Schreier.TitsCertCheck
public meta import CFSG.Sporadic.Schreier.TitsLocalCheck
public meta import CFSG.Sporadic.Schreier.TitsActionCheck
public meta import CFSG.Sporadic.Schreier.TitsOrbit
public meta import CFSG.Sporadic.Schreier.TitsStabCheck
public meta import CFSG.Sporadic.Schreier.TitsEnum
public meta import CFSG.Sporadic.Schreier.TitsCentralCheck
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public meta import CFSG.Quasithin.Recognition.CertTitsEnum4
public meta import CFSG.Quasithin.Recognition.CertVertexTable
public meta import CFSG.Quasithin.Recognition.CertVertexTable2
public meta import CFSG.Quasithin.Recognition.CertTitsJCheckBase
public meta import CFSG.Quasithin.Recognition.CertDataTitsOuter

public section

namespace CFSG.Quasithin

open CFSG.Certificates.Native CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Tits

@[expose] def piInv : Array ℕ := invCand 1755 titsPiArr

@[expose] def pPel : Array (Array ℕ) := Array.ofFn (n := 1024) fun i =>
  if i.val < 512 then jPel[i.val]! else compA 1755 jPel[i.val - 512]! titsPiArr

@[expose] def pIdxMap : Std.HashMap ℕ ℕ :=
  (List.range 1024).foldl
    (fun m i => m.insert (jKey4 (pPel[i]!)[5]! (pPel[i]!)[1]! (pPel[i]!)[24]! (pPel[i]!)[12]!) i) {}

@[expose] def pIdx4 (x0 x1 x2 x3 : ℕ) : ℕ := pIdxMap.getD (jKey4 x0 x1 x2 x3) 0

@[expose] def pIdx (a : Array ℕ) : ℕ := pIdx4 a[5]! a[1]! a[24]! a[12]!

@[expose] def pMulT : Array (Array ℕ) :=
  Array.ofFn (n := 1024) fun i => Array.ofFn (n := 1024) fun j =>
    pIdx4 (pPel[i]!)[(pPel[j]!)[5]!]! (pPel[i]!)[(pPel[j]!)[1]!]! (pPel[i]!)[(pPel[j]!)[24]!]!
      (pPel[i]!)[(pPel[j]!)[12]!]!

@[expose] def pInvT : Array ℕ := Array.ofFn (n := 1024) fun i => pIdx (invCand 1755 pPel[i]!)

@[expose] def pOneI : ℕ := pIdx (idA 1755)

@[expose] def pZI : ℕ := pIdx jZArr

@[expose] def pOps : VOps 1024 where
  mul i j := finPt 1024 (pMulT[(i : ℕ)]!)[(j : ℕ)]!
  inv i := finPt 1024 pInvT[(i : ℕ)]!
  one := finPt 1024 pOneI
  zI := finPt 1024 pZI

@[expose] def pEBarr : Array Bool := Array.ofFn (n := 1024) fun i =>
  decide (∀ j : Fin 1024, pOps.comm i j = pOps.one ∨ pOps.comm i j = pOps.zI)

@[expose] def pEB (i : Fin 1024) : Bool := pEBarr[(i : ℕ)]!

@[expose] def pFBarr : Array Bool := Array.ofFn (n := 1024) fun i =>
  decide (∀ e : Fin 1024, pEB e = true → pOps.mul i e = pOps.mul e i)

@[expose] def pFB (i : Fin 1024) : Bool := pFBarr[(i : ℕ)]!

@[expose] def pRB (i : Fin 1024) : Bool := decide (i.val < 512)

@[expose] def pGenArrs : Array (Array ℕ) := jGenArrs.push titsPiArr

@[expose] def pGenInvArrs : Array (Array ℕ) := pGenArrs.map (invCand 1755)

@[expose] def pCjT : Array (Array ℕ) :=
  Array.ofFn (n := 4) fun k => Array.ofFn (n := 1024) fun i =>
    pIdx (compA 1755 (compA 1755 pGenArrs[(k : ℕ)]! pPel[i]!) pGenInvArrs[(k : ℕ)]!)

@[expose] def pCj (k : Fin 4) (i : Fin 1024) : Fin 1024 := finPt 1024 (pCjT[(k : ℕ)]!)[(i : ℕ)]!

@[expose] def pCcT : Array ℕ :=
  Array.ofFn (n := 1024) fun i => pIdx (compA 1755 (compA 1755 jCArr pPel[i]!) jCInv)

@[expose] def pCc (i : Fin 1024) : Fin 1024 := finPt 1024 pCcT[(i : ℕ)]!

@[expose] def pI0N : ℕ :=
  ((List.range 1024).find? fun i => !(pFBarr[i]!) && (pMulT[i]!)[i]! == pOneI).getD 0

@[expose] def pBfs : Array ℕ × Array ℕ := Id.run do
  let mut par : Array ℕ := Array.replicate 1024 1024
  let mut gl : Array ℕ := Array.replicate 1024 0
  let mut queue : Array ℕ := #[pI0N]
  par := par.set! pI0N pI0N
  let mut head := 0
  for _ in [0:1024] do
    if head < queue.size then
      let x := queue[head]!
      head := head + 1
      for k in [0:4] do
        let y := (pCjT[k]!)[x]!
        if par[y]! == 1024 then
          par := par.set! y x
          gl := gl.set! y k
          queue := queue.push y
  return (par, gl)

@[expose] def pWordAux (par gl : Array ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | fuel + 1, j =>
    if j == pI0N then [] else if par[j]! == 1024 then [] else gl[j]! :: pWordAux par gl fuel par[j]!

@[expose] def pWtab (j : Fin 1024) : List (Fin 4) :=
  (pWordAux pBfs.1 pBfs.2 1200 (j : ℕ)).map (finPt 4)

@[expose] def pI0 : Fin 1024 := finPt 1024 pI0N

@[expose] def conjPi (g : Array ℕ) : Array ℕ := compA 1755 (compA 1755 titsPiArr g) piInv

end CFSG.Quasithin
