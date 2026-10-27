module

public import CFSG.Monster.GMS.Griess13.DataPacked

@[expose] public section

namespace CFSG.Monster.GMS.Griess13.Co1Data

open scoped Matrix
open CFSG.Blueprint.NativeSporadic (decode)
open CFSG.Sporadic.SmallF2 (rowsMatrix rowsMatrix_mulRows rowsMatrix_idRows rowsMatrix_powRows
  rowsMatrix_apply rowsMatrix_rowsOfPayload toVecD toVecD_apply toVecD_xor toVecD_zero
  foldl_xor_toVecD ofBits_testBit)
open CFSG.Sporadic.SmallF2.Native (mulRows idRows powRows rowsOfPayload ofBits)

@[expose] def gCheck : Bool :=
  PR.eq (prG.pow 7) PR.one && !PR.eq prG PR.one &&
    (List.finRange 3).all fun k => PR.eq ((prG.mul (prX k)).mul prG.inv) (prY k)

@[expose] def tmatPay (i : ℕ) : String := "T\n" ++ (tmatBits.drop (576 * i)).take 576

@[expose] def trows (i : ℕ) : Array ℕ := rowsOfPayload 24 (tmatPay i)

@[expose] def freeCheck : Bool :=
  (List.finRange 8).all fun i => (List.finRange 8).all fun j =>
    ((trows i.val)[freePos.getD j.val 0 / 24]?.getD 0).testBit (freePos.getD j.val 0 % 24) ==
      decide (i = j)

@[expose] def oneCheck : Bool := eqRows (trows 7) (idRows 24)

@[expose] def commuteCheck : Bool :=
  (List.finRange 8).all fun i => (List.finRange 3).all fun k =>
    eqRows (mulRows 24 (trows i.val) (prX k).r) (mulRows 24 (prX k).r (trows i.val))

@[expose] def eqCoeff (X : Array ℕ) (i j a : ℕ) : Bool :=
  ((a / 24 == i) && ((X[a % 24]?.getD 0).testBit j)) !=
    ((a % 24 == j) && ((X[i]?.getD 0).testBit (a / 24)))

@[expose] def eqMask (X : Array ℕ) (i j : ℕ) : ℕ := ofBits 576 (eqCoeff X i j)

@[expose] def eqAt (Xs : List (Array ℕ)) (r : ℕ) : ℕ :=
  eqMask (Xs.getD (r / 576) #[]) (r % 576 / 24) (r % 24)

@[expose] def eqsOf (Xs : List (Array ℕ)) : Array ℕ := Array.ofFn (n := 1728) fun r => eqAt Xs r.val

@[expose] def fmaskOf (free : List ℕ) : ℕ := free.foldl (fun m f => m ||| (1 <<< f)) 0

@[expose] def gaussJordan (rows0 : Array ℕ) (fmask : ℕ) : Array ℕ × Array ℕ := Id.run do
  let mut rows := rows0
  let mut piv : Array ℕ := Array.replicate 576 0
  let mut r := 0
  for c in [0:576] do
    if !fmask.testBit c then
      let mut p := r
      while p < rows.size && !(rows[p]!.testBit c) do
        p := p + 1
      if p < rows.size then
        let tmp := rows[p]!
        rows := rows.set! p rows[r]!
        rows := rows.set! r tmp
        let pr := rows[r]!
        for i in [0:rows.size] do
          if i != r && rows[i]!.testBit c then
            rows := rows.set! i (rows[i]! ^^^ pr)
        piv := piv.set! c (r + 1)
        r := r + 1
  return (rows, piv)

@[expose] def certOf (gj : Array ℕ × Array ℕ) (a : ℕ) : ℕ × ℕ :=
  let row := gj.1[gj.2[a]! - 1]!
  (row >>> 576, (row % 2 ^ 576) ^^^ (1 <<< a))

@[expose] def foldXor (eqs : Array ℕ) (μ : ℕ) : ℕ :=
  (List.range eqs.size).foldl (fun acc r => if μ.testBit r then acc ^^^ eqs[r]! else acc) 0

@[expose] def verifyCert (eqs : Array ℕ) (fmask a : ℕ) (cert : ℕ × ℕ) : Bool :=
  foldXor eqs cert.1 == ((1 <<< a) ^^^ cert.2) && (cert.2 ||| fmask) == fmask

@[expose] def spanCheckWith (eqs : Array ℕ) (fmask : ℕ) (cert : ℕ → ℕ × ℕ) : Bool :=
  (List.range 576).all fun a => fmask.testBit a || verifyCert eqs fmask a (cert a)

@[expose] def spanCheck (Xs : List (Array ℕ)) (free : List ℕ) : Bool :=
  let eqs := eqsOf Xs
  let fmask := fmaskOf free
  let gj := gaussJordan ((Array.range eqs.size).map fun r => eqs[r]! ||| (1 <<< (576 + r))) fmask
  spanCheckWith eqs fmask (certOf gj)

@[expose] def xRows :
    List (Array ℕ) := [(prX 0).r, (prX 1).r, (prX 2).r]

@[expose] def cF (c : Fin 8 → ZMod 2) (i : ℕ) : ZMod 2 := if h : i < 8 then c ⟨i, h⟩ else 0

@[expose] def comboRows (c : Fin 8 → ZMod 2) : Array ℕ :=
  Array.ofFn (n := 24) fun a =>
    (List.range 8).foldl
      (fun acc i => if cF c i = 1 then acc ^^^ ((trows i)[a.val]?.getD 0) else acc) 0

@[expose] def abCheck : Bool :=
  PR.eq prA (prAB.getD 0 PR.one) && PR.eq prB (prAB.getD 1 PR.one)

end CFSG.Monster.GMS.Griess13.Co1Data
