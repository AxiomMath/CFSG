module

public import Certificates.Data.CFSGNative.GF2W1112.Spin

public section

namespace CFSG.GF2W1112

open CFSG.Sporadic.SmallF2.Native

@[expose] def w12UEqR (X Y : Array Nat) : Bool :=
  (List.range 22).all fun i => (X[i]?.getD 0) % 2 ^ 22 == (Y[i]?.getD 0) % 2 ^ 22

@[expose] def w12UEqCoeff (X Z : Array Nat) (i j a : Nat) : Bool :=
  ((a / 22 == i) && ((X[a % 22]?.getD 0).testBit j)) !=
    ((a % 22 == j) && ((Z[i]?.getD 0).testBit (a / 22)))

@[expose] def w12UEqMask (X Z : Array Nat) (i j : Nat) : Nat := ofBits 484 (w12UEqCoeff X Z i j)

@[expose] def w12UEqAt (Xs Zs : List (Array Nat)) (r : Nat) : Nat :=
  w12UEqMask (Xs.getD (r / 484) #[]) (Zs.getD (r / 484) #[]) (r % 484 / 22) (r % 22)

@[expose] def w12UEqsOf (Xs Zs : List (Array Nat)) : Array Nat :=
  Array.ofFn (n := 1452) fun r => w12UEqAt Xs Zs r.val

@[expose] def w12UFmaskOf (free : List Nat) : Nat := free.foldl (fun m f => m ||| (1 <<< f)) 0

@[expose] def w12UGaussJordan (rows0 : Array Nat) (fmask : Nat) : Array Nat × Array Nat :=
  Id.run do
    let mut rows := rows0
    let mut piv : Array Nat := Array.replicate 484 0
    let mut r := 0
    for c in [0:484] do
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

@[expose] def w12UCertOf (gj : Array Nat × Array Nat) (a : Nat) : Nat × Nat :=
  let row := gj.1[gj.2[a]! - 1]!
  (row >>> 484, (row % 2 ^ 484) ^^^ (1 <<< a))

@[expose] def w12UFoldXor (eqs : Array Nat) (μ : Nat) : Nat :=
  (List.range eqs.size).foldl (fun acc r => if μ.testBit r then acc ^^^ eqs[r]! else acc) 0

@[expose] def w12UVerifyCert (eqs : Array Nat) (fmask a : Nat) (cert : Nat × Nat) : Bool :=
  w12UFoldXor eqs cert.1 == ((1 <<< a) ^^^ cert.2) && (cert.2 ||| fmask) == fmask

@[expose] def w12USpanCheckWith (eqs : Array Nat) (fmask : Nat) (cert : Nat → Nat × Nat) : Bool :=
  (List.range 484).all fun a => fmask.testBit a || w12UVerifyCert eqs fmask a (cert a)

@[expose] def w12USpanCheck (Xs Zs : List (Array Nat)) (free : List Nat) (_ : Unit := ()) : Bool :=
  let eqs := w12UEqsOf Xs Zs
  let fmask := w12UFmaskOf free
  let gj := w12UGaussJordan
    ((Array.range eqs.size).map fun r => eqs[r]! ||| (1 <<< (484 + r))) fmask
  w12USpanCheckWith eqs fmask (w12UCertOf gj)

@[expose] def w12UFreeCheck (Bs : Array (Array Nat)) (free : List Nat) : Bool :=
  (List.range 11).all fun i => (List.range 11).all fun j =>
    ((Bs[i]!)[free.getD j 0 / 22]?.getD 0).testBit (free.getD j 0 % 22) == decide (i = j)

@[expose] def w12USolCheck (Bs : Array (Array Nat)) (Xs Zs : List (Array Nat)) : Bool :=
  (List.range 11).all fun i => (List.range 3).all fun k =>
    w12UEqR (mulRows 22 (Bs[i]!) (Xs.getD k #[])) (mulRows 22 (Zs.getD k #[]) (Bs[i]!))

@[expose] def w12UCombo (Bs : Array (Array Nat)) (cc : Nat) : Array Nat :=
  Array.ofFn (n := 22) fun a =>
    (List.range 11).foldl
      (fun acc i => if cc.testBit i then acc ^^^ ((Bs[i]!)[a.val]?.getD 0) else acc) 0

@[expose] def w12UWordEval (G1 G2 : Array Nat) (w : List (Nat × Nat)) : Array Nat :=
  w.foldl (fun acc q => mulRows 22 acc (powRows 22 (if q.1 == 0 then G1 else G2) q.2)) (idRows 22)

@[expose] def w12URels (X1 X2 M : Array Nat) (tw : List (List (Nat × Nat))) (kk : List Nat) :
    Bool :=
  (tw.zip kk).all fun p =>
    w12UEqR (powRows 22 (mulRows 22 (w12UWordEval X1 X2 p.1) M) p.2) (idRows 22)

@[expose] def w12UEnum (Bs : Array (Array Nat)) (X1s X2s : Array (Array Nat))
    (tw : List (List (Nat × Nat))) (kk : List Nat) (Qs : Array (Array Nat))
    (X01 X02 M0 : Array Nat) : Bool :=
  w12AllLoop (fun cc =>
    let M := w12UCombo Bs cc
    !(w12UEqR (powRows 22 M 3) (idRows 22)) ||
      w12AllLoop (fun c1 => w12AllLoop (fun c2 =>
        !(w12URels (X1s[c1]!) (X2s[c2]!) M tw kk) ||
          Qs.any fun Q =>
            w12UEqR (mulRows 22 Q (X1s[c1]!)) (mulRows 22 X01 Q) &&
              w12UEqR (mulRows 22 Q (X2s[c2]!)) (mulRows 22 X02 Q) &&
              w12UEqR (mulRows 22 Q M) (mulRows 22 M0 Q)) 16 0) 16 0) 2048 0

end CFSG.GF2W1112
