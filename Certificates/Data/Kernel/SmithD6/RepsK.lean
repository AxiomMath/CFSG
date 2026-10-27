module

public import Certificates.Data.SmithD6Facts
public import Certificates.Data.Kernel.SmithD6.Trees

public section

namespace CFSG.KD.SmithD6Reps

open CFSG.SmithD6

@[expose] def tvColsP (p : Nat × Nat) : Array Nat :=
  let A := (bitsOf p.1).foldl
    (fun acc i => (bitsOf p.2).foldl (fun acc j => acc ^^^ pairMat[i * 12 + j]!) acc) 0
  Array.ofFn (n := 32) fun c => ((A >>> (32 * c.val)) &&& 0xFFFFFFFF) ^^^ 2 ^ c.val

@[expose] def commL (A B : Array Nat) : Bool :=
  (List.range 32).all fun m => mf7Ap A B[m]! == mf7Ap B A[m]!

@[expose] def braidL (A B : Array Nat) : Bool :=
  (List.range 32).all fun m => mf7Ap A (mf7Ap B A[m]!) == mf7Ap B (mf7Ap A B[m]!)

@[expose] def dihL (A B : Array Nat) : Bool :=
  (List.range 32).all fun m =>
    mf7Ap A (mf7Ap B (mf7Ap A B[m]!)) == mf7Ap B (mf7Ap A (mf7Ap B A[m]!))

@[expose] def kindL (A B : Array Nat) : Nat :=
  if commL A B then 0 else if braidL A B then 1 else 2

@[expose] def relL (k : Nat) (A B : Array Nat) : Bool :=
  match k with
  | 0 => commL A B
  | 1 => braidL A B && !commL A B
  | _ => dihL A B && !commL A B && !braidL A B

@[expose] def spanOKL (T : Array Nat) (D : Mf7Span) : Bool :=
  let g := mf7Gens T
  D.basis.size == 8 && D.coef.size == 32 &&
  (List.range 32).all fun m => decide (D.coef[m]! < 256) &&
    mf7Ap D.basis D.coef[m]! == g[m]! && mf7Ap D.syn g[m]! == 0

@[expose] def intOKL (isWt : Nat → Bool) (A B : Array Nat) (Dl D0 : Mf7Span) : Bool :=
  let S := D0.basis.map (mf7Ap Dl.syn)
  let h0 := commL A B
  (List.range 256).all fun d => mf7Ap S d != 0 ||
    (let v := mf7Ap D0.basis d; v == 0 || (h0 && isWt v))

@[expose] def repKindsL : List Nat := [0, 0, 0, 0, 2, 1]

@[expose] def repsL (isWt : Nat → Bool) (A : Array Nat) (Bs : Nat → Array Nat) : Bool :=
  let D0 := mf7SpanData A
  spanOKL A D0 &&
  (List.range 6).all fun c =>
    let B := Bs c
    let Dl := mf7SpanData B
    kindL A B == repKindsL.getD c 0 && relL (repKindsL.getD c 0) A B &&
    (c == 0 || (spanOKL B Dl && intOKL isWt A B Dl D0))

@[expose] def planeL (A B : Array Nat) (w w' : Nat) : Bool :=
  let Dl := mf7SpanData B
  (mf7Ap A w' ^^^ w' == w) && mf7Ap B w == w && mf7Ap Dl.syn w != 0

end CFSG.KD.SmithD6Reps

end
