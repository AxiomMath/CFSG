module

public import Certificates.Data.CFSGNative.J4Tree.Aff

public section

namespace CFSG.ASVolI

open CFSG.J4Tree.Native CFSG.Sporadic.SmallF2.Native

set_option compiler.extract_closed false

@[expose] def burnsideJ4NP_fixesPt (a : Code) (v : Nat) : Bool :=
  v % 2 == 1 && decide (v < 4096) && vecMulN 12 a.rows v == v

@[expose] def burnsideJ4NP_colMinus (a : Code) (z : Nat) : Nat :=
  vecMulN 12 (transposeRows 12 a.rows) z ^^^ z

@[expose] def burnsideJ4NP_sepOK (a : Code) (z : Nat) : Bool :=
  burnsideJ4NP_colMinus a z == 1

@[expose] def burnsideJ4NP_bruteFix (a : Code) : Bool :=
  (List.range 2048).any fun w => burnsideJ4NP_fixesPt a (2 * w + 1)

@[expose] def burnsideJ4NP_reduceComb (B : List (Nat × Nat)) (p : Nat × Nat) : Nat × Nat :=
  B.foldl (fun p b => if p.1 ^^^ b.1 < p.1 then (p.1 ^^^ b.1, p.2 ^^^ b.2) else p) p

@[expose] def burnsideJ4NP_insertComb (B : List (Nat × Nat)) (p : Nat × Nat) : List (Nat × Nat) :=
  let q := burnsideJ4NP_reduceComb B p
  if q.1 == 0 then B else (q :: B).mergeSort fun x y => y.1 ≤ x.1

@[expose] def burnsideJ4NP_solveComb (vs : List Nat) (target : Nat) : Nat :=
  let B := (List.range vs.length).foldl
    (fun B i => burnsideJ4NP_insertComb B (vs.getD i 0, 1 <<< i)) []
  (burnsideJ4NP_reduceComb B (target, 0)).2

@[expose] def burnsideJ4NP_fixCand (a : Code) : Nat :=
  let vs := (List.range 11).map fun i => (a.rows[i + 1]?.getD 0) ^^^ (1 <<< (i + 1))
  1 ||| (burnsideJ4NP_solveComb vs ((a.rows[0]?.getD 0) ^^^ 1) <<< 1)

@[expose] def burnsideJ4NP_sepCand (a : Code) : Nat :=
  let rm := (List.range 12).map fun i => (a.rows[i]?.getD 0) ^^^ (1 <<< i)
  let cols := (List.range 12).map fun j =>
    (List.range 12).foldl
      (fun acc i => if (rm.getD i 0).testBit j then acc ||| (1 <<< i) else acc) 0
  burnsideJ4NP_solveComb cols 1

@[expose] def burnsideJ4NP_hasFix (a : Code) : Bool :=
  if burnsideJ4NP_fixesPt a (burnsideJ4NP_fixCand a) then true
  else if burnsideJ4NP_sepOK a (burnsideJ4NP_sepCand a) then false
  else burnsideJ4NP_bruteFix a

@[noinline, expose] def burnsideJ4NP_sextArrOf (zm : List Nat) : Array Bool :=
  zm.foldl (fun A c => A.set! (etaCode c).transl true) (Array.replicate 2048 false)

@[expose] def burnsideJ4NP_affine2AWith (S : Array Bool) (a : Code) : Bool :=
  if a.inE then S[a.transl]?.getD false else burnsideJ4NP_hasFix a

end CFSG.ASVolI
