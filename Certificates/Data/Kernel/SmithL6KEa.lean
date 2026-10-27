module

public import Certificates.Data.Kernel.SmithL6K
public import Certificates.Data.SmithL6E23a

public section

namespace CFSG.SmithL6.K

open CFSG.SmithL6
open CFSG.SmithE (applyCols)

@[expose] def c8K (T : List (List Nat)) : Bool :=
  let A := (T.getD 0 []).toArray
  let B := (T.getD 31 []).toArray
  eaBits.all (fun m => applyCols A (2 ^ m) == 2 ^ m && applyCols B (2 ^ m) == 2 ^ m) &&
    (List.range 4096).all fun j =>
      (applyCols A (16 * j) == 16 * j && applyCols B (16 * j) == 16 * j) == (j == 0)

@[expose] def wK (W : Nat) : Bool :=
  eaBits.all fun m => (List.range 1395).any fun i => fldW 20 W i == 2 ^ m

@[expose] def eaIK (C I : Nat) : List Nat :=
  (List.range 1953).filter fun p => tvImgP C I p 0 == 0 && tvImgP C I p 31 == 31

@[expose] def f4K (C I : Nat) (T : List (List Nat)) : Bool :=
  let R := (eaIK C I).map fun p => (p, eaBits.map fun m => applyCols (T.getD p []).toArray (2 ^ m))
  R.all fun a => R.all fun b => a.1 == b.1 || a.2 != b.2

@[expose] def eaRelC (x y : Nat) : Nat :=
  if x = y then 0 else if conjC x y = y then 1 else if conjC x y = conjC y x then 2 else 3

@[expose] def rig1K (C I : Nat) (G : List Nat) : Bool :=
  let base := 0 :: 31 :: eaIK C I
  G.all fun g => decide (g < 1953) && (List.range 1953).all fun q =>
    q == g || base.any fun f => eaRelC (fldW 12 C g) (fldW 12 C f) != eaRelC (fldW 12 C q) (fldW 12 C f)

@[expose] def profC (C : Nat) (G : List Nat) (q : Nat) : List Nat :=
  G.map fun g => eaRelC (fldW 12 C q) (fldW 12 C g)

@[expose] def eaG : List Nat := [0, 31, 96, 220, 596, 1332, 760, 42, 838, 14, 1, 2]

@[expose] def profKey (C : Nat) (G : List Nat) (q : Nat) : Nat :=
  (profC C G q).foldl (fun acc r => 4 * acc + r) 0

end CFSG.SmithL6.K
