module

public import Certificates.Data.Kernel.SmithL6K
public import Certificates.Data.SmithL6Stab

public section

namespace CFSG.SmithL6.K

open CFSG.SmithL6

@[expose] def stabClsK (C a : Nat) : Nat :=
  if a = 0 then 0 else
  if fldW 12 C a / 64 = fldW 12 C 0 / 64 then 1 else
  if fldW 12 C a % 64 = fldW 12 C 0 % 64 then 2 else
  3 + 2 * (if form (fldW 12 C 0 % 64) (fldW 12 C a / 64) then 1 else 0) +
    (if form (fldW 12 C a % 64) (fldW 12 C 0 / 64) then 1 else 0)

@[expose] def convEdgeK (C I g u v : Nat) : Bool := tvImgP C I g u == v

@[expose] def stabEdgeK (C I g u v : Nat) : Bool :=
  tvImgP C I g 0 == 0 && tvImgP C I g u == v && stabClsK C u == stabClsK C v

@[expose] def repsK (C : Nat) : List Nat :=
  (List.range 7).map fun c => ((List.range 1953).find? fun a => stabClsK C a == c).getD 0

@[expose] noncomputable def fixK (C I : Nat) : Nat → List Nat → Bool :=
  fun b W => List.rec (motive := fun _ => Nat → Bool) (fun b => decide (1953 ≤ b))
    (fun q _ ih b => (b == 0 || decide (q < 1953) && tvImgP C I q 0 == 0 && tvImgP C I q b != b) &&
      ih (b + 1)) W b

@[expose] def decCols (D : List (Nat × Nat × Nat)) (T : List Nat) : Nat :=
  D.foldl (fun acc e => if (T.getD e.2.1 0).testBit e.2.2 then acc ||| e.1 else acc) 0

@[expose] def stabCardK (C : Nat) : Bool :=
  (List.range 7).all fun c =>
    ((List.range 1953).filter fun a => stabClsK C a == c).length == stabSizes[c]!

@[expose] def stabCommK (C I : Nat) : Bool :=
  let A := (List.range 1953).filter fun a => decide (stabClsK C a ≤ 1)
  let B := (List.range 1953).filter fun a => stabClsK C a == 0 || stabClsK C a == 2
  A.all (fun a => A.all fun b => tvImgP C I a b == b) &&
    B.all (fun a => B.all fun b => tvImgP C I a b == b) &&
    tvImgP C I 1 0 == 0 && tvImgP C I 94 0 == 0 && tvImgP C I 1 94 != 94

end CFSG.SmithL6.K
