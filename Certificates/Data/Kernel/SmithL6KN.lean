module

public import Certificates.Data.Kernel.SmithL6KU
public import Certificates.Data.SmithL6Four

public section

namespace CFSG.SmithL6.K

open CFSG.SmithL6

@[expose] def tvImgQ (C I j a : Nat) : Nat := fldW 11 I (conjF (fldW 12 C j) (fldW 12 C a))

@[expose] def isPartnerK (C I u : Nat) : Bool := u != 0 && tvImgQ C I 0 u == tvImgQ C I u 0

@[expose] def partRootK (C I v : Nat) : Bool := v == 31 || !isPartnerK C I v

@[expose] def partEdgeK (C I g u v : Nat) : Bool :=
  tvImgQ C I g 0 == 0 && tvImgQ C I g u == v && (!isPartnerK C I v || isPartnerK C I u)

@[expose] def keyTri (k : Nat) : Nat × Nat × Nat := (k % 1953, k / 1953 % 1953, k / 1953 / 1953)

@[expose] noncomputable def nthK : List Nat → Nat → Nat :=
  fun L => List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun x _ ih i => if i == 0 then x else ih (i - 1)) L

@[expose] noncomputable def keyAt (L : List Nat) (v : Nat) : Nat :=
  fldW 33 (nthK L (v / 1000)) (v % 1000)

@[expose] noncomputable def recAt (L : List Nat) (v : Nat) : Nat :=
  fldW 32 (nthK L (v / 1000)) (v % 1000)

@[expose] noncomputable def allFrom (f : Nat → Bool) (a n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true) (fun _ ih a => f a && ih (a + 1)) n a

@[expose] def fourEdgeK (C I : Nat) (key : Nat → Nat) (g u v : Nat) : Bool :=
  let s := keyTri (key u)
  let t := keyTri (key v)
  decide (s.2.2 < 1953) && t.1 == tvImgQ C I g s.1 && t.2.1 == tvImgQ C I g s.2.1 &&
    t.2.2 == tvImgQ C I g s.2.2

@[expose] noncomputable def genOK (C I M : Nat) : Bool :=
  allFrom (fun g => !M.testBit g || (tvImgQ C I g 0 == 0 && tvImgQ C I g 31 == 31)) 0 1953

@[expose] def fourRowK (C I : Nat) (key rec : Nat → Nat) (M root v : Nat) : Bool :=
  let r := rec v
  let p := r % 32768
  let g := (r >>> 15) % 2048
  (!decide (v < 20160) || v == root ||
    (decide (p < 20160) && decide (rec p >>> 26 < r >>> 26) && decide (g < 1953) &&
      M.testBit g && fourEdgeK C I key g p v)) &&
  (!decide (v + 1 < 20160) || decide (key v < key (v + 1)))

@[expose] noncomputable def fourChunkK (C I : Nat) (key rec : Nat → Nat) (M root k : Nat) : Bool :=
  allFrom (fourRowK C I key rec M root) (1000 * k) 1000

end CFSG.SmithL6.K
