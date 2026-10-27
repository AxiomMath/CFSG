module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.S8E58K

open CFSG.KC.Enum

@[expose] noncomputable def cm (CM a b : Nat) : Bool := Nat.beq fld(CM, Nat.add (Nat.mul 64 a) b, 1) 1

@[expose] noncomputable def mt (MT a b : Nat) : Nat := fld(MT, Nat.mul 6 (Nat.add (Nat.mul 44 a) b), 63)

@[expose] noncomputable def fx (FX a : Nat) : Nat := fld(FX, Nat.mul 8 a, 255)

@[expose] noncomputable def g3 (MT i j k : Nat) : List Nat :=
  [43, i, j, k, mt MT i j, mt MT i k, mt MT j k, mt MT i (mt MT j k)]

@[expose] noncomputable def g4 (MT : Nat) (L : List Nat) (l : Nat) : List Nat :=
  L ++ L.map fun f => mt MT f l

@[expose] noncomputable def w2K (FX a b c : Nat) : Bool :=
  !(Nat.beq (Nat.land (Nat.land (fx FX b) (fx FX c)) (Nat.xor 255 (fx FX a))) 0) &&
    !(Nat.beq (Nat.land (Nat.land (fx FX b) (fx FX c)) (fx FX a)) 0)

@[expose] noncomputable def w8K (CM MT FX a b c : Nat) : Bool :=
  cm CM a b && cm CM a c && cm CM b c && cm CM a (mt MT b c) && Nat.beq (fx FX a) 0 &&
    Nat.beq (fx FX (mt MT a b)) 0 && Nat.beq (fx FX (mt MT a c)) 0 &&
      Nat.beq (fx FX (mt MT a (mt MT b c))) 0

@[expose] noncomputable def w3K (CM MT FX : Nat) (L : List Nat) (b a : Nat) : Bool :=
  L.contains b && !(b == 43) && L.contains a && (w2K FX a b b || w8K CM MT FX a b b)

@[expose] noncomputable def w4K (CM MT FX : Nat) (L : List Nat) (b c a : Nat) : Bool :=
  L.contains b && !(b == 43) && L.contains c && !(c == 43) && !(c == b) && L.contains a &&
    (w2K FX a b c || w8K CM MT FX a b c)

@[expose] noncomputable def w3X (CM MT FX : Nat) (L : List Nat) (x : Nat) : Bool :=
  w3K CM MT FX L fld(x, 0, 63) fld(x, 6, 63)

@[expose] noncomputable def w4X (CM MT FX : Nat) (L : List Nat) (x : Nat) : Bool :=
  w4K CM MT FX L fld(x, 0, 63) fld(x, 6, 63) fld(x, 12, 63)

@[expose] noncomputable def rk (R i j k : Nat) : Nat :=
  fld(R, Nat.mul 11 (Nat.add (Nat.mul 1849 i) (Nat.add (Nat.mul 43 j) k)), 2047)

@[expose] noncomputable def wt (W r l : Nat) : Nat :=
  fld(W, Nat.mul 18 (Nat.add (Nat.mul 44 r) l), 262143)

@[expose] noncomputable def max4K (CM : Nat) (L : List Nat) (i j k l : Nat) : Bool :=
  allN 43 fun n => !(cm CM n i && cm CM n j && cm CM n k && cm CM n l) || L.contains n

@[expose] noncomputable def t34K (CM MT FX W i j k r : Nat) : Bool :=
  strictB (wt W r 43) (fun x => w3X CM MT FX (g3 MT i j k) x) && allN 43 fun l =>
    !(Nat.blt k l && cm CM i l && cm CM j l && cm CM k l && !((g3 MT i j k).contains l)) ||
    ((g3 MT i j k).all (fun f => cm CM f l) &&
      strictB (wt W r l) (fun x => w4X CM MT FX (g4 MT (g3 MT i j k) l) x) &&
      max4K CM (g4 MT (g3 MT i j k) l) i j k l)

@[expose] noncomputable def k34K (CM MT FX R W i : Nat) : Bool :=
  allN 43 fun j => allN 43 fun k =>
    !(Nat.blt i j && cm CM i j && Nat.blt j k && cm CM i k && cm CM j k &&
      !([43, i, j, mt MT i j].contains k)) ||
    (cm CM i (mt MT j k) && strictB (rk R i j k) (fun r => t34K CM MT FX W i j k r))

end CFSG.KC.S8E58K
