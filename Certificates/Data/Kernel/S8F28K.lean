module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.S8F28K

open CFSG.KC.Enum

@[expose] noncomputable def m128 : Nat := 340282366920938463463374607431768211455

@[expose] noncomputable def cm (CM a b : Nat) : Bool := Nat.beq fld(CM, Nat.add (Nat.mul 64 a) b, 1) 1

@[expose] noncomputable def mt (MT a b : Nat) : Nat := fld(MT, Nat.mul 6 (Nat.add (Nat.mul 44 a) b), 63)

@[expose] noncomputable def fk (FMK a : Nat) : Nat := fld(FMK, Nat.mul 128 a, m128)

@[expose] noncomputable def fAnd (FMK : Nat) (L : List Nat) : Nat :=
  L.foldr (fun a m => Nat.land (fk FMK a) m) m128

@[expose] noncomputable def dz (X F : Nat) : Bool := !(Nat.beq (Nat.land X (Nat.xor m128 F)) 0)

@[expose] noncomputable def g2 (MT i j : Nat) : List Nat := [43, i, j, mt MT i j]

@[expose] noncomputable def g3 (MT i j k : Nat) : List Nat :=
  [43, i, j, k, mt MT i j, mt MT i k, mt MT j k, mt MT i (mt MT j k)]

@[expose] noncomputable def g4 (MT : Nat) (L : List Nat) (l : Nat) : List Nat :=
  L ++ L.map fun f => mt MT f l

@[expose] noncomputable def s1K (FMK : Nat) (L : List Nat) (F : Nat) : Bool :=
  L.any fun b => !(b == 43) && dz (fk FMK b) F

@[expose] noncomputable def s2K (FMK : Nat) (L : List Nat) (F : Nat) : Bool :=
  L.any fun b => L.any fun c => !(b == 43) && !(c == 43) && !(b == c) &&
    dz (Nat.land (fk FMK b) (fk FMK c)) F

@[expose] noncomputable def s3K (CM MT FMK : Nat) (L : List Nat) (F : Nat) : Bool :=
  L.any fun b => L.any fun c => !(b == 43) && !(c == 43) && !(b == c) && cm CM b c &&
    dz (Nat.land (fk FMK b) (fk FMK c)) F && L.any fun d =>
      !([43, b, c, mt MT b c].contains d) &&
        dz (Nat.land (Nat.land (fk FMK b) (fk FMK c)) (fk FMK d)) F

@[expose] noncomputable def e3K (FMK : Nat) (L : List Nat) (F : Nat) : Bool :=
  L.any fun a => L.any fun b => L.any fun c => !(a == b) && !(a == c) && !(b == c) &&
    !(a == 43) && dz (fk FMK a) F && !(b == 43) && dz (fk FMK b) F && !(c == 43) && dz (fk FMK c) F

@[expose] noncomputable def e4K (CM MT FMK : Nat) (L : List Nat) (F : Nat) : Bool :=
  L.any fun d => !(d == 43) && L.any fun a => !([43, d].contains a) && cm CM d a &&
    dz (Nat.land (fk FMK d) (fk FMK a)) F && L.any fun b =>
      !([43, d, a, mt MT d a].contains b) && cm CM d b &&
        dz (Nat.land (fk FMK d) (fk FMK b)) F && L.any fun c =>
          !([43, d, a, mt MT d a].contains c) && !([43, d, b, mt MT d b].contains c) &&
            dz (Nat.land (fk FMK d) (fk FMK c)) F

@[expose] noncomputable def r2K (FMK : Nat) (L : List Nat) : Bool := s1K FMK L (fAnd FMK L)

@[expose] noncomputable def r3K (FMK : Nat) (L : List Nat) : Bool :=
  s1K FMK L (fAnd FMK L) && (s2K FMK L (fAnd FMK L) || e3K FMK L (fAnd FMK L))

@[expose] noncomputable def r4K (CM MT FMK : Nat) (L : List Nat) : Bool :=
  s2K FMK L (fAnd FMK L) && (s3K CM MT FMK L (fAnd FMK L) || e4K CM MT FMK L (fAnd FMK L))

@[expose] noncomputable def max4K (CM : Nat) (L : List Nat) (i j k l : Nat) : Bool :=
  allN 43 fun n => !(cm CM n i && cm CM n j && cm CM n k && cm CM n l) || L.contains n

@[expose] noncomputable def c2K (CM MT FMK : Nat) : Bool :=
  allN 43 fun i => allN 43 fun j => !(Nat.blt i j && cm CM i j) || r2K FMK (g2 MT i j)

@[expose] noncomputable def c3K (CM MT FMK i : Nat) : Bool :=
  allN 43 fun j => allN 43 fun k =>
    !(Nat.blt i j && cm CM i j && Nat.blt j k && cm CM i k && cm CM j k &&
      !([43, i, j, mt MT i j].contains k)) ||
    (cm CM i (mt MT j k) && r3K FMK (g3 MT i j k))

@[expose] noncomputable def t4K (CM MT FMK i j k : Nat) : Bool :=
  allN 43 fun l => !(Nat.blt k l && cm CM i l && cm CM j l && cm CM k l &&
      !((g3 MT i j k).contains l)) ||
    ((g3 MT i j k).all (fun f => cm CM f l) && r4K CM MT FMK (g4 MT (g3 MT i j k) l) &&
      max4K CM (g4 MT (g3 MT i j k) l) i j k l)

@[expose] noncomputable def c4K (CM MT FMK i : Nat) : Bool :=
  allN 43 fun j => allN 43 fun k =>
    !(Nat.blt i j && cm CM i j && Nat.blt j k && cm CM i k && cm CM j k &&
      !([43, i, j, mt MT i j].contains k)) ||
    (cm CM i (mt MT j k) && t4K CM MT FMK i j k)

end CFSG.KC.S8F28K
