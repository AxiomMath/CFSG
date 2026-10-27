module

public import Certificates.Data.Kernel.G2Three.S7

public section

namespace CFSG.KD.G2Three

@[expose] noncomputable def inspLetters (GA : Nat → Nat) : List Nat :=
  [GA 0, GA 1, GA 0, GA 2, MUL (GA 3) (GA 3), GA 2, GA 3, GA 1, MUL (GA 0) (GA 0), GA 2]

@[expose] noncomputable def inspWord (GA : Nat → Nat) : Nat := (inspLetters GA).foldl MUL ONE

@[expose] noncomputable def inspWordInv (GA : Nat → Nat) : Nat :=
  (inspLetters GA).reverse.foldl (fun a w => MUL a (MUL w w)) ONE

@[expose] noncomputable def closedK (XS : Nat → Nat) (ks : List Nat) : Bool :=
  ks.all fun a => ks.all fun b => ks.any fun c => Nat.beq (MUL (XS a) (XS b)) (XS c)

@[expose] noncomputable def c0K (XS : Nat → Nat) (T : Nat) (k1 k2 : List Nat) : Bool :=
  closedK XS k1 && closedK XS k2 && q8K (XS 1) (XS 2) && q8K (XS 3) (XS 4) &&
    Nat.beq (MUL (XS 1) (XS 1)) T && Nat.beq (MUL (XS 3) (XS 3)) T &&
    !(k2.any fun b => Nat.beq (XS b) (XS 1))

@[expose] noncomputable def c1K (XS : Nat → Nat) (k1 k2 : List Nat) : Bool :=
  (List.range 64).all fun a => (List.range 64).all fun b =>
    !q8K (XS a) (XS b) || (k1.contains a && k1.contains b) || (k2.contains a && k2.contains b)

@[expose] noncomputable def c2K (XS : Nat → Nat) (GXL : List Nat) (k1 k2 : List Nat) : Bool :=
  [k1, k2].all fun ks => GXL.all fun y => ks.all fun k => ks.any fun k' =>
    Nat.beq (MUL y (XS k)) (MUL (XS k') y)

@[expose] noncomputable def c3K (XS : Nat → Nat) (XL : List Nat) (G GI : Nat) : Bool :=
  Nat.beq (MUL G GI) ONE &&
    (!(Nat.beq (MUL (XS 4) (XS 4)) ONE) &&
      Nat.beq (MUL (MUL (XS 4) (XS 4)) (MUL (XS 4) (XS 4))) ONE &&
      memK (MUL (MUL G (XS 4)) GI) XL) &&
    !memK (MUL (MUL G (XS 25)) GI) XL

@[expose] noncomputable def c4K (X1 Y1 U V G GI : Nat) : Bool :=
  Nat.beq X1 (MUL (MUL (MUL G G) (MUL V V)) (MUL GI GI)) &&
    Nat.beq Y1 (MUL (MUL (MUL GI GI) U) (MUL G G))

end CFSG.KD.G2Three

end
