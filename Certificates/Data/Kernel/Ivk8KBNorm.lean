module

public import Certificates.Data.Kernel.Ivk8Norm
public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KS.Ivk8KBNorm

open CFSG.Certificates.Kernel.PkEnum CFSG.KS.Ivk8Norm

@[expose] noncomputable def notInV {n : Nat} (x : VP n) (L : List (VP n)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun y _ ih => bAnd(difV x y, ih)) L

@[expose] noncomputable def distinctV {n : Nat} (L : List (VP n)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x xs ih => bAnd(notInV x xs, ih)) L

@[expose] noncomputable def conjsV {n : Nat} (d : VP n) (cs : List (VP n)) : List (VP n) :=
  List.rec (motive := fun _ => List (VP n)) [] (fun c _ ih => conjV c d :: ih) cs

@[expose] noncomputable def cubeNe {n : Nat} (w : VP n) : Bool :=
  difV (mulV w (mulV w w)) (oneV n)

@[expose] noncomputable def fixZ {n : Nat} (d : VP n) (E : List (VP n)) (z : VP n) : Bool :=
  bIf(cubeNe z, true, bIf(difV z (oneV n), bIf(notInV z E, cubeNe (mulV z (conjV d z)), true), true))

@[expose] noncomputable def fixOK {n : Nat} (d : VP n) (E K : List (VP n)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun z _ ih => bAnd(fixZ d E z, ih)) K

end CFSG.KS.Ivk8KBNorm

end
