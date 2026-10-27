module

public import Certificates.Data.Kernel.SporSch.IntLines
public import CFSG.Certificates.Kernel.Enum.Defs
public import Certificates.Data.Kernel.Spor.Chain
public import Certificates.Data.Kernel.Spor.Raw

public section

namespace CFSG.KC.TitsPrim

open CFSG.KC.Enum CFSG.KS CFSG.KC.IntLines CFSG.KC.LQT.Cov

@[expose] noncomputable def letP (S SI : Nat → Nat) (z : Int) : Nat :=
  Int.rec (motive := fun _ => Nat) (fun k => S (Nat.sub k 1)) (fun k => SI k) z

@[expose] noncomputable def ptK (w : Nat) (S SI : Nat → Nat) (wd : List Int) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) x
    (fun z _ ih => strictN ih (fun y => pg w (mask w) (letP S SI z) y)) wd

@[expose] noncomputable def fixK (w : Nat) (S : Nat → Nat) (x : Nat) (wd : List Int) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun z _ ih => bAnd(Nat.beq (pg w (mask w) (S (Nat.sub z.natAbs 1)) x) x, ih)) wd

@[expose] noncomputable def primOK (w kS n k x : Nat) (S SI L R : Nat → Nat) (p : Nat)
    (a b : List Int) : Bool :=
  bAnd(CFSG.KS.Raw.lettersK kS a, bAnd(Nat.beq (ptK w S SI a x) p,
  bAnd(CFSG.KS.Raw.lettersK kS b, bAnd(fixK w S x b,
  strictB (L p) (fun l => bAnd(Nat.blt l k,
  strictB (R l) (fun r => bAnd(Nat.blt r n, Nat.beq (ptK w S SI b r) p))))))))

@[expose] noncomputable def walkK (n : Nat) (ok : Nat → List Int → List Int → Bool) :
    List (List Char) → List (List Char) → Nat → Bool :=
  List.rec (motive := fun _ => List (List Char) → Nat → Bool)
    (fun H p => List.rec (motive := fun _ => Bool) (Nat.beq p n) (fun _ _ _ => false) H)
    (fun t _ ih H p => List.rec (motive := fun _ => Bool) false
      (fun h H' _ => Option.rec (motive := fun _ => Bool) false
        (fun a => Option.rec (motive := fun _ => Bool) false
          (fun b => bAnd(ok p a b, ih H' (Nat.succ p))) (intsSK (tokK h)))
        (intsSK (tokK t))) H)

end CFSG.KC.TitsPrim

end
