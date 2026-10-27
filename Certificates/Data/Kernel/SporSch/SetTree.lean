module

public import Certificates.Data.Kernel.SporSch.SetReplay

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def maskK (w s t x : Nat) : Nat :=
  strictN x (fun p => strictN (mask w) (fun m => Nat.shiftRight
    (foldN s (fun q acc => Nat.lor acc (Nat.shiftLeft (nat_lit 1) (Nat.add (nat_lit 64) (pg w m p q))))
      t) (nat_lit 64)))

@[expose] noncomputable def imgMK (w s t G x : Nat) : Nat :=
  strictN G (fun g => strictN x (fun p => strictN (mask w) (fun m => Nat.shiftRight
    (foldN s (fun q acc => Nat.lor acc
      (Nat.shiftLeft (nat_lit 1) (Nat.add (nat_lit 64) (pg w m g (pg w m p q))))) t) (nat_lit 64))))

@[expose] noncomputable def treeK (w s : Nat) (G X : Nat → Nat) (kg i : Nat) : Bool :=
  bIf(Nat.beq i (nat_lit 0), true, strictB (X i) (fun x =>
    bAnd(Nat.blt (parX w s x) i, bAnd(Nat.blt (labX w s x) kg,
      Nat.beq (maskK w s i x)
        (imgMK w s (Nat.add i (nat_lit 1048576)) (G (labX w s x)) (X (parX w s x)))))))

@[expose] noncomputable def sortMK (w s : Nat) (X SO : Nat → Nat) (c i : Nat) : Bool :=
  strictB (SO i) (fun j => bAnd(Nat.blt j c,
    bIf(Nat.blt (Nat.succ i) c, strictB (SO (Nat.succ i)) (fun j' =>
      Nat.blt (maskK w s j (X j)) (maskK w s j' (X j'))), true)))

end CFSG.KS.SporSch

end
