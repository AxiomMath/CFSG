module

public import Certificates.Data.Kernel.Spor.Raw

public section

namespace CFSG.KS.Ru2250

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def tv (w m T0 T1 x : Nat) : Nat := pg w m T0 (pg w m T1 x)

@[expose] noncomputable def invK (n w m T0 T1 : Nat) : Bool :=
  bAnd(allN n (fun x => Nat.beq (tv w m T0 T1 (tv w m T0 T1 x)) x),
    bIf(allN n (fun x => Nat.beq (tv w m T0 T1 x) x), false, true))

@[expose] noncomputable def fixK (n w m T0 T1 : Nat) : Nat :=
  foldN n (fun x s => Nat.add s (nIf(Nat.beq (tv w m T0 T1 x) x, nat_lit 1, nat_lit 0))) (nat_lit 0)

@[expose] noncomputable def cmK (n w m T0 T1 X : Nat) : Bool :=
  allN n (fun x => Nat.beq (tv w m T0 T1 (pg w m X x)) (pg w m X (tv w m T0 T1 x)))

@[expose] noncomputable def prK (n w m T0 T1 X Y : Nat) : Bool :=
  bIf(allN n (fun x => Nat.beq (tv w m T0 T1 (pg w m X x)) (pg w m Y (tv w m T0 T1 x))), false,
    true)

@[expose] noncomputable def pathK (PL : Nat → Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 1)
    (fun _ ih j => nIf(Nat.beq j (nat_lit 0), nat_lit 1, strictN (PL j) (fun pl =>
      Nat.add (Nat.land pl (nat_lit 1)) (Nat.mul (nat_lit 2) (ih (Nat.shiftRight pl (nat_lit 4)))))))

@[expose] noncomputable def pwK (n w m G0 G1 idn : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => idn)
    (fun _ ih P => nIf(Nat.ble P (nat_lit 1), idn, strictN (ih (Nat.shiftRight P (nat_lit 1)))
      (fun T => pcomp n w m (nIf(Nat.beq (Nat.land P (nat_lit 1)) (nat_lit 0), G0, G1)) T)))

@[expose] noncomputable def reachK (PL : Nat → Nat) : Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun j => Nat.beq j (nat_lit 0))
    (fun _ ih j => bIf(Nat.beq j (nat_lit 0), true, strictB (PL j) (fun pl =>
      ih (Nat.shiftRight pl (nat_lit 4)))))

@[expose] noncomputable def zwK (n w m N : Nat) (PL : Nat → Nat) (G0 G1 Z T0 T1 j : Nat) : Bool :=
  bAnd(Nat.blt j N, bAnd(reachK PL (nat_lit 64) j,
    strictB (pwK n w m G0 G1 (pidn n w) (nat_lit 64) (pathK PL (nat_lit 64) j)) (fun G =>
      allN n (fun x => Nat.beq (tv w m T0 T1 (pg w m G x)) (pg w m G (pg w m Z x))))))

@[expose] noncomputable def cntK (TR : Nat → Nat) (o0 o1 c1 : Nat)
    (P : Nat → Nat → Nat → Nat → Bool) (lo len : Nat) : Nat :=
  foldN len (fun i s => strictN (Nat.add lo i) (fun a => strictN (TR (Nat.add o0 a)) (fun T0 =>
    Nat.add s (foldN c1 (fun b s' => strictN (TR (Nat.add o1 b)) (fun T1 =>
      Nat.add s' (nIf(P a b T0 T1, nat_lit 1, nat_lit 0)))) (nat_lit 0))))) (nat_lit 0)

@[expose] noncomputable def rowK (TR : Nat → Nat) (o0 o1 : Nat) (P : Nat → Nat → Nat → Nat → Bool)
    (a blo blen : Nat) : Bool :=
  strictB (TR (Nat.add o0 a)) (fun T0 => allN blen (fun i => strictB (Nat.add blo i) (fun b =>
    strictB (TR (Nat.add o1 b)) (fun T1 => P a b T0 T1))))
end CFSG.KS.Ru2250

end
