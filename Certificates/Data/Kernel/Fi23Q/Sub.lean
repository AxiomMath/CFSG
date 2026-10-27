module

public import Certificates.Data.Kernel.Fi23Q.Defs

public section

namespace CFSG.KC.Fi23Q

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Pc3

@[expose] noncomputable def swR (m SV v : Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) List.nil
    (fun i acc => (fun k => (fun e w =>
      Bool.rec (motive := fun _ => List Nat)
        (Bool.rec (motive := fun _ => List Nat) (List.append w (List.append w acc))
          (List.append w acc) (Nat.beq e (nat_lit 1)))
        acc (Nat.beq e (nat_lit 0))) (dg v k) (nwR (nat_lit 13) (f32 SV k)))
      (Nat.sub (Nat.sub m (nat_lit 1)) i)) m

@[expose] noncomputable def relW (H : Nat → Nat) (m SV PW CJ : Nat) : Bool :=
  bAnd(allN m fun k => vecOK (nat_lit 13) (f32 SV k),
    bAnd(allN m fun k => (fun s => eqH H (List.append s (List.append s s)) (swR m SV (f32 PW k)))
        (nwR (nat_lit 13) (f32 SV k)),
      allN m fun i => allN m fun j => bIf(Nat.blt i j,
        (fun si sj => eqH H (List.append sj si)
            (List.append si (swR m SV (f32 CJ (Nat.add (Nat.shiftLeft i (nat_lit 4)) j)))))
          (nwR (nat_lit 13) (f32 SV i)) (nwR (nat_lit 13) (f32 SV j)), true)))

@[expose] noncomputable def fixW (H : Nat → Nat) (m SV x : Nat) : Bool :=
  allN m fun k => Nat.beq (wv H (nwR (nat_lit 13) (f32 SV k)) x) x

@[expose] noncomputable def conjW (H : Nat → Nat) (m SV CR v b q : Nat) : Bool :=
  bAnd(vecOK m v, bAnd(vecOK (nat_lit 13) b,
    (fun w => eqH H (List.append (swR m SV v) w) (List.append w (nwR (nat_lit 13) (f32 CR q))))
      (nwR (nat_lit 13) b)))

end CFSG.KC.Fi23Q

end
