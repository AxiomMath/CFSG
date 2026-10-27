module

public import CFSG.Certificates.Kernel.Lie.CT.Core
public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KC.GMS

open CFSG.KLie.CT CFSG.KC.Loop

@[expose] noncomputable def neStrictB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def neAllL {α : Type} (p : α → Bool) (l : List α) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a _ ih => andB (p a) ih) l

@[expose] noncomputable def neLen {α : Type} (l : List α) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => strictN ih Nat.succ) l

@[expose] noncomputable def neGet {α : Type} (d : α) (l : List α) (k : Nat) : α :=
  List.rec (motive := fun _ => Nat → α) (fun _ => d)
    (fun a _ ih k => Nat.rec (motive := fun _ => α) a (fun k' _ => ih k') k) l k

@[expose] noncomputable def neBoundK (T : List (List Nat)) : Bool :=
  neAllL (neAllL fun e => Nat.blt e (nat_lit 64)) T

@[expose] noncomputable def nePack (r : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ _ => nat_lit 0)
    (fun e _ ih n s => Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun n' _ => Nat.lor (Nat.shiftLeft e s) (ih n' (Nat.add s (nat_lit 6)))) n)
    r (nat_lit 64) (nat_lit 0)

@[expose] noncomputable def neHit (r : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun e _ ih n => Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun n' _ => Nat.lor (pw2 e) (ih n')) n) r (nat_lit 64)

@[expose] noncomputable def neIdx (L : List (Fin 7)) (v : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun a _ ih => Bool.rec (motive := fun _ => Nat) (Nat.succ ih) (nat_lit 0) (Nat.beq a.val v)) L

@[expose] noncomputable def neRows (conjTab : List (List Nat)) (L : List (Fin 7)) : Nat :=
  orN (nat_lit 7) fun v =>
    Nat.shiftLeft (nePack (neGet [] conjTab (neIdx L v))) (Nat.mul (nat_lit 384) v)

@[expose] noncomputable def neIdP : Nat :=
  orN (nat_lit 64) fun i => Nat.shiftLeft i (Nat.mul (nat_lit 6) i)

@[expose] noncomputable def nePermW (R : Nat) (u : List (Fin 7)) : Nat :=
  List.rec (motive := fun _ => Nat) neIdP
    (fun l _ ih => strictN ih fun P => (fun row => orN (nat_lit 64) fun i =>
        Nat.shiftLeft (fget row (fget P i (nat_lit 6)) (nat_lit 6)) (Nat.mul (nat_lit 6) i))
      (fget R l.val (nat_lit 384))) u

@[expose] noncomputable def nePermsK (R : Nat) (ws : List (List (Fin 7))) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun u _ ih => List.cons (nePermW R u) ih) ws

@[expose] noncomputable def neNodup (Vs : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun U rest ih => andB (neAllL (fun V => notB (Nat.beq U V)) rest) ih) Vs

@[expose] noncomputable def neWitMask (wit : List (Nat × Nat × Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun t _ ih => Nat.lor (Prod.rec (motive := fun _ => Nat) (fun a bc =>
      Prod.rec (motive := fun _ => Nat) (fun b _ =>
        Bool.rec (motive := fun _ => Nat) (nat_lit 0) (pw2 (Nat.add (Nat.mul (nat_lit 20) a) b))
          (andB (Nat.blt a (nat_lit 20)) (Nat.blt b (nat_lit 20)))) bc) t) ih) wit

@[expose] noncomputable def kAct (mulTab conjTab : List (List Nat)) (L : List (Fin 7))
    (actWords orbitWords : List (List (Fin 7))) (wit : List (Nat × Nat × Nat)) : Bool :=
  andB (neBoundK mulTab) <| andB (neBoundK conjTab) <|
    andB (allN (nat_lit 6) fun k => Nat.beq (neHit (neGet [] conjTab k)) (maskN (nat_lit 64))) <|
    andB (neAllL (neAllL fun (l : Fin 7) =>
      Nat.blt (nat_lit 0) (Nat.land (nat_lit 47) (pw2 l.val))) actWords) <|
    andB (neAllL (neAllL fun (l : Fin 7) => Nat.blt l.val (nat_lit 6)) orbitWords) <|
    andB (neStrictB (neRows conjTab L) fun R => neNodup (nePermsK R actWords)) <|
    andB (Nat.beq (neLen actWords) (nat_lit 192)) <| andB (Nat.beq (neLen orbitWords) (nat_lit 20)) <|
    neStrictB (neWitMask wit) fun M => allN (nat_lit 20) fun k => allN (nat_lit 20) fun l =>
      orB (notB (Nat.blt k l))
        (Nat.blt (nat_lit 0) (Nat.land M (pw2 (Nat.add (Nat.mul (nat_lit 20) k) l))))

@[expose] noncomputable def kW0 (conjTab : List (List Nat)) (L : List (Fin 7)) (w : List (Fin 7)) :
    Bool :=
  andB (neBoundK conjTab) (neStrictB (nePermW (neRows conjTab L) w) fun P =>
    allN (nat_lit 63) fun i => notB (Nat.beq (fget P (Nat.succ i) (nat_lit 6)) (Nat.succ i)))

end CFSG.KC.GMS

end
