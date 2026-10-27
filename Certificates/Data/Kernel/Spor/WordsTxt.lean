module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KS.Words

open CFSG.KC.Enum

@[expose] def letterOfCode (c : Nat) : Int :=
  if c % 2 = 0 then ((c / 2 + 1 : Nat) : Int) else -((c / 2 + 1 : Nat) : Int)

@[expose] def decW (W : Nat) : Nat → List Int
  | 0 => []
  | L + 1 => letterOfCode ((W >>> (4 * L)) % 16) :: decW W L

@[expose] noncomputable def push (ok : Bool) (sg v acc : Nat) : Bool × Nat :=
  (bAnd(ok, bAnd(Nat.blt (nat_lit 0) v, Nat.ble v (nat_lit 8))),
    Nat.add (Nat.mul acc (nat_lit 16)) (Nat.add (Nat.mul (nat_lit 2) (Nat.sub v (nat_lit 1))) sg))

@[expose] noncomputable def run (WC WL : Nat → Nat) (N : Nat) (cs : List Char) :
    Nat → Nat → Nat → Nat → Nat → Bool → Bool → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat → Bool → Bool → Bool)
    (fun k acc len sg v tok ne =>
      bIf(ne, bIf(tok,
          strictB (push true sg v acc).2 fun a => bAnd((push true sg v acc).1,
            bAnd(Nat.beq a (WC k), bAnd(Nat.beq (Nat.succ len) (WL k), Nat.beq (Nat.succ k) N))),
          bAnd(Nat.beq acc (WC k), bAnd(Nat.beq len (WL k), Nat.beq (Nat.succ k) N))),
        Nat.beq k N))
    (fun ch _ ih k acc len sg v tok ne => strictB (Char.toNat ch) fun c =>
      bIf(Nat.beq c (nat_lit 10),
        bIf(ne,
          bIf(tok,
            strictB (push true sg v acc).2 fun a => bAnd((push true sg v acc).1,
              bAnd(Nat.beq a (WC k), bAnd(Nat.beq (Nat.succ len) (WL k),
                ih (Nat.succ k) (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 0) false false))),
            bAnd(Nat.beq acc (WC k), bAnd(Nat.beq len (WL k),
              ih (Nat.succ k) (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 0) false false))),
          ih k acc len sg v tok ne),
      bIf(Nat.beq c (nat_lit 32),
        bIf(tok,
          strictB (push true sg v acc).2 fun a => bAnd((push true sg v acc).1,
            ih k a (Nat.succ len) (nat_lit 0) (nat_lit 0) false true),
          ih k acc len (nat_lit 0) (nat_lit 0) false true),
      bIf(Nat.beq c (nat_lit 45),
        bIf(tok, false, bIf(Nat.beq sg (nat_lit 0), ih k acc len (nat_lit 1) v false true, false)),
      bIf(Nat.ble (nat_lit 48) c, bIf(Nat.blt c (nat_lit 58),
          strictB (Nat.add (Nat.mul v (nat_lit 10)) (Nat.sub c (nat_lit 48))) fun v' =>
            ih k acc len sg v' true true,
          false), false)))))
    cs

@[expose] noncomputable def wordsK (cs : List Char) (WC WL : Nat → Nat) (N : Nat) : Bool :=
  run WC WL N cs (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 0) false false

end CFSG.KS.Words

end
