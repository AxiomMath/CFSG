module

public import Certificates.Data.Kernel.M1F2

public section

namespace CFSG.KC.VOrbRec

open CFSG.KLie.CT CFSG.KC.M1F2

@[expose] noncomputable def closedAt (d MA MB M p : Nat) : Bool :=
  andB (bit M (vmF d MA p)) (bit M (vmF d MB p))

@[expose] noncomputable def recAt (d MA MB M : Nat) (R : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun acc => Nat.beq acc M)
    (fun r _ ih acc => strictB (Nat.land r (Nat.sub (pw2 d) (nat_lit 1))) fun p =>
      strictB (Nat.shiftRight r d) fun q =>
        andB (Nat.blt p (pw2 d)) (andB (notB (bit acc p)) (andB (bit acc q)
          (andB (orB (Nat.beq (vmF d MA q) p) (Nat.beq (vmF d MB q) p))
            (andB (closedAt d MA MB M p) (ih (Nat.lor acc (pw2 p)))))))) R

@[expose] noncomputable def vorbRecK (d MA MB v₀ n M : Nat) (R : List Nat) : Bool :=
  andB (Nat.blt v₀ (pw2 d)) (andB (Nat.beq (Nat.succ (List.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun _ _ ih => Nat.succ ih) R)) n)
    (andB (closedAt d MA MB M v₀) (recAt d MA MB M R (pw2 v₀))))

end CFSG.KC.VOrbRec

end
