module

public import CFSG.Certificates.Kernel.Lie.CT.Core

public section

namespace CFSG.KC.F4M

open CFSG.KLie.CT CFSG.KC.Loop

@[expose] noncomputable def MULT : Nat := nat_lit 2625168384

@[expose] noncomputable def fm (a b : Nat) : Nat := fget MULT (Nat.add (Nat.mul (nat_lit 4) a) b) (nat_lit 2)

@[expose] noncomputable def ent (P i j : Nat) : Nat :=
  fget P (Nat.add (Nat.mul (nat_lit 6) i) j) (nat_lit 2)

@[expose] noncomputable def xorN (n : Nat) (f : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun k ih => Nat.xor (f k) ih) n

@[expose] noncomputable def mk (f : Nat → Nat → Nat) : Nat :=
  orN (nat_lit 36) fun t =>
    Nat.shiftLeft (Nat.land (f (Nat.div t (nat_lit 6)) (Nat.mod t (nat_lit 6))) (nat_lit 3))
      (Nat.mul (nat_lit 2) t)

@[expose] noncomputable def mmul (P Q : Nat) : Nat :=
  strictN P fun P => strictN Q fun Q =>
    mk fun i j => xorN (nat_lit 6) fun k => fm (ent P i k) (ent Q k j)

@[expose] noncomputable def tr (P : Nat) : Nat :=
  strictN P fun P => xorN (nat_lit 6) fun i => ent P i i

@[expose] noncomputable def sqC (a : Nat) : Nat := fm a a

@[expose] noncomputable def barM (P : Nat) : Nat :=
  strictN P fun P => mk fun i j => sqC (ent P i j)

@[expose] noncomputable def trn (P : Nat) : Nat := strictN P fun P => mk fun i j => ent P j i

@[expose] noncomputable def detStep (P T S : Nat) : Nat :=
  xorN (nat_lit 6) fun j =>
    nIf(bit S j, fm (ent P (Nat.sub (popc (nat_lit 6) S) (nat_lit 1)) j)
      (fget T (Nat.sub S (pw2 j)) (nat_lit 2)), nat_lit 0)

@[expose] noncomputable def detTab (P n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun S ih => strictN ih fun T =>
      Nat.lor T (Nat.shiftLeft (nIf(Nat.beq S (nat_lit 0), nat_lit 1, detStep P T S))
        (Nat.mul (nat_lit 2) S))) n

@[expose] noncomputable def det (P : Nat) : Nat :=
  strictN P fun P => fget (detTab P (nat_lit 64)) (nat_lit 63) (nat_lit 2)

@[expose] noncomputable def ONE : Nat := nat_lit 1180663682709764194305

@[expose] noncomputable def ANTI : Nat := nat_lit 1154048505100108800

@[expose] noncomputable def E23 : Nat := nat_lit 1073741824

@[expose] noncomputable def unitaryOK (P : Nat) : Bool :=
  Nat.beq (mmul (mmul (trn (barM P)) ANTI) P) ANTI

end CFSG.KC.F4M

end
