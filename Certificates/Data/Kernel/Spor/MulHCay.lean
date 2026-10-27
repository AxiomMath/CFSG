module

public import Certificates.Data.Kernel.Spor.MulH

public section

namespace CFSG.KS.MulHCay

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.PEnum CFSG.KS.MulH

@[expose] noncomputable def cayPtK (cnt k : Nat) (PL POS M : Nat → Nat) (c : Nat) : Bool :=
  strictB (Nat.div c cnt) (fun i => strictB (Nat.mod c cnt) (fun j => strictB (r32 M c) (fun q =>
    bAnd(Nat.blt q cnt, bIf(Nat.beq j (nat_lit 0), Nat.beq q i,
      Nat.beq q (r32 POS (Nat.add (Nat.mul (r32 M (Nat.add (Nat.mul cnt i) (parOf PL j))) k)
        (labOf PL j))))))))

@[expose] noncomputable def powPK (n w m p : Nat) (e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (pidn n w) (fun _ acc => pcomp n w m p acc) e

end CFSG.KS.MulHCay

end
