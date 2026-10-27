module

public import Certificates.Data.Kernel.MonsterB.Rep4371XGen

public section

namespace CFSG.KC.Rep4371X

open CFSG.KC CFSG.KC.KDense CFSG.KC.Loop CFSG.KC.Rep4371Row

@[expose] noncomputable def octM (W m : Nat) : Bool :=
  strictB (spreadT W m) fun x => bAnd(Nat.beq (Nat.land x W) x,
    bAnd(Nat.beq (popc24 x) (popcT (nat_lit 8) m), Nat.beq (spreadT W (Nat.xor m (nat_lit 255))) (Nat.xor x W)))

@[expose] noncomputable def octChk : Bool :=
  allBelow (nat_lit 77) (nat_lit 2) fun b => strictB (wordT (octT b)) fun W =>
    allBelow (nat_lit 256) (nat_lit 4) fun m => octM W m

end CFSG.KC.Rep4371X

end
