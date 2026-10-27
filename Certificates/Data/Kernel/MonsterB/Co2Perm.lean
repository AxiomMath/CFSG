module

public import Certificates.Data.Kernel.MonsterB.Co2Mem
public import Certificates.Data.Kernel.MonsterB.U6Orb

public section

namespace CFSG.KC.Co2Mem

open CFSG.KC.Enum CFSG.KS CFSG.KLie.CT CFSG.KC.U6Orb

@[expose] noncomputable def permStep (n x : Nat) (r : Nat → Bool) (M : Nat) : Bool :=
  andB (Nat.blt x n)
    (andB (notB (CFSG.KLie.CT.bit M x)) (CFSG.KC.U6Orb.strictB (Nat.lor M (pw2 x)) r))

@[expose] noncomputable def permGo (n w X k : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun t r => permStep n (pg w (mask w) X t) r) k

@[expose] noncomputable def permK (n w X : Nat) : Bool := permGo n w X n 0

end CFSG.KC.Co2Mem

end
