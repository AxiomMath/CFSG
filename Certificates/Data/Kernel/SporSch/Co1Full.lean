module

public import Certificates.Data.Kernel.SporSch.Co1VOrb

public section

namespace CFSG.KS.SporSch.M24

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.VOrb

@[expose] noncomputable def trK (X : Nat) : Nat :=
  foldN (nat_lit 24) (fun i s => Nat.lor s (Nat.shiftLeft
    (foldN (nat_lit 24) (fun j t => Nat.lor t
      (Nat.shiftLeft (Nat.land (Nat.shiftRight (rowK X j) i) (nat_lit 1)) j)) (nat_lit 0))
    (Nat.mul (nat_lit 24) i))) (nat_lit 0)

@[expose] noncomputable def quadK (a U v : Nat) : Nat :=
  strictN (Nat.land v (nat_lit 16777215)) (fun v' =>
    Nat.xor (parK (Nat.land (Nat.land a (nat_lit 16777215)) v'))
      (parK (Nat.land v' (actK U v'))))

@[expose] noncomputable def cntSl (T S : Nat → Nat) (n w lo len c₀ c₁ : Nat) : Bool :=
  Nat.beq (foldUp len (fun d c => strictN (Nat.add lo d) (fun k =>
    nIf(Nat.blt k n, nIf(memK T S n (Nat.xor (ptK T k) w), Nat.succ c, c), c))) c₀) c₁

end CFSG.KS.SporSch.M24

end
