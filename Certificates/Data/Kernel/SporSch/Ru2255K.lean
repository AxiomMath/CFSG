module

public import Certificates.Data.Kernel.SporSch.Ru2250K
public import Certificates.Data.Kernel.MonsterB.Co2Word

public section

namespace CFSG.KS.Ru2255

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Co2Mem

@[expose] noncomputable def tv3 (w m T0 T1 T2 x : Nat) : Nat := pg w m T0 (pg w m T1 (pg w m T2 x))

@[expose] noncomputable def sqK (n w m T0 T1 T2 Z : Nat) : Bool :=
  allN n (fun x => Nat.beq (tv3 w m T0 T1 T2 (tv3 w m T0 T1 T2 x)) (pg w m Z x))

@[expose] noncomputable def fixBK (f : Nat → Nat) (e : Nat) : Bool :=
  allN (nat_lit 4) (fun b => Nat.beq (iterK f e b) b)

@[expose] noncomputable def fibK (w m AG T0 T1 T2 : Nat) : Bool :=
  bAnd(fixBK (fun y => pg w m AG (tv3 w m T0 T1 T2 y)) (nat_lit 13),
    fixBK (fun y => pg w m AG (tv3 w m T0 T1 T2 (pg w m AG (tv3 w m T0 T1 T2
      (tv3 w m T0 T1 T2 y))))) (nat_lit 29))

@[expose] noncomputable def ordK (f : Nat → Nat) : Bool :=
  bAnd(fixBK f (nat_lit 14), bAnd(bIf(fixBK f (nat_lit 7), false, true),
    bIf(fixBK f (nat_lit 2), false, true)))

@[expose] noncomputable def conjK (n w m G X Y : Nat) : Bool :=
  allN n (fun x => Nat.beq (pg w m X (pg w m G x)) (pg w m G (pg w m Y x)))

@[expose] noncomputable def conjRK (n w m G X Y : Nat) : Bool :=
  allN n (fun x => bAnd(Nat.blt (pg w m Y x) n,
    Nat.beq (pg w m G (pg w m Y x)) (pg w m X (pg w m G x))))

@[expose] noncomputable def cnt3K (TR : Nat → Nat) (o0 o1 o2 c1 c2 : Nat)
    (P : Nat → Nat → Nat → Bool) (lo len : Nat) : Nat :=
  foldN len (fun i s => strictN (TR (Nat.add o0 (Nat.add lo i))) (fun T0 =>
    Nat.add s (foldN c1 (fun b s' => strictN (TR (Nat.add o1 b)) (fun T1 =>
      Nat.add s' (foldN c2 (fun c s'' => strictN (TR (Nat.add o2 c)) (fun T2 =>
        Nat.add s'' (nIf(P T0 T1 T2, nat_lit 1, nat_lit 0)))) (nat_lit 0)))) (nat_lit 0))))
    (nat_lit 0)

end CFSG.KS.Ru2255

end
