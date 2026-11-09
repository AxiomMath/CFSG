module

public import Certificates.Data.Kernel.Spor.MulHQ

public section

namespace CFSG.KS.MulH

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.PEnum

@[expose] noncomputable def invIxK (k cnt : Nat) (CL : Nat → Nat) (c : Nat) : Bool :=
  strictB (r32 CL c) (fun q => bAnd(Nat.blt q cnt,
    Nat.beq (r32 CL (Nat.add (Nat.mul q (Nat.add k k)) (Nat.sub (Nat.mod c (Nat.add k k)) k)))
      (Nat.div c (Nat.add k k))))

@[expose] noncomputable def clHK (n w m k cnt : Nat) (T G GI CL : Nat → Nat) (c : Nat) : Bool :=
  bIf(Nat.blt (Nat.mod c (Nat.add k k)) k,
    findPtK cnt T (prodQK n w m (Nat.add k k) T (bothK k G GI)) CL c, invIxK k cnt CL c)

@[expose] noncomputable def walkK (K cnt : Nat) (PL CL : Nat → Nat) : Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ _ => cnt)
    (fun _ ih a b => nIf(Nat.beq b (nat_lit 0), a,
      strictN (ih a (parOf PL b)) (fun a' => nIf(Nat.blt a' cnt,
        r32 CL (Nat.add (Nat.mul a' K) (labOf PL b)), cnt))))

@[expose] noncomputable def nqWK (K nc cnt : Nat) (PL CL NP : Nat → Nat) (i : Nat) : Bool :=
  bIf(Nat.beq i (nat_lit 0), true,
    strictB (parOf PL i) (fun p => strictB (labOf PL i) (fun l =>
      allN nc (fun j => strictB (r32 NP (Nat.add (Nat.mul i nc) j)) (fun v =>
        bAnd(Nat.blt v cnt, Nat.beq v (walkK K cnt PL CL cnt (r32 NP (Nat.add (Nat.mul p nc) j))
          (r32 NP (Nat.add (Nat.mul (r32 CL l) nc) j)))))))))

@[expose] noncomputable def nqGK (n w m k nc cnt : Nat) (T S C CI CL NP : Nat → Nat) : Bool :=
  allN k (fun l => allN nc (fun j => strictB (r32 NP (Nat.add (Nat.mul (r32 CL l) nc) j)) (fun b =>
    bAnd(Nat.blt b cnt, Nat.beq (T b) (pcomp n w m (pcomp n w m (C j) (S l)) (CI j))))))

end CFSG.KS.MulH

end
