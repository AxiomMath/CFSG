module

public import Certificates.Data.Kernel.Spor.PEnum
public import Certificates.Data.Kernel.Spor.PEnumX

public section

namespace CFSG.KS.MulH

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.PEnum

@[expose] noncomputable def hkStep (h x : Nat) : Nat :=
  Nat.mod (Nat.mul (Nat.xor h x) (nat_lit 1099511628211)) (nat_lit 18446744073709551616)

@[expose] noncomputable def hkGo (w m X : Nat) (rem : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ h => h)
    (fun _ ih i h => strictN (hkStep h (pg w m X i)) (fun h' => ih (Nat.succ i) h')) rem

@[expose] noncomputable def hkeyK (n w m X : Nat) : Nat :=
  hkGo w m X n (nat_lit 0) (nat_lit 14695981039346656037)

@[expose] noncomputable def hsortPtK (n w m cnt : Nat) (T HS HSI : Nat → Nat) (i : Nat) : Bool :=
  strictB (r32 HS i) (fun s => bAnd(Nat.blt s cnt, bAnd(Nat.beq (r32 HSI s) i,
    bIf(Nat.blt (Nat.succ i) cnt,
      Nat.blt (hkeyK n w m (T s)) (hkeyK n w m (T (r32 HS (Nat.succ i)))), true))))

@[expose] noncomputable def findPtK (cnt : Nat) (T Q POS : Nat → Nat) (i : Nat) : Bool :=
  strictB (r32 POS i) (fun q => bAnd(Nat.blt q cnt, Nat.beq (T q) (Q i)))

@[expose] noncomputable def slK (cnt : Nat) (P : Nat → Bool) (lo len : Nat) : Bool :=
  allN len (fun d => strictB (Nat.add lo d) (fun i => bIf(Nat.blt i cnt, P i, true)))

@[expose] noncomputable def wfoldK (n w m : Nat) (S : Nat → Nat) (wd : List Nat) (acc : Nat) :
    Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun l _ ih acc => strictN (pcomp n w m acc (S l)) ih) wd acc

@[expose] noncomputable def cntBelowK (cnt : Nat) (q : Nat → Bool) (hi : Nat) : Nat :=
  CFSG.KS.PEnum.cntK (fun i => bAnd(Nat.blt i cnt, q i)) hi

end CFSG.KS.MulH

end
