module

public import Certificates.Data.Kernel.Spor.MulH

public section

namespace CFSG.KS.PEnumR

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.PEnum CFSG.KS.MulH

@[expose] noncomputable def hkGo4 (w m M4 X : Nat) (q : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ h => h)
    (fun _ ih i h => strictN (Nat.land (Nat.shiftRight X (Nat.mul w i)) M4) (fun c =>
      strictN (hkStep (hkStep (hkStep (hkStep h (Nat.land c m))
        (Nat.land (Nat.shiftRight c w) m)) (Nat.land (Nat.shiftRight c (Nat.add w w)) m))
        (Nat.land (Nat.shiftRight c (Nat.add w (Nat.add w w))) m)) (fun h' =>
      strictN (Nat.add i (nat_lit 4)) (fun i' => ih i' h')))) q

@[expose] noncomputable def hkey4 (n w m X : Nat) : Nat :=
  hkGo4 w m (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 4) w)) (nat_lit 1)) X
    (Nat.shiftRight n (nat_lit 2)) (nat_lit 0) (nat_lit 14695981039346656037)

@[expose] noncomputable def hvF (n w m : Nat) (T HV : Nat → Nat) (i : Nat) : Bool :=
  Nat.beq (hkey4 n w m (T i)) (HV i)

@[expose] noncomputable def penumPtR (n w m : Nat) (GI : Nat → Nat) (k cnt : Nat)
    (T PL POS SRT SRI : Nat → Nat) (i : Nat) : Bool :=
  strictB (T i) (fun t =>
  bAnd(bIf(Nat.beq i (nat_lit 0), true,
    strictB (parOf PL i) (fun p => strictB (labOf PL i) (fun l =>
    bAnd(Nat.blt p i, bAnd(Nat.blt l k, bAnd(Nat.beq (r32 POS (Nat.add (Nat.mul p k) l)) i,
      bIf(Nat.blt (Nat.succ i) cnt,
        lexLtK p l (parOf PL (Nat.succ i)) (labOf PL (Nat.succ i)), true))))))),
  bAnd(allN k (fun j => strictB (r32 POS (Nat.add (Nat.mul i k) j)) (fun q =>
    bAnd(Nat.blt q cnt, bAnd(Nat.beq (T q) (pcomp n w m t (GI j)),
      bIf(Nat.beq q (nat_lit 0), true,
        bIf(lexLtK i j (parOf PL q) (labOf PL q), false, true)))))),
  strictB (r32 SRT i) (fun s => bAnd(Nat.blt s cnt, bAnd(Nat.beq (r32 SRI s) i,
    bIf(Nat.blt (Nat.succ i) cnt, Nat.blt (T s) (T (r32 SRT (Nat.succ i))), true)))))))

end CFSG.KS.PEnumR

end
