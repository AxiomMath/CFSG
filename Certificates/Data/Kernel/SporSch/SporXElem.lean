module

public import Certificates.Data.Kernel.SporSch.PairJ3Cnt

public section

namespace CFSG.KS.SporXE

open CFSG.KC.Enum CFSG.KS.SporSch

@[expose] noncomputable def wF (L : Nat → Nat → Nat) (w : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) x (fun l _ y => L l y) w

@[expose] noncomputable def eF (L : Nat → Nat → Nat) (we : List Nat × Nat) : Nat → Nat :=
  Prod.rec (motive := fun _ => Nat → Nat) (fun w e => powF (wF L w) e) we

@[expose] noncomputable def sF (fs : List (Nat → Nat)) : List (Nat → Nat) :=
  List.rec (motive := fun _ => List (Nat → Nat)) [fun x => x]
    (fun f _ ih => ih ++ List.map (fun h x => h (f x)) ih) fs

@[expose] noncomputable def allF (p : (Nat → Nat) → Bool) (fs : List (Nat → Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun f _ ih => bAnd(p f, ih)) fs

@[expose] noncomputable def distB (bs : List Nat) (hs : List (Nat → Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun h t ih => bAnd(allF (fun h' => bIf(eqOnL bs h h', false, true)) t, ih)) hs

@[expose] noncomputable def ltW (nl : Nat) (words : List (List Nat × Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun we _ ih => bAnd(Prod.rec (motive := fun _ => Bool)
    (fun w _ => List.rec (motive := fun _ => Bool) true (fun l _ ih' => bAnd(Nat.blt l nl, ih')) w)
      we, ih)) words

@[expose] noncomputable def csB (bs : List Nat) (fs : List (Nat → Nat)) : Bool :=
  allF (fun f => bAnd(eqOnL bs (fun x => f (f x)) (fun x => x),
    allF (fun g => eqOnL bs (fun x => f (g x)) (fun x => g (f x))) fs)) fs

@[expose] noncomputable def ckE (bs : List Nat) (L : Nat → Nat → Nat) (nl : Nat)
    (words : List (List Nat × Nat)) : Bool :=
  bAnd(ltW nl words, bAnd(csB bs (words.map (eF L)), distB bs (sF (words.map (eF L)))))

end CFSG.KS.SporXE

end
