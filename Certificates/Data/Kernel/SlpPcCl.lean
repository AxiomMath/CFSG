module

public import Certificates.Data.Kernel.SlpPc

public section

namespace CFSG.KC.SlpPc

open CFSG.KC.Ord

@[expose] noncomputable def revOnto (l acc : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
    (fun x _ ih acc => ih (List.cons x acc)) l acc

@[expose] noncomputable def lenN (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun _ _ ih => Nat.succ ih) l

@[expose] noncomputable def zsOf (es : List (List Nat)) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil
    (fun e _ ih => revOnto (revOnto (dropN 7 e) List.nil) ih) es

@[expose] noncomputable def commOK (mul : Nat → Nat → Nat) (R : Nat → Nat) (y : Nat)
    (zs : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun z _ ih => andB ((fun Z => Nat.beq (mul Z y) (mul y Z)) (R z)) ih) zs

@[expose] noncomputable def entOK (mul : Nat → Nat → Nat) (ONE : Nat) (R : Nat → Nat)
    (pw : List (List Nat)) (X : Nat) (e : List Nat) : Bool :=
  andB (ltUpTo e 5 6) (sB (nfM mul ONE pw e) fun y => sB (R (nthD 0 e 6)) fun H =>
    andB (Nat.beq (mul X H) (mul H y)) (commOK mul R y (dropN 7 e)))

@[expose] noncomputable def clK (mul : Nat → Nat → Nat) (ONE A B : Nat) (R : Nat → Nat)
    (pw : List (List Nat)) (hs : List Nat) (X : Nat) (es : List (List Nat))
    (lp : List (Nat × Nat)) (ab : List Nat) : Bool :=
  andB (List.rec (motive := fun _ => Bool) true (fun e _ ih => andB (entOK mul ONE R pw X e) ih) es)
    (mapS R (zsOf es) fun zv =>
      (fun cur => runP mul ONE lp List.nil cur (lenN cur) fun bl cur n =>
        andB (Nat.beq (lk ONE bl cur n (nthD 0 ab 0)) A) (Nat.beq (lk ONE bl cur n (nthD 0 ab 1)) B))
      (revOnto zv (revOnto hs [ONE])))

@[expose] noncomputable def clsOK (mul : Nat → Nat → Nat) (ONE A B : Nat) (R : Nat → Nat)
    (pw : List (List Nat)) (hs wr : List Nat) (lp : List (List (Nat × Nat))) (lab : List (List Nat))
    (ce : List (List (List Nat))) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun k => Nat.beq k 5)
    (fun es _ ih k => andB (sB (R (nthD 0 wr k)) fun X =>
      List.rec (motive := fun _ => Bool) true
        (fun _ _ _ => clK mul ONE A B R pw hs X es (nthD List.nil lp k) (nthD List.nil lab k))
        (nthD List.nil lp k)) (ih (Nat.succ k))) ce

@[expose] def fusT (fus : List (List Nat)) (r : Nat) : Nat := (fus.getD r []).getD 7 0

@[expose] def peLinkOK (fus pe : List (List Nat)) (lp : List (List (Nat × Nat))) : Bool :=
  pe.all (fun p => Nat.blt (p.getD 6 0) fus.length && Nat.blt (p.getD 14 0) pe.length &&
      Nat.blt (p.getD 15 0) fus.length &&
      (List.range 6).all (fun t =>
        Nat.beq ((pe.getD (p.getD 14 0) []).getD t 0) ((fus.getD (p.getD 15 0) []).getD t 0)) &&
      Nat.beq (fusT fus ((pe.getD (p.getD 14 0) []).getD 6 0)) (fusT fus (p.getD 6 0)) &&
      Nat.beq ((pe.getD (p.getD 14 0) []).getD 7 0) (p.getD 7 0)) &&
    (List.range 5).all (fun k => !(lp.getD k []).isEmpty || pe.any (fun p =>
      Nat.beq (fusT fus (p.getD 15 0)) k && Nat.blt (fusT fus (p.getD 6 0)) 5 &&
        !(lp.getD (fusT fus (p.getD 6 0)) []).isEmpty))

@[expose] noncomputable def chkJCl (mul vec : Nat → Nat → Nat) (A B ONE L LV HV RM L9 H9 : Nat)
    (prg px : List (Nat × Nat)) (wg wr : List Nat) (hw rel fus : List (List Nat)) (bw : Nat)
    (hwm : List Nat) (ce : List (List (List Nat))) (lp : List (List (Nat × Nat)))
    (lab : List (List Nat)) : Bool :=
  runP mul ONE prg List.nil [B, A, ONE] 3 fun bl0 cur0 n0 =>
  runP mul ONE px bl0 cur0 n0 fun bl cur n =>
    mapS (fun w => wordP mul ONE (fun l => lk ONE bl cur n (nthD 0 wg l)) w) hw fun hs =>
    pows mul ONE hs fun pw =>
      andB (Nat.beq hs.length 6) (andB (relsOK mul ONE hs pw rel 0 0)
        (andB (hwmOK L9 H9 hwm) (andB (bwOK L bw) (andB (invOK vec LV HV RM bw hs hwm)
          (andB (fusOK mul ONE (lk ONE bl cur n) pw wr fus)
            (clsOK mul ONE A B (lk ONE bl cur n) pw hs wr lp lab ce 0))))))

end CFSG.KC.SlpPc

end
