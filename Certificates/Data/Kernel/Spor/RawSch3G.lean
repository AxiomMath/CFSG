module

public import Certificates.Data.Kernel.Spor.RawSch3F

public section

namespace CFSG.KS.Raw

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def anyLt (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun j ih => bIf(f j, true, ih)) n

@[expose] noncomputable def wvK (n w m idn : Nat) (S SI : Nat → Nat) (kS TJ : Nat)
    (wd : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) idn
    (fun a _ ih => strictN ih (fun T => pcomp n w m (letterK S SI kS (stAt TJ a)) T)) wd

@[expose] noncomputable def wlK (kS TJ : Nat) (wd : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun a _ ih => bAnd(Nat.blt a (Nat.shiftRight (stCnt TJ) (nat_lit 1)),
      bAnd(Nat.blt (stAt TJ a) kS, ih))) wd

@[expose] noncomputable def wdsK (n w m idn : Nat) (S SI : Nat → Nat) (kS TJ : Nat)
    (W : List (List Nat)) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun j => Nat.beq j kS)
    (fun wd _ ih j => bAnd(wlK kS TJ wd,
      bAnd(Nat.beq (S j) (wvK n w m idn S SI kS TJ wd), ih (Nat.succ j)))) W

@[expose] noncomputable def fixK (w m : Nat) (S SI : Nat → Nat) (kS T p : Nat) : Bool :=
  allN (stCnt T) (fun j => Nat.beq (pg w m (letterK S SI kS (stAt T j)) p) p)

@[expose] noncomputable def incK (T2 T1 : Nat) : Bool :=
  allN (stCnt T2) (fun j => strictB (stAt T2 j) (fun l =>
    anyLt (stCnt T1) (fun j' => Nat.beq (stAt T1 j') l)))

@[expose] noncomputable def lv12K (w m : Nat) (S SI : Nat → Nat) (kS BP i T1 T2 : Nat) : Bool :=
  bAnd(invTabK kS T1, bAnd(invTabK kS T2, bAnd(fixK w m S SI kS T1 (pg w m BP i),
    bAnd(fixK w m S SI kS T2 (pg w m BP (Nat.succ i)), incK T2 T1))))

end CFSG.KS.Raw

end
