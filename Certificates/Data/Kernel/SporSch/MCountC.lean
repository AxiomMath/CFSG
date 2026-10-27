module

public import Certificates.Data.Kernel.Spor.MCount

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Mathieu CFSG.KS.M11 CFSG.KS.MEnum

@[expose] noncomputable def commC (n w m : Nat) (D : Nat → Nat) (k : Nat) (g : Nat → Nat) : Bool :=
  allFrom (fun j => strictB (D j) (fun d =>
    allFrom (fun x => Nat.beq (g (pg w m d x)) (pg w m d (g x))) n (nat_lit 0))) k (nat_lit 0)

@[expose] noncomputable def lastC (n w m nw pm : Nat) (D : Nat → Nat) (k L3 L4 h s : Nat) : Nat :=
  foldUp (lcnt L3) (fun k3 s => strictN (ltr nw pm L3 k3) (fun t3 =>
    foldUp (lcnt L4) (fun k4 s => strictN (ltr nw pm L4 k4) (fun t4 =>
      nIf(commC n w m D k (fun x => pg w m h (pg w m t3 (pg w m t4 x))), Nat.succ s, s))) s)) s

@[expose] noncomputable def sliceC (n w m nw pm : Nat) (D : Nat → Nat) (k L0 L1 L2 L3 L4 sub i : Nat) :
    Nat :=
  strictN (Nat.div (lcnt L1) sub) (fun q =>
  strictN (ltr nw pm L0 (Nat.div i sub)) (fun g0 =>
  foldUp q (fun j s => strictN (pcomp n w m g0
      (ltr nw pm L1 (Nat.add (Nat.mul q (Nat.mod i sub)) j))) (fun h1 =>
    foldUp (lcnt L2) (fun k2 s => strictN (pcomp n w m h1 (ltr nw pm L2 k2)) (fun h =>
      lastC n w m nw pm D k L3 L4 h s)) s)) (nat_lit 0)))

@[expose] noncomputable def mCntC (n w : Nat) (bs : List Nat) (NW : Nat) (tA tB : List Nat)
    (W : List (List Int)) (sub i : Nat) (D : Nat → Nat) (k : Nat) : Nat :=
  strictN (mask w) (fun m => strictN (Nat.mul n w) (fun nw => strictN (mask nw) (fun pm =>
  strictN (pidn n w) (fun idn => strictN (Nat.add NW NW) (fun NL =>
  strictN (mLT n w tA tB W) (fun LT =>
  levN n w m nw pm idn LT NL bs (mask NL) (fun Ls _ =>
    five Ls (fun L0 L1 L2 L3 L4 => sliceC n w m nw pm D k L0 L1 L2 L3 L4 sub i))))))))

end CFSG.KS.SporSch

end
