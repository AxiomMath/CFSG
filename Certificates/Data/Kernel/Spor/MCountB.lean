module

public import Certificates.Data.Kernel.Spor.MCount

public section

namespace CFSG.KS.MEnum

open CFSG.KC.Enum CFSG.KS CFSG.KS.Mathieu CFSG.KS.M11

@[expose] noncomputable def cntZB (n nb w m ky r : Nat) (Rs : List (Nat × Nat)) (g : Nat → Nat)
    (s : Nat) : Nat :=
  nIf(powId nb g (nat_lit 2),
    nIf(powId nb g (nat_lit 1), s, Nat.add (Nat.succ s) (memsZ n w m g Rs (nat_lit 60))),
    nIf(powId nb g ky,
      Nat.add s (Nat.add (nat_lit 1048576) (partsZ nb w m ky r g Rs (nat_lit 40))),
      s))

@[expose] noncomputable def lastZB (n nb w m nw pm ky r : Nat) (Rs : List (Nat × Nat))
    (L3 L4 h s : Nat) : Nat :=
  foldUp (lcnt L3) (fun k3 s => strictN (ltr nw pm L3 k3) (fun t3 =>
    foldUp (lcnt L4) (fun k4 s => strictN (ltr nw pm L4 k4) (fun t4 =>
      cntZB n nb w m ky r Rs (fun x => pg w m h (pg w m t3 (pg w m t4 x))) s)) s)) s

@[expose] noncomputable def sliceZB (n nb w m nw pm ky r : Nat) (Rs : List (Nat × Nat))
    (L0 L1 L2 L3 L4 sub i : Nat) : Nat :=
  strictN (Nat.div (lcnt L1) sub) (fun q =>
  strictN (ltr nw pm L0 (Nat.div i sub)) (fun g0 =>
  foldUp q (fun j s => strictN (pcomp n w m g0
      (ltr nw pm L1 (Nat.add (Nat.mul q (Nat.mod i sub)) j))) (fun h1 =>
    foldUp (lcnt L2) (fun k2 s => strictN (pcomp n w m h1 (ltr nw pm L2 k2)) (fun h =>
      lastZB n nb w m nw pm ky r Rs L3 L4 h s)) s)) (nat_lit 0)))

@[expose] noncomputable def mCntZB (n nb w : Nat) (bs : List Nat) (NW : Nat) (tA tB : List Nat)
    (W : List (List Int)) (sub i ky r : Nat) (Rs : List (Nat × Nat)) : Nat :=
  strictN (mask w) (fun m => strictN (Nat.mul n w) (fun nw => strictN (mask nw) (fun pm =>
  strictN (pidn n w) (fun idn => strictN (Nat.add NW NW) (fun NL =>
  strictN (mLT n w tA tB W) (fun LT =>
  levN n w m nw pm idn LT NL bs (mask NL) (fun Ls _ =>
    five Ls (fun L0 L1 L2 L3 L4 => sliceZB n nb w m nw pm ky r Rs L0 L1 L2 L3 L4 sub i))))))))

end CFSG.KS.MEnum

end
