module

public import Certificates.Data.Kernel.Misc.Sp8Syl3
public import Certificates.Data.RudvalisFF81Sp8Cent

public section

namespace CFSG.KD.Sp8Cz

open CFSG.KD.BfsK CFSG.KD.Sp8Syl3 CFSG.KC.Mat8P CFSG.KC.Loop
open CFSG.Quasithin.H13.Mat8Cert CFSG.RankThree.PartTwo.Sec21.FF81.Sp8

@[expose] noncomputable def czTabK (R : Nat → Nat) (n : Nat) : Bool :=
  Nat.beq (recX R 8 0) oneP && tableKk R (rst R) 8 n 7 203 1418 203

@[expose] noncomputable def rst2 (R : Nat → Nat) (a b x s : Nat) : Nat :=
  mulP x (R (cond (Nat.beq s 0) a b))

@[expose] noncomputable def e9TabK (R : Nat → Nat) (o a b n : Nat) : Bool :=
  Nat.beq (recX R o 0) oneP && tableKk R (rst2 R a b) o n 2 1 1 1

@[expose] noncomputable def l1N (R : Nat → Nat) : List Nat :=
  [R 0, mulP (R 0) (R 0), R 1, mulP (R 1) (R 1), R 3, mulP (R 3) (R 3), R 7, mulP (R 7) (R 7)]

@[expose] noncomputable def w2N (R : Nat → Nat) (a b : Nat) : List Nat :=
  [mulP (R a) (R b), mulP (R a) (mulP (R b) (R b)), mulP (mulP (R a) (R a)) (R b),
    mulP (mulP (R a) (R a)) (mulP (R b) (R b))]

@[expose] noncomputable def memN (X : Nat) (L : List Nat) : Bool := L.any (Nat.beq X)

@[expose] noncomputable def e9MemK (R : Nat → Nat) (o a b : Nat) : Bool :=
  allBelow 9 1 fun t =>
    Nat.beq (recX R o t) oneP || memN (recX R o t) (l1N R) || memN (recX R o t) (w2N R a b)

@[expose] def qW (a : ℕ) : Bool := (a ^^^ yS a == yS (yS a)) && b4N a (yS a)

@[expose] def crossW (a b : ℕ) : Bool :=
  !b4N a b && !b4N a (yS b) && !b4N (yS a) b && !b4N (yS a) (yS b)

@[expose] def cntW : ℕ :=
  ((((Finset.range 256).filter fun a => qW a = true) ×ˢ
    ((Finset.range 256).filter fun a => qW a = true)).filter fun x => crossW x.1 x.2 = true).card

@[expose] def cntW' : ℕ :=
  ∑ p ∈ fixW, ∑ r ∈ fixW.filter (fun r => b4N p r = true),
    ∑ q ∈ fixW.filter (fun q => (!b4N p q && !b4N r q) = true),
      (fixW.filter fun s => (b4N q s && !b4N p s && !b4N r s) = true).card

end CFSG.KD.Sp8Cz

end
