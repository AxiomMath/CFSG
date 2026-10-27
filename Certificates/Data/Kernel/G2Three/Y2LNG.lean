module

public import Certificates.Data.Y2L.NG
public import Certificates.Data.Kernel.G2Three.Defs

public section

namespace CFSG.KD.G2Three

open CFSG.OddStandard.HigherRank.G2Three.Sec2

@[expose] noncomputable def ngGenK (G : Nat → Nat) (i : Nat) : Nat :=
  bif Nat.blt i 4 then G i else ONE

@[expose] noncomputable def ngWordK (G : Nat → Nat) (w : List Nat) : Nat :=
  w.foldl (fun acc i => MUL acc (ngGenK G i)) ONE

@[expose] noncomputable def ngCheckK (G : Nat → Nat) : Bool :=
  let W := y2l_ngW ()
  [0, 1, 2, 3].all (fun i => Nat.beq (ngWordK G [i, i, i]) ONE) &&
    (y2l_ws26 1 true).all (fun r => Nat.beq (ngWordK G (y2l_ngSubst W r)) ONE) &&
    (y2l_ws7 1).all (fun r => !Nat.beq (ngWordK G (y2l_ngSubst W r)) ONE)

end CFSG.KD.G2Three

end
