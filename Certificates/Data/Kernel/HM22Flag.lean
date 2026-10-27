module

public import Certificates.Data.SmithB45HM22Flag

public section

namespace CFSG.KC.HM22Flag

open CFSG.Quasithin.HM22

@[expose] def colT (K P Pi : PM) (j : ℕ) : PV := PM.mulVec Pi (PM.mulVec K (PM.col P j))

@[expose] def winOK (ns : List ℕ) (stds : List PM) (j : ℕ) (v : PV) : Bool :=
  (List.range (ns.length - 1)).all fun i =>
    if nsF ns i ≤ j ∧ j < nsF ns (i + 1) then
      PV.lowZero (nsF ns (i + 1)) v &&
        PV.eqv (nsF ns (i + 1) - nsF ns i) (v.shr (nsF ns i)) (PM.col (stds.getD i []) (j - nsF ns i))
    else true

@[expose] def chunk (f : ℕ → Bool) (w k : ℕ) : Bool := (List.range w).all fun t => f (w * k + t)

@[expose] def idCol9 (j : ℕ) : Bool :=
  PV.eqv 198 (PM.mulVec flagP9 (PM.col flagPi9 j)) (PV.single j 1)

@[expose] def blk1Col9 (j : ℕ) : Bool :=
  winOK flagNs9 [std84A, std15A, std15A, std84A] j (colT (indP blk9 9 false) flagP9 flagPi9 j)

@[expose] def blk2Col9 (j : ℕ) : Bool :=
  winOK flagNs9 [std84B, std15B, std15B, std84B] j (colT (indP blk9 9 true) flagP9 flagPi9 j)

end CFSG.KC.HM22Flag
