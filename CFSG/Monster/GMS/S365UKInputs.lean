module

public import CFSG.Sporadic.Co1.Module.OddLitInputs
public import Certificates.Data.Kernel.Co1M.U45

@[expose] public section

namespace CFSG.Sporadic.Co1.Module.Odd

open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.OddNative CFSG.KC.Co1F2 CFSG.KC.U45
  CFSG.Sporadic.Co1.Module

structure UW where
  SI : List ℕ
  SE : List (List ℕ)
  CE : List (List ℕ)

def type4U (v : ℕ) : Bool :=
  type4N (transposeRows 24 qRows) (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 v

structure UOK (W : OddW) (nw : ℕ) (U : UW) : Prop where
  nw1 : 1 ≤ nw
  st : ∀ i < nS, stRec W.T.wl W.T.wp W.T.tab U.SI i = true
  heads : eqL (headsE U.SE) U.SI = true
  se : allE U.SE (stE nw (W.reg 27) W.T.tab nS) = true
  ce : allE U.CE (c5E nw (W.reg 86) W.T.tab W.aux nS) = true
  cinc : incE U.CE 0 = true
  clen : lenE U.CE = 759
  t4 : ∀ e ∈ U.SE ++ U.CE, type4U (getL 0 e 2) = true ∧ type4U (getL 0 e (lastO nw)) = true

end CFSG.Sporadic.Co1.Module.Odd

end
