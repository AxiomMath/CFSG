module

public import Certificates.Data.CFSGNative.Timmesfeld.PcReg

public section

namespace Timmesfeld.PcE3

open Timmesfeld.PcReg CFSG.HardMathSupport.Foote.E27

set_option compiler.extract_closed false

@[expose] def tripleOK (p n : Nat) (P : Array (Nat × Nat)) (L : Array (Array Nat))
    (t a b : Nat) : Bool :=
  decide (t < p ^ n) && decide (a < p ^ n) && decide (b < p ^ n) &&
    tabMul P L t a == tabMul P L a t && tabMul P L t b == tabMul P L b t &&
    tabMul P L a b == tabMul P L b a &&
    tabPowIdx P L t p == 0 && tabPowIdx P L a p == 0 && tabPowIdx P L b p == 0 &&
    (List.range p).all fun i => (List.range p).all fun j => (List.range p).all fun l =>
      (i == 0 && j == 0 && l == 0) ||
        tabMul P L (tabMul P L (tabPowIdx P L t i) (tabPowIdx P L a j)) (tabPowIdx P L b l) != 0

@[expose] def e3OK (p n : Nat) (P : Array (Nat × Nat)) (L : Array (Array Nat))
    (ts as bs : Array Nat) : Bool :=
  ts.size == as.size && ts.size == bs.size &&
    (List.range ts.size).all fun k => tripleOK p n P L ts[k]! as[k]! bs[k]!

end Timmesfeld.PcE3
