
module

public import CFSG.Quasithin.Vol2.KGFactC31HeData

@[expose] public section

namespace CFSG.Quasithin.KGC31.He

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Schreier.PairNative
  CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.Native CFSG.Sporadic.HeldB _root_.Certificates

theorem band_l {a b : Bool} (h : (a && b) = true) : a = true := ((Bool.and_eq_true a b).mp h).1

theorem band_r {a b : Bool} (h : (a && b) = true) : b = true := ((Bool.and_eq_true a b).mp h).2

theorem beq_nat {a b : ℕ} (h : (a == b) = true) : a = b := beq_iff_eq.mp h

end CFSG.Quasithin.KGC31.He

end
