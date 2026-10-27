module

public import CFSG.Quasithin.Vol2.KGFactC31HeData

public section

namespace CFSG.Quasithin.KGC31.He

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.HeldB CFSG.Certificates
  CFSG.Certificates.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative
  CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.Native _root_.Certificates

@[expose] def refW (k : ℕ) : List (List ℤ) := if k = 0 then w5W else w7W

end CFSG.Quasithin.KGC31.He

end
