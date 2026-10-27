
module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7IsoInputs
import CFSG.Certificates.Kernel.LocalQTA7RhoSound

@[expose] public section

namespace Certificates

open CFSG.KC.LQT.L CFSG.QuasithinUnique.Vol2Native.A312L.Seven in
private theorem certificate4082_v8 :
    (List.finRange 7).map (fun i => bitsV (vec8 i)) = [1, 2, 4, 7, 3, 6, 5] := by
  decide +kernel

open CFSG.KC.LQT.L CFSG.QuasithinUnique.Vol2Native.A312L.Seven in
private theorem certificate4082_v9 :
    (List.finRange 7).map (fun i => bitsV (vec9 i)) = [1, 2, 4, 7, 6, 3, 5] := by
  decide +kernel

end Certificates
