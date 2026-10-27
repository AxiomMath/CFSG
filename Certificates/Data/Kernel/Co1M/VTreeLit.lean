module

public import Certificates.Data.Kernel.J4Q.VOrb
public import Certificates.Data.CFSGNative.Co1.OddCent

public section

namespace CFSG.KC.Co1M

open CFSG.KC.J4Q CFSG.Sporadic.Co1.OddCentNative

@[expose] noncomputable def vtLit (rm root : Nat) (EN : List Nat) : VTree :=
  ⟨(vptsK rm root EN).toArray, (List.cons 0 (List.map (fun e => Nat.shiftRight e 114) EN)).toArray,
    (List.cons 0 (List.map (fun e => Nat.land (Nat.shiftRight e 112) 3) EN)).toArray⟩

end CFSG.KC.Co1M

end
