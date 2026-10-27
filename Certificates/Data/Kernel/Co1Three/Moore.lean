module

public import Certificates.Data.Kernel.Co1BW
public import Certificates.Data.Kernel.Co1B

public section

namespace CFSG.KC.Co1Moore

open CFSG.KC.Co1B

@[expose] noncomputable def ndK (M : Nat → Nat) (N i : Nat) : Nat :=
  if i - 1 < N then M (i - 1) else oneK

@[expose] noncomputable def mooreK (m : Nat → Nat) (X : Nat) : Bool :=
  !eqK X oneK && eqK (powWK X 3) oneK &&
    (List.range 7).all (fun j => eqK (mulWK X (m (j + 1))) (mulWK (m (j + 1)) X)) &&
    eqK (powWK (m 1) 3) oneK && !eqK (m 1) oneK &&
    (List.range 6).all (fun j => eqK (powWK (m (j + 2)) 2) oneK) &&
    (List.range 6).all (fun j => eqK (powWK (mulWK (m (j + 1)) (m (j + 2))) 3) oneK) &&
    (List.range 7).all (fun i => (List.range 7).all (fun j =>
      decide (i + 2 ≤ j) -> eqK (powWK (mulWK (m (i + 1)) (m (j + 1))) 2) oneK))

end CFSG.KC.Co1Moore

end
