module

public import Certificates.Data.Kernel.FiveStdKW

public section

namespace CFSG.KC.FiveStdK

@[expose] noncomputable def nzK (g2 : Nat) (H V K1 : List Nat) : Bool :=
  andB (!(Nat.beq g2 oneK)) <|
  andB (allL H fun h => memL (powersK g2 5) (cjK h (invK h) g2)) <|
  andB (allN 4 fun i => letB (V.getD i 0) fun v =>
    andB (memL H v) (Nat.beq (cjK v (invK v) g2) (powK g2 (Nat.succ i)))) <|
  allL V fun v => andB (allL (powersK g2 5) fun x => memL (powersK g2 5) (cjK v (invK v) x))
    (allL K1 fun k => memL K1 (cjK v (invK v) k))

end CFSG.KC.FiveStdK

end
