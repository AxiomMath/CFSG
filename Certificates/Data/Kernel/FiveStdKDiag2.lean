module

public import Certificates.Data.Kernel.FiveStdKDiag

public section

namespace CFSG.KC.FiveStdK

@[expose] noncomputable def dvIn (A nA zt τ b : Nat) : Bool :=
  orB (memA A nA (mulK b (invK oneK))) <| orB (memA A nA (mulK b (invK zK))) <|
    orB (memA A nA (mulK b (invK τ))) (memA A nA (mulK b (invK zt)))

@[expose] noncomputable def dvPt (A nA B Mc k : Nat) : Bool :=
  letB (f20 B k) fun τ =>
    ifB (andB (Nat.beq (mulK τ τ) oneK) (andB (!Nat.beq τ oneK) (!Nat.beq τ zK)))
      (letB (mulK zK τ) fun zt => allN Mc fun j => dvIn A nA zt τ (f20 B j)) true

@[expose] noncomputable def dvOK (A nA B Mc : Nat) : Bool := allN Mc (dvPt A nA B Mc)

end CFSG.KC.FiveStdK

end
