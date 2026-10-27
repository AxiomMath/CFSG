module

public import Certificates.Certificate120801
public import Certificates.Certificate120802
public import Certificates.Certificate120803
public import Certificates.Certificate120804

public section

namespace CFSG.Sporadic.Co1Sub

theorem card_T₀ : Nat.card T₀ = 2 ^ 21 :=
  Certificates.certificate120801

theorem card_A₀ : Nat.card A₀ = 3 * 2 ^ 21 :=
  Certificates.certificate120802

theorem card_B₀ : Nat.card B₀ = 405 * 2 ^ 21 :=
  Certificates.certificate120803

theorem sup_A₀_B₀ : A₀ ⊔ B₀ = ⊤ :=
  Certificates.certificate120804

end CFSG.Sporadic.Co1Sub

end
