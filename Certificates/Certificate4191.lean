module

public import CFSG.Sporadic.Schreier.TitsAction
public import CFSG.Quasithin.Vol2.GoldschmidtF45RuModel
import Certificates.Kernel.TitsF48.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Schreier.Tits CFSG.Quasithin.H13.F45Ru

@[expose] def titsF48Facts : Prop :=
  (∀ p : Fin 1755, (∀ x ∈ titsH, x ∈ titsN → x p = p) → p = 0) ∧
    ∀ π : ↥titsH →* Equiv.Perm (Fin 1755),
      (∀ (x : Equiv.Perm (Fin 1755)) (hx : x ∈ titsH), x ∈ titsN → π ⟨x, hx⟩ = x) →
      (∀ (x : Equiv.Perm (Fin 1755)) (hx : x ∈ titsH) (p : Fin 1755),
        octGraph.dist (Sum.inl 0) (Sum.inl p) ≤ 6 → π ⟨x, hx⟩ p = x p) →
      (∀ (y : Equiv.Perm (Fin 1755)) (hy : y ∈ titsH) (q : Equiv.Perm (Fin 1755)), q ∈ titsN →
        (π ⟨y, hy⟩ * q) ^ 17971200 = 1) →
      ∀ y, π y = y

end Certificates

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Schreier.Tits CFSG.Quasithin.H13.F45Ru in
theorem certificate4191 : titsF48Facts :=
  KernelTitsF48.facts4191

end Certificates
