
module


public import Certificates.Certificate2254

public section

namespace CFSG.Sporadic.RuSchreier

theorem ruOrbLA_check :
    (∀ i < 3, ruZL i ∈ Subgroup.centralizer (ruL : Set (Equiv.Perm (Fin 4060)))) ∧
      ∀ k < 19, ∀ k' < 19, k ≠ k' → Disjoint (ruOrb k) (ruOrb k') :=
  Certificates.certificate2254

end CFSG.Sporadic.RuSchreier
