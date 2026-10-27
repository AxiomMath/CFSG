module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP10Cox
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP2Tr
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP5Tr

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431

@[expose] def U42AutRho : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M₁ M₂ : Subgroup G) (z : G) (c : AutCtx G M₁ M₂ z)
    (R : Subgroup G), IsSylowTwoOf R (cenOf (c.iso.toG fhB)) →
    c.iso.imgG That ⊓ cenOf (c.iso.toG fhB) ≤ R →
    Conf437 z (c.iso.toG fhB) (c.iso.imgG That) R → Conf54 M₁ M₂ (c.iso.toG fhB) R →
    Conf55 c (c.iso.toG fhB) → ∀ ι : Ah ≃* ↥(M₁ ⊔ M₂),
      (∀ x : P1h, (ι (x : Ah) : G) = (c.iso.phi1 x : G)) →
      (∀ x : P2h, (ι (x : Ah) : G) = (c.iso.phi2 x : G)) →
      ∃ ρ : G, ρ ∉ M₁ ⊔ M₂ ∧ ρ ^ 2 = c.iso.toG fhB ∧
        (∀ a ∈ [p10sA 0, p10sA 2, p10sA 4, p10sA 5, p10tA],
          ρ * (ι a : G) * ρ⁻¹ = (ι a : G) * c.iso.toG fhB)

end CFSG.Quasithin.H13.F431.U42Aut
