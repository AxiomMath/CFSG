module

public import CFSG.Quasithin.Background.C2Defs
public import CFSG.Quasithin.Background.F918P4

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G]

@[expose] def FusesThreesModZ (K : Subgroup G) (s : G) : Prop :=
  ∃ x ∈ K, x ^ 3 ∈ oTwoZIn K ∧ x ∉ oTwoZIn K ∧
    ∀ k ∈ K, (k * x * k⁻¹)⁻¹ * (s * x * s⁻¹) ∉ oTwoZIn K

@[expose] def F918Fine4Hat6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T V L V₁ Vp H K : Subgroup G), HypF918 T V L V₁ Vp H K →
    SQTKGroup ↥H → conjClosure K T = K →
    IsHat ↥(autIH V₁ Vp H K) ↥(alternatingGroup (Fin 6)) →
    ∀ t ∈ T, ¬ FusesThreesModZ K t

end CFSG.Quasithin
