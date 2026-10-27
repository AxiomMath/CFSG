module

public import CFSG.Sporadic.Co2Smith.C27Final
public import CFSG.Sporadic.Co2Smith.HPExclude
public import CFSG.Sporadic.Co2Smith.CRecog

public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup CFSG.Sporadic.Co2Rank3 CFSG.Sporadic.Co2Cert

@[expose] def SmithGlobalResidual :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G), IsSimpleGroup G → SmithHyp G z →
    ∀ φ : centralizer ({z} : Set G) ≃* Cz,
      (∀ g : G, ∀ ht : g⁻¹ * z * g ∈ centralizer ({z} : Set G),
        (⟨_, ht⟩ : centralizer ({z} : Set G)) ∈ CFSG.pCore 2 (centralizer ({z} : Set G)) →
          g⁻¹ * z * g = z) →
      (∀ g : G, ∀ ht : g⁻¹ * z * g ∈ centralizer ({z} : Set G), g⁻¹ * z * g = z ∨
        ∃ i ∈ ({1, 2, 5} : Finset (Fin 9)), ∃ h : Cz, h * φ ⟨_, ht⟩ * h⁻¹ = cR i) →
      (∃ g : G, ∃ ht : g⁻¹ * z * g ∈ centralizer ({z} : Set G), ∃ h : Cz,
        h * φ ⟨_, ht⟩ * h⁻¹ = cR 5) →
      Co2RecognitionData G

theorem nonempty_mulEquiv_co2_of_residual
    (hc : CCFacts) (hR : SmithGlobalResidual)
    {G : Type} [Group G] [Finite G] {z : G} (hsimple : IsSimpleGroup G) (hG : SmithHyp G z) :
    Nonempty (G ≃* CFSG.Blueprint.NativeSporadic.Co2) := by
  obtain ⟨φ⟩ := nonempty_mulEquiv_Cz_of_census hG
  exact nonempty_mulEquiv_co2_of_data (hR G z hsimple hG φ
    (fun g ht hE => smith_2_2 hc hG φ g ht hE) (fun g ht => smith_conj_classes hc hG φ g ht)
    (smith_2_7 hc hG φ))

theorem smith_co2_of_residual
    (hc : CCFacts) (hR : SmithGlobalResidual) :
    ∀ (X : Type) [Group X] [Finite X] (t : X),
      TimmesfeldCo2Hyp X t → Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.Co2) := by
  intro X _ _ t h
  exact nonempty_mulEquiv_co2_of_residual hc hR h.simple (smithHyp_of_timmesfeld h)

end CFSG.Sporadic.Co2Smith
