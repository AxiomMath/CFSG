module

public import CFSG.Sporadic.SuzRecog.ModelBase
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2SuzNWC

public section

namespace CFSG.Sporadic.SuzRecog

open Subgroup CFSG.Open CFSG.LargeExtraspecial CFSG.Sporadic.SuzOddCore
  CFSG.ComponentClassification.AS81

@[expose] def SuzLevelTwoGluing : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : LargeExtraspecial.Setting G),
    S.width = 3 → (¬ ∃ U : Subgroup G, U ≤ S.QG ∧ IsElemAbelian 2 U ∧ Nat.card U = 16) →
    S.Mbar.map S.O.subtype = timmesfeldOmega S.q →
    (∃ g : G, g * S.z * g⁻¹ ∈ S.QG ∧ g * S.z * g⁻¹ ≠ S.z) → SuzL34Data S.z →
    Nonempty (S.M ≃* invE 1) →
    ∃ (σ : S.M ≃* invE 1) (ψ : Model.NR0 →* G) (Φ₂ : Model.Crho1 →* G),
      (∀ x (hx : x ∈ invE 1) (hxN : x ∈ Model.NR0), ψ ⟨x, hxN⟩ = (σ.symm ⟨x, hx⟩ : G)) ∧
      (∀ x (hx : x ∈ invE 1) (hxC : x ∈ Model.Crho1), Φ₂ ⟨x, hxC⟩ = (σ.symm ⟨x, hx⟩ : G)) ∧
      (∀ x (hxN : x ∈ Model.NR0) (hxC : x ∈ Model.Crho1), Φ₂ ⟨x, hxC⟩ = ψ ⟨x, hxN⟩)

end CFSG.Sporadic.SuzRecog
