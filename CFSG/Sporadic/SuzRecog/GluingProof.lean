module

public import CFSG.Sporadic.SuzRecog.TitsTwoType
public import CFSG.Sporadic.SuzOddCore.InvCentralizers
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2SuzNWC
public import CFSG.Sporadic.SuzRecog.ModelBase

public section

namespace CFSG.Sporadic.SuzRecog

open Subgroup CFSG.Open CFSG.LargeExtraspecial CFSG.Sporadic.SuzOddCore
  CFSG.ComponentClassification.AS81 TitsTwo

@[expose] def SuzLeafHyp {G : Type} [Group G] [Finite G] (S : LargeExtraspecial.Setting G) : Prop :=
  S.width = 3 ∧ (¬ ∃ U : Subgroup G, U ≤ S.QG ∧ IsElemAbelian 2 U ∧ Nat.card U = 16) ∧
    S.Mbar.map S.O.subtype = timmesfeldOmega S.q ∧
    (∃ g : G, g * S.z * g⁻¹ ∈ S.QG ∧ g * S.z * g⁻¹ ≠ S.z) ∧ SuzL34Data S.z

section Agree

variable {G : Type} [Group G] {M : Subgroup G}

@[expose] def B0Agree (σ : M ≃* invE 1) (ψ : Model.NR0 →* G) : Prop :=
  ∀ x (hx : x ∈ invE 1) (hxN : x ∈ Model.NR0), ψ ⟨x, hxN⟩ = (σ.symm ⟨x, hx⟩ : G)

@[expose] def ChartAgree {w : Equiv.Perm (Fin 1782)} (σ : M ≃* invE 1) (ζ : centM w →* G) :
    Prop :=
  ∀ x (hx : x ∈ invE 1) (hxw : x ∈ centM w), ζ ⟨x, hxw⟩ = (σ.symm ⟨x, hx⟩ : G)

variable {F : Type*} [Group F] {V : Type*} [MulAction F V] {Γ : SimpleGraph V}
  {T : Set V → Prop} {ι κ : Type*}

@[expose] def CellRel (D : TitsDataTwo Γ T F ι κ) (π : F →* Model.Crho1)
    {w : Equiv.Perm (Fin 1782)} (σ : M ≃* invE 1) (ψ : Model.NR0 →* G) (ζ : centM w →* G) :
    Prop :=
  ∀ k (h₁ : (π ((D.c k)⁻¹ * D.s * D.c' k) : Equiv.Perm (Fin 1782)) ∈ Model.NR0)
    (h₂ : (π (D.c k) : Equiv.Perm (Fin 1782)) ∈ invE 1)
    (h₃ : (π D.s : Equiv.Perm (Fin 1782)) ∈ centM w)
    (h₄ : (π (D.c' k) : Equiv.Perm (Fin 1782)) ∈ invE 1),
    ψ ⟨_, h₁⟩ = ((σ.symm ⟨_, h₂⟩ : M) : G)⁻¹ * ζ ⟨_, h₃⟩ * ((σ.symm ⟨_, h₄⟩ : M) : G)

end Agree

@[expose] def SuzB0Gluing : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : LargeExtraspecial.Setting G),
    SuzLeafHyp S → Nonempty (S.M ≃* invE 1) →
    ∃ (σ : S.M ≃* invE 1) (ψ : Model.NR0 →* G), B0Agree σ ψ

@[expose] def SuzChartTransfer (w : Equiv.Perm (Fin 1782)) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : LargeExtraspecial.Setting G),
    SuzLeafHyp S → ∀ σ : S.M ≃* invE 1, ∃ ζ : centM w →* G, ChartAgree σ ζ

end CFSG.Sporadic.SuzRecog
