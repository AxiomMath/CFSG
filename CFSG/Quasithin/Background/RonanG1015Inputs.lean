module

public import CFSG.Quasithin.Background.P4InspectFinal

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace RonanG1015

open CFSG.Quasithin.G11

@[expose] def NonSQTSylow : Prop :=
  ∀ (U : Type) [AddCommGroup U] [Module (ZMod 2) U] [Finite U]
    (f : LinearMap.BilinForm (ZMod 2) U) (M K Q : Subgroup (GLV U)) (v : U),
    G121Data f M K Q v → ¬ CFSG.IsStronglyQuasithin ↥K →
    ∀ P : Sylow 2 ↥K, ¬ (∀ s ∈ P, ((s : ↥K) : GLV U) ∈ Q)

@[expose] def NonSQTOuter : Prop :=
  ∀ (U : Type) [AddCommGroup U] [Module (ZMod 2) U] [Finite U]
    (f : LinearMap.BilinForm (ZMod 2) U) (M K Q : Subgroup (GLV U)) (v : U),
    G121Data f M K Q v → ¬ CFSG.IsStronglyQuasithin ↥K →
    ∀ (α : ↥K ≃* ↥K) (P : Sylow 2 ↥K), (∀ s ∈ P, α s ∈ P) → (∀ s, α (α s) = s) →
      (∀ s ∈ P, ∀ t ∈ P, (s⁻¹ * α s) * (t⁻¹ * α t) = (t⁻¹ * α t) * (s⁻¹ * α s) ∧
        (s⁻¹ * α s) * (s⁻¹ * α s) = 1) →
      (∀ q ∈ Q, ∀ k k' : ↥K, (k' : GLV U) = q * (k : GLV U) * q⁻¹ →
        ((α k' : ↥K) : GLV U) = q * ((α k : ↥K) : GLV U) * q⁻¹) →
      ∃ g : GLV U, ∀ k : ↥K, ((α k : ↥K) : GLV U) = g * (k : GLV U) * g⁻¹

@[expose] def InspectSylowFree : Prop :=
  ∀ (U : Type) [AddCommGroup U] [Module (ZMod 2) U] [Finite U]
    (f : LinearMap.BilinForm (ZMod 2) U) (M K Q : Subgroup (GLV U)) (v : U),
    G121Data f M K Q v →
    ∀ P : Sylow 2 ↥K, (∀ s ∈ P, ((s : ↥K) : GLV U) ∈ Q) →
      Module.finrank (ZMod 2) U = 4 ∧ Nat.card ↥Q = 4 ∧
        ∃ (φ : ↥K ≃* ↥(alternatingGroup (Fin 5))) (ψ : U ≃ₗ[ZMod 2] ↥(permCore 5)),
          ∀ (k : ↥K) (u w : U), w = (k : GLV U) u →
            (ψ w : Fin 5 → ZMod 2) =
              permAct ((φ k : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) (ψ u)

@[expose] def InspectOuterQ : Prop :=
  ∀ (U : Type) [AddCommGroup U] [Module (ZMod 2) U] [Finite U]
    (f : LinearMap.BilinForm (ZMod 2) U) (M K Q : Subgroup (GLV U)) (v : U),
    G121Data f M K Q v →
    ∀ (α : ↥K ≃* ↥K) (P : Sylow 2 ↥K), (∀ s ∈ P, α s ∈ P) → (∀ s, α (α s) = s) →
      (∀ s ∈ P, ∀ t ∈ P, (s⁻¹ * α s) * (t⁻¹ * α t) = (t⁻¹ * α t) * (s⁻¹ * α s) ∧
        (s⁻¹ * α s) * (s⁻¹ * α s) = 1) →
      (∀ q ∈ Q, ∀ k k' : ↥K, (k' : GLV U) = q * (k : GLV U) * q⁻¹ →
        ((α k' : ↥K) : GLV U) = q * ((α k : ↥K) : GLV U) * q⁻¹) →
      ∃ g : GLV U, ∀ k : ↥K, ((α k : ↥K) : GLV U) = g * (k : GLV U) * g⁻¹

theorem inspectSylowFree_of (h : NonSQTSylow) : InspectSylowFree := by
  intro U _ _ _ f M K Q v hD P hP
  by_cases hsqt : CFSG.IsStronglyQuasithin ↥K
  · exact inspect_sylow U f M K Q v hD hsqt P hP
  · exact absurd hP (h U f M K Q v hD hsqt P)

theorem inspectOuterQ_of (h : NonSQTOuter) : InspectOuterQ := by
  intro U _ _ _ f M K Q v hD α P hαP hαα hel hcent
  by_cases hsqt : CFSG.IsStronglyQuasithin ↥K
  · exact inspect_outer U f M K Q v hD hsqt α P hαP hαα hel
  · exact h U f M K Q v hD hsqt α P hαP hαα hel hcent

end RonanG1015

end CFSG.Quasithin
