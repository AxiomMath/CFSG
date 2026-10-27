module

public import CFSG.Quasithin.Background.G12Stmts

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace G11

@[expose] def OuterGLInput : Prop :=
  ∀ (U : Type) [AddCommGroup U] [Module (ZMod 2) U] [Finite U] (K : Subgroup (GLV U)),
    (∀ g : GLV U, g ∈ K) → 3 ≤ Module.finrank (ZMod 2) U → Module.finrank (ZMod 2) U ≠ 4 →
    ∀ (α : ↥K ≃* ↥K) (P : Sylow 2 ↥K), (∀ s ∈ P, α s ∈ P) → (∀ s, α (α s) = s) →
      (¬ ∃ c : GLV U, ∀ k : ↥K, ((α k : ↥K) : GLV U) = c * (k : GLV U) * c⁻¹) →
      ∃ s ∈ P, ∃ t ∈ P,
        ¬ ((s⁻¹ * α s) * (t⁻¹ * α t) = (t⁻¹ * α t) * (s⁻¹ * α s) ∧
          (s⁻¹ * α s) * (s⁻¹ * α s) = 1)

section Inspect

variable {U : Type} [AddCommGroup U] [Module (ZMod 2) U]

structure G121Data (f : LinearMap.BilinForm (ZMod 2) U) (M K Q : Subgroup (GLV U)) (v : U) :
    Prop where
  dim : 2 < Module.finrank (ZMod 2) U
  symp : IsSymplectic f
  M_le : M ≤ spSub f
  concl : G121Concl f M v
  K_le : K ≤ M
  K_norm : ∀ m ∈ M, ∀ k ∈ K, m * k * m⁻¹ ∈ K
  K_irr : IsIrr K ⊤
  K_perf : Group.IsPerfect ↥K
  Q_le : Q ≤ M
  Q_comm : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a
  Q_sq : ∀ a ∈ Q, a * a = 1
  Q_trans : v ≠ 0 ∧ ∃ hv : v ∈ perp f v, FullTransvections Q (perp f v) v hv

end Inspect

@[expose] def InspectSimple : Prop :=
  ∀ (U : Type) [AddCommGroup U] [Module (ZMod 2) U] [Finite U]
    (f : LinearMap.BilinForm (ZMod 2) U) (M K Q : Subgroup (GLV U)) (v : U),
    G121Data f M K Q v → IsSimpleGroup ↥K

@[expose] def InspectSylow : Prop :=
  ∀ (U : Type) [AddCommGroup U] [Module (ZMod 2) U] [Finite U]
    (f : LinearMap.BilinForm (ZMod 2) U) (M K Q : Subgroup (GLV U)) (v : U),
    G121Data f M K Q v → CFSG.IsStronglyQuasithin ↥K →
    ∀ P : Sylow 2 ↥K, (∀ s ∈ P, ((s : ↥K) : GLV U) ∈ Q) →
      Module.finrank (ZMod 2) U = 4 ∧ Nat.card ↥Q = 4 ∧
        ∃ (φ : ↥K ≃* ↥(alternatingGroup (Fin 5))) (ψ : U ≃ₗ[ZMod 2] ↥(permCore 5)),
          ∀ (k : ↥K) (u w : U), w = (k : GLV U) u →
            (ψ w : Fin 5 → ZMod 2) =
              permAct ((φ k : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) (ψ u)

@[expose] def InspectOuter : Prop :=
  ∀ (U : Type) [AddCommGroup U] [Module (ZMod 2) U] [Finite U]
    (f : LinearMap.BilinForm (ZMod 2) U) (M K Q : Subgroup (GLV U)) (v : U),
    G121Data f M K Q v → CFSG.IsStronglyQuasithin ↥K →
    ∀ (α : ↥K ≃* ↥K) (P : Sylow 2 ↥K), (∀ s ∈ P, α s ∈ P) → (∀ s, α (α s) = s) →
      (∀ s ∈ P, ∀ t ∈ P, (s⁻¹ * α s) * (t⁻¹ * α t) = (t⁻¹ * α t) * (s⁻¹ * α s) ∧
        (s⁻¹ * α s) * (s⁻¹ * α s) = 1) →
      ∃ g : GLV U, ∀ k : ↥K, ((α k : ↥K) : GLV U) = g * (k : GLV U) * g⁻¹

@[expose] def SectionSQTInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.SectionRank.IsSQTKCat X →
    ∀ (H : Subgroup X) (N : Subgroup H) [N.Normal] [IsSimpleGroup (H ⧸ N)],
      (∃ a b : H ⧸ N, a * b ≠ b * a) → CFSG.IsStronglyQuasithin (H ⧸ N)

end G11

end CFSG.Quasithin
