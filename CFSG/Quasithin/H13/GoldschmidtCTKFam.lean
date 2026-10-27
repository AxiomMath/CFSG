module

public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks

public section

namespace CFSG.Quasithin.H13.CTK

open CFSG.Open CFSG.QuasithinUnique

@[expose] def IsDelta5Ext (K : Type*) [Group K] (V : Subgroup K) : Prop :=
  ∃ α : K →* alternatingGroup (Fin 5), Function.Surjective α ∧ α.ker = V ∧
    ∃ β : V →* Multiplicative (evenWeight 5), Function.Bijective β ∧
      ∀ ℓ : K, ∀ u v : V, (v : K) = ℓ * u * ℓ⁻¹ → ∀ i : Fin 5,
        ((Multiplicative.toAdd (β v) : evenWeight 5) : Fin 5 → ZMod 2) i =
          ((Multiplicative.toAdd (β u) : evenWeight 5) : Fin 5 → ZMod 2)
            ((α ℓ : Equiv.Perm (Fin 5))⁻¹ i)

@[expose] def A5Config (S : Type) [Group S] : Prop :=
  ∃ K V T₁ T₂ : Subgroup S, V ≤ K ∧ Nat.card ↥V = 16 ∧ IsElemAbelian 2 V ∧
    IsDelta5Ext ↥K (V.subgroupOf K) ∧ T₁ ≤ Subgroup.normalizer (K : Set S) ∧
    Subgroup.normalizer (V : Set S) = K ⊔ T₁ ∧ IsSylowTwoOf T₁ (K ⊔ T₁) ∧
    IsSylowTwoOf T₂ ⊤ ∧ T₁ ≤ T₂ ∧ T₁.relIndex T₂ ≤ 2

end CFSG.Quasithin.H13.CTK
