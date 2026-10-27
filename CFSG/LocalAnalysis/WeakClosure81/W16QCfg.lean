module

public import CFSG.LocalAnalysis.WeakClosure81.W15ElevenThreeC

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup

variable {G : Type} [Group G] [Finite G]

structure KTCfg16 (U V₀ V I K T Q : Subgroup G) : Prop where
  comm_V : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x
  sq_V : ∀ x ∈ V, x * x = 1
  comm_I : ∀ x ∈ I, ∀ y ∈ I, x * y = y * x
  sq_I : ∀ x ∈ I, x * x = 1
  le_V : U ⊔ V₀ ≤ V
  le_I : U ⊔ V₀ ≤ I
  V_le_K : V ≤ K
  I_le_K : I ≤ K
  V_le_T : V ≤ T
  I_le_Q : I ≤ Q
  Q_le_T : Q ≤ T
  Q_le : Q ≤ centralizer (I : Set G)
  T_le : T ≤ normalizer (Q : Set G)
  inf_le : V ⊓ Q ≤ U ⊔ V₀
  comm_mem : ∀ x ∈ Q, ∀ k ∈ K, k * x * k⁻¹ * x⁻¹ ∈ I
  exists_mul : ∀ t ∈ T, ∃ v ∈ V, v⁻¹ * t ∈ Q
  mem_of_comm : ∀ v ∈ V, v ∉ U ⊔ V₀ → ∀ w ∈ I, v * w = w * v → w ∈ U ⊔ V₀
  card_eq : Nat.card I = Nat.card V
  inf_centralizer_le : Q ⊓ centralizer (V : Set G) ≤ I ⊔ (T ⊓ centralizer (K : Set G))
  inf_eq_bot : V₀ ⊓ centralizer (K : Set G) = ⊥
  comm_mem_V₀ : ∀ t ∈ T, ∀ v ∈ V, t * v * t⁻¹ * v⁻¹ ∈ V₀
  U_le : U ≤ centralizer (K : Set G)
  not_le : ¬ V ≤ U ⊔ V₀
  sq_C : ∀ x ∈ T ⊓ centralizer (K : Set G), x * x = 1

end CFSG.LocalAnalysis.WeakClosure81

end
