module

public import CFSG.Quasithin.EmptyFaithful.S152L08A
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtX1512Odd

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace X1512

variable {G : Type} [Group G]

@[expose] def ShapeDatum (H P C A : Subgroup G) : Prop :=
  ∃ x : G, x ∈ H ∧ x ∉ P ∧ x ^ 3 ∈ C ∧
    (∀ a ∈ A, a * x * a⁻¹ * x⁻¹ ∈ C ∨ a * x * a⁻¹ * x ∈ C) ∧
    ∃ a ∈ A, a * x * a⁻¹ * x ∈ C

structure ShapeCtx (T P H U L N A : Subgroup G) : Prop where
  mp : MinParabolic H T P
  elem : IsElemAbelian 2 U
  step : IsChiefStep H U L N
  noncentral : ¬ IsCentralStep H L N
  le : A ≤ T
  abelian : IsElemAbelian 2 A
  offender : ¬ A ≤ pCoreOf 2 H
  count : cSecIn A L N = A ⊓ pCoreOf 2 H ∧
    Nat.card A * Nat.card (fixSecIn A L N) =
      Nat.card (A ⊓ pCoreOf 2 H : Subgroup G) * Nat.card N
  leJ : A ≤ thompsonJ H

namespace ShapeCtx

variable {T P H U L N A : Subgroup G} (c : ShapeCtx T P H U L N A)

include c

theorem normalizes : H ≤ Subgroup.normalizer (cSecIn H L N : Set G) :=
  S152L08.normalizes_cSecIn c.step

variable [Finite G]

theorem pCoreOf_le : pCoreOf 2 H ≤ cSecIn H L N := S152Fin.pCoreOf_le_cSecIn c.elem c.step

theorem not_mem_of_not_mem {a : G} (hK : ¬ oTwoUpper H ≤ cSecIn H L N) (ha : a ∈ A)
    (haQ : a ∉ pCoreOf 2 H) : a ∉ cSecIn H L N := fun hC =>
  haQ (inf_le_pCoreOf c.mp (S152Fin.cSecIn_le_left H L N) c.normalizes hK ⟨c.le ha, hC⟩)

end ShapeCtx

end X1512

end CFSG.Quasithin
