module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.Statements
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.Steps

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod

namespace F53.Stellmacher.S29

open CosetGeom

variable {G : Type} [Group G] [Finite G]

structure ModFacts (X S Z : Subgroup G) : Prop where
  card_Z : Nat.card Z = 16
  elem_abelian : ∀ B : Subgroup G, B ≤ S → IsElemAbelian 2 B →
    (pCoreOf 2 X ⊓ B).relIndex B ≤ 4 ∧
    (pCoreOf 2 X ⊓ B).relIndex B ≤ (Z ⊓ Subgroup.centralizer (B : Set G)).relIndex Z ∧
    ((pCoreOf 2 X ⊓ B).relIndex B = 4 → 4 ≤ Nat.card ↥⁅Z, B⁆)
  central_involution : ∀ B : Subgroup G, B ≤ S →
    S ≤ Subgroup.normalizer ((pCoreOf 2 X ⊔ B : Subgroup G) : Set G) →
    (pCoreOf 2 X).relIndex (pCoreOf 2 X ⊔ B) = 2 →
    (Z ⊓ Subgroup.centralizer (B : Set G)).relIndex Z = 4
  centralizer_order_eight : ∀ U : Subgroup G, U ≤ Z → S ≤ Subgroup.normalizer (U : Set G) →
    Nat.card U = 8 → ∀ s ∈ S, (∀ u ∈ U, s * u = u * s) → s ∈ pCoreOf 2 X

structure Sit29 (H M S : Subgroup G) (α a₂ a₃ β : Geo H M) : Prop where
  amalg : F53Amalgam H M S
  h28 : Hss28At H M
  h26 : Hss26AAt H M
  b1 : 1 < bMin H M
  adj : (graph (H ⊔ M) H M).Adj α β
  vα : vtype α = false
  bα : bAt α = bMin H M
  hz : Zv β ≤ centerOf (stab β)
  hmod : IsOrthSec (stab α) ⊥ (Zv α) ∨ IsNatSec (stab α) ⊥ (Zv α)
  n₂ : a₂ ∈ nbrs β
  n₃ : a₃ ∈ nbrs β
  ne₁₂ : α ≠ a₂
  ne₁₃ : α ≠ a₃
  ne₂₃ : a₂ ≠ a₃

end F53.Stellmacher.S29

end CFSG.Quasithin
