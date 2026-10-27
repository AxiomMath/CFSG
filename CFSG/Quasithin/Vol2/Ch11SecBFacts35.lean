module

public import CFSG.Quasithin.Vol2.Ch11SecBFacts21

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped Pointwise

@[expose] def FactCartanPower : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V T D : Subgroup G) (n p : ℕ),
    IsElemAbelian 2 V → 2 ≤ n → L ≤ Subgroup.normalizer (V : Set G) → ⁅V, L⁆ = V →
    NatModuleOf L V n → QuasithinUnique.IsSylowTwoOf T (L ⊔ T) →
    T ≤ Subgroup.normalizer (V : Set G) → T ≤ Subgroup.normalizer (L : Set G) →
    p.Prime → p ≠ 2 → D ≤ L → IsElemAbelian p D →
    (D : Set G) * (T : Set G) = (T : Set G) * (D : Set G) →
    ∀ t ∈ T, t ∈ Subgroup.normalizer (D : Set G) →
      ∃ r : ℕ, ∀ d ∈ D, t * d * t⁻¹ * (d ^ r)⁻¹ ∈ Subgroup.centralizer (V : Set G)

end CFSG.Quasithin.Vol2.Ch11.SecB
