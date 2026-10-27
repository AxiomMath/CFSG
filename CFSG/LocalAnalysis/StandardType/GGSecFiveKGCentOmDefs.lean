module

public import CFSG.LieType.Universal.Spin.Chevalley.Plus

public section

namespace CFSG.StandardType.KGCentOm

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin

@[expose] def kgcLiftSet {K : Type} [Field K] {n : ℕ} {G : Type*} [Group G]
    (ψ : spinGroup (quadPlus n K) →* G) (D : Subgroup G) : Set (spinGroup (quadPlus n K)) :=
  {s | ∃ d ∈ D, ∀ u, d * ψ u * d⁻¹ = ψ (s * u * s⁻¹)}

@[expose] def KGCFixedIdx {K : Type} [Field K] {n : ℕ} (hn : 3 ≤ n)
    (S : Set (spinGroup (quadPlus n K))) (i : Fin n) : Prop :=
  ∀ σ ∈ S, spinAction (quadPlus n K) σ ((plusFrame n K hn).vec i true) =
    (plusFrame n K hn).vec i true

end CFSG.StandardType.KGCentOm

end
