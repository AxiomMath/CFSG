module

public import CFSG.LocalAnalysis.StandardType.GGTBJOmDefs

public section

open Module Multiplicative QuadraticMap Polynomial

namespace CFSG.StandardType

namespace OrthTorus

open SpCoord NbrOrth
open CFSG.RankThree.Classical2 (orthDerived)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p r : ℕ} {A : Subgroup (V ≃ₗ[K] V)}

@[expose] noncomputable def TBJOmData.τΩ (Δ : TBJOmData Q p A r) (hA : A ≤ orthDerived Q) :
    (Fin r → Multiplicative (ZMod p)) →* ↥(orthDerived Q) :=
  Δ.τ.codRestrict (orthDerived Q) fun f =>
    hA (by
      have h : Δ.τ f ∈ Δ.τ.range := ⟨f, rfl⟩
      rwa [Δ.τ_range] at h)

end OrthTorus

end CFSG.StandardType

end
