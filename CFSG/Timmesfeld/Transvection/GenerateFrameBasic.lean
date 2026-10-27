module

public import CFSG.Timmesfeld.Transvection.LineGroup

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS
open scoped commutatorElement

variable {H : Type*} [Group H]

structure PairRelations {K F : Type*} [Field K] [Field F] (σ : F ≃+* F) (ι : K →+* F)
    (Δ : Set (Subgroup H)) (A E D E' : Subgroup H) (pA pD : K → H) (wA wD : H)
    (hA hD : Kˣ → H) (β : F → H) : Prop where
  add : ∀ s t, β (s + t) = β s * β t
  injective : Function.Injective β
  mem_iff : ∀ g, g ∈ shortRootGroup Δ E A D E' ↔ ∃ c, β c = g
  shortLong : ∀ (s : F) (t n : K), ι n = σ s * s * ι t →
    ⁅β s, pA t⁆ = wA * β (s * ι t) * wA⁻¹ * pD n
  shortLong' : ∀ (s : F) (t n : K), ι n = σ s * s * ι t →
    ⁅wD * wA * β (σ s) * (wD * wA)⁻¹, pD t⁆ = wA * β (σ (s * ι t)) * wA⁻¹ * pA n
  trace : ∀ (s t : F) (n : K), ι n = s * σ t + σ s * t → ⁅β s, wA * β t * wA⁻¹⁆ = pD n
  trace' : ∀ (s t : F) (n : K), ι n = s * σ t + σ s * t →
    ⁅wD * wA * β (σ s) * (wD * wA)⁻¹, wA * β (σ t) * wA⁻¹⁆ = pA n
  torusA : ∀ (c : Kˣ) (s : F), hA c * β s * (hA c)⁻¹ = β (ι (c : K) * s)
  torusD : ∀ (c : Kˣ) (s : F), hD c * β s * (hD c)⁻¹ = β (ι ((c⁻¹ : Kˣ) : K) * s)

end CFSG.Timmesfeld.Transvection
