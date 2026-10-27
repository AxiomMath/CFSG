module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorusBasic
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitOmFrame
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerOrth
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpCoord
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutNonsplitOmChar

public section

open Module Multiplicative QuadraticMap Polynomial

namespace CFSG.StandardType

namespace OrthTorus

open SpCoord NbrOrth
open CFSG.RankThree.Classical2 (orthDerived)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

structure TBJOmData (Q : QuadraticForm K V) (p : ℕ) (A : Subgroup (V ≃ₗ[K] V)) (r : ℕ) where
  τ : (Fin r → Multiplicative (ZMod p)) →* (V ≃ₗ[K] V)
  F : SevOm.Frame Q p A r
  D : Type
  [addD : AddCommGroup D]
  [modD : Module K D]
  [finD : FiniteDimensional K D]
  c : D ≃ₗ[K] D
  θ : Fin r → D →ₗ[K] V
  τ_eq : ∀ f, τ f = F.ι (piMul r p f)
  τ_inj : Function.Injective τ
  τ_range : τ.range = A
  finrank_D : finrank K D = 2
  c_pow : c ^ p = 1
  c_fix : ∀ u, c u = u → u = 0
  c_twist : ∃ T : D ≃ₗ[K] D, T * c * T⁻¹ = c⁻¹
  c_roots : ∀ (e : ZMod p) (θ' : D →ₗ[K] D), Function.Injective θ' →
    (∀ x, θ' (c x) = (c ^ e.val) (θ' x)) → e = 1 ∨ e = -1
  θ_inj : ∀ j, Function.Injective (θ j)
  θ_range : ∀ j, LinearMap.range (θ j) = F.U j
  θ_act : ∀ (s : Multiplicative (Fin r → ZMod p)) (j : Fin r) (d : D),
    F.ι s (θ j d) = θ j ((c ^ (toAdd s j).val) d)
  normalizer : ∀ g : V ≃ₗ[K] V, (∀ a ∈ A, g * a * g⁻¹ ∈ A) →
    ∃ (π : Equiv.Perm (Fin r)) (ε : Fin r → ZMod p), (∀ i, ε i = 1 ∨ ε i = -1) ∧
      ∀ f f', g * τ f * g⁻¹ = τ f' → ∀ i, toAdd (f' (π i)) = ε i * toAdd (f i)
  swapMove : ∀ i j : Fin r, i ≠ j → ∃ w ∈ orthDerived Q,
    (∀ v : V, (∀ u ∈ F.U i, QuadraticMap.polar Q u v = 0) →
      (∀ u ∈ F.U j, QuadraticMap.polar Q u v = 0) → w v = v) ∧
    ∀ f, w * τ f * w⁻¹ = τ (permAut (Equiv.swap i j) f)
  dinvMove : ∀ i j : Fin r, i ≠ j → ∃ w ∈ orthDerived Q,
    (∀ v : V, (∀ u ∈ F.U i, QuadraticMap.polar Q u v = 0) →
      (∀ u ∈ F.U j, QuadraticMap.polar Q u v = 0) → w v = v) ∧
    ∀ f, w * τ f * w⁻¹ = τ (NbrOrth.dinv i j f)
  signMove : (∃ v : V, v ≠ 0 ∧ ∀ a ∈ A, a v = v) → ∀ i : Fin r, ∃ w ∈ orthDerived Q,
    (∀ v : V, (∀ u ∈ F.U i, QuadraticMap.polar Q u v = 0) →
      (∀ u : V, (∀ a ∈ A, a u = u) → QuadraticMap.polar Q u v = 0) → w v = v) ∧
    ∀ f, w * τ f * w⁻¹ = τ (sgnAut i f)
  noFixed : OrdPNsOm.charSum Q ⊤ ≡ 1 [ZMOD p] → ∀ v : V, (∀ a ∈ A, a v = v) → v = 0
  exFixed : OrdPNsOm.charSum Q ⊤ ≡ -1 [ZMOD p] → ∃ v : V, v ≠ 0 ∧ ∀ a ∈ A, a v = v

attribute [instance] TBJOmData.addD TBJOmData.modD TBJOmData.finD

end OrthTorus

end CFSG.StandardType

end
