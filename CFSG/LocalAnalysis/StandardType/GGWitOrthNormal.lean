module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
import CFSG.LocalAnalysis.StandardType.GGWitOrthNormalAux

public section

namespace CFSG.StandardType.ZS

open Subgroup

theorem wit_orth_normal {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    [Module.Finite (ZMod p) U] (Q : QuadraticForm (ZMod p) U)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) :
    ∃ (e : U ≃ₗ[ZMod p] (Fin (Module.finrank (ZMod p) U) → ZMod p))
      (w : Fin (Module.finrank (ZMod p) U) → ZMod p),
      (∀ i, w i ≠ 0) ∧ ∀ v, Q v = ∑ i, w i * (e v i) ^ 2 := by
  exact owNm_orth_normal_aux hp hp2 Q hQ

theorem wit_classRefl_transport {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {U V : Type} [AddCommGroup U] [Module (ZMod p) U]
    [AddCommGroup V] [Module (ZMod p) V] (Q : QuadraticForm (ZMod p) U) (Q' : QuadraticForm (ZMod p) V)
    (e : U ≃ₗ[ZMod p] V) (he : ∀ v, Q' (e v) = Q v) (c : ZMod p)
    {A : Subgroup (U ≃ₗ[ZMod p] U)} {A' : Subgroup (V ≃ₗ[ZMod p] V)}
    (hA : A = closure (ClassRefl p Q c)) (hA' : A' = closure (ClassRefl p Q' c)) :
    ∃ φ : ↥A ≃* ↥A', ∀ g : ↥A,
      ((φ g : ↥A') : V ≃ₗ[ZMod p] V) = e.symm.trans (((g : ↥A) : U ≃ₗ[ZMod p] U).trans e) := by
  exact owNm_classRefl_transport_aux hp hp2 Q Q' e he c hA hA'

theorem wit_absIrred_transport {p : ℕ} (hp : p.Prime) {U V : Type} [AddCommGroup U] [Module (ZMod p) U]
    [AddCommGroup V] [Module (ZMod p) V] (e : U ≃ₗ[ZMod p] V)
    {A : Subgroup (U ≃ₗ[ZMod p] U)} {A' : Subgroup (V ≃ₗ[ZMod p] V)} (φ : ↥A ≃* ↥A')
    (hφ : ∀ g : ↥A, ((φ g : ↥A') : V ≃ₗ[ZMod p] V) = e.symm.trans (((g : ↥A) : U ≃ₗ[ZMod p] U).trans e))
    (h : AbsIrred p A) : AbsIrred p A' := by
  exact owNm_absIrred_transport_aux hp e φ hφ h

end CFSG.StandardType.ZS

end
