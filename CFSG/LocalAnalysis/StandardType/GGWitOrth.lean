module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs

import CFSG.LocalAnalysis.StandardType.GGWitOrthCrAux2
import CFSG.LocalAnalysis.StandardType.GGWitOrthL51Aux4

public section

namespace CFSG.StandardType.ZS

open Subgroup

theorem wit_orth_small {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {U : Type} [AddCommGroup U] [Module (ZMod p) U] [Module.Finite (ZMod p) U]
    (Q : QuadraticForm (ZMod p) U) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {A : Subgroup (U ≃ₗ[ZMod p] U)} (hA : ∀ g : U ≃ₗ[ZMod p] U, g ∈ A ↔ IsIsom p Q g)
    (hsmall : Module.finrank (ZMod p) U = 3 ∨
      (p = 3 ∧ (Module.finrank (ZMod p) U = 4 ∨ Module.finrank (ZMod p) U = 5))) :
    WitNEG3 p A ∨ WitORTH p A := by
  rcases hsmall with h3 | ⟨hp3, h45⟩
  · left
    refine ⟨h3, (hA _).mpr ?_⟩
    intro v
    simp
  · right
    rcases h45 with h4 | h5
    · exact ⟨hp3, Or.inl h4, Q, hQ, hA⟩
    · exact ⟨hp3, Or.inr h5, Q, hQ, hA⟩

theorem wit_orth_cr {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {U : Type} [AddCommGroup U] [Module (ZMod p) U] [Module.Finite (ZMod p) U]
    (hp5 : 5 ≤ p) (hd : 4 ≤ Module.finrank (ZMod p) U)
    (Q : QuadraticForm (ZMod p) U) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {A : Subgroup (U ≃ₗ[ZMod p] U)} (hA : ∀ g : U ≃ₗ[ZMod p] U, g ∈ A ↔ IsIsom p Q g) :
    ∀ r ∈ A, IsRefl p r → WitCR p A r := by
  exact owCr_wit_orth_cr hp hp2 hp5 hd Q hQ hA

theorem wit_orth_l51 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {U : Type} [AddCommGroup U] [Module (ZMod p) U] [Module.Finite (ZMod p) U]
    (hp3 : p = 3) (hd : 6 ≤ Module.finrank (ZMod p) U)
    (Q : QuadraticForm (ZMod p) U) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {A : Subgroup (U ≃ₗ[ZMod p] U)} (hA : ∀ g : U ≃ₗ[ZMod p] U, g ∈ A ↔ IsIsom p Q g) :
    ∀ r ∈ A, IsRefl p r → WitL51 p A r := by
  exact owL5_wit_orth_l51 hp hp2 hp3 hd Q hQ hA

end CFSG.StandardType.ZS

end
