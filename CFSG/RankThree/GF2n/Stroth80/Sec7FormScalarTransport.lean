module

public import CFSG.RankThree.GF2n.Stroth80.Sec7InvariantForm

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap CFSG.Open
open scoped Matrix

theorem sec7_form_scalar_of_invariant {K K' : Type} [Field K] [Field K'] [Finite K'] [CharP K' 2]
    {b c : K'} (hirr : ∀ s : K', s ^ 2 + b * s + c ≠ 0)
    {U : Type*} [AddCommGroup U] [Module K U]
    (θ : K ≃+* K') (Ψ : U ≃+ (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K'))
    (hΨ : ∀ (a : K) (u : U), Ψ (a • u) = θ a • Ψ u)
    (β : LinearMap.BilinForm K U) {Γ : Type*} [Group Γ]
    (φ : Γ →* GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K')
    (hφ : φ.range = StatedOmega (StatedQuadMinus 2 K' b c))
    (act : Γ → U → U)
    (hact : ∀ (g : Γ) (u : U), Ψ (act g u) =
      ((φ g : GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K') :
        Matrix (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K') *ᵥ Ψ u)
    (hinv : ∀ (g : Γ) (x y : U), β (act g x) (act g y) = β x y) :
    ∃ κ : K', ∀ x y : U, θ (β x y) = κ * polar (quadMinus 2 K' b c) (Ψ x) (Ψ y) := by
  have hsymm_smul : ∀ (t : K') (v : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K'),
      Ψ.symm (t • v) = θ.symm t • Ψ.symm v := by
    intro t v
    apply Ψ.injective
    rw [Ψ.apply_symm_apply, hΨ, θ.apply_symm_apply, Ψ.apply_symm_apply]
  have hadd_left : ∀ v₁ v₂ w : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K',
      θ (β (Ψ.symm (v₁ + v₂)) (Ψ.symm w)) =
        θ (β (Ψ.symm v₁) (Ψ.symm w)) + θ (β (Ψ.symm v₂) (Ψ.symm w)) := by
    intro v₁ v₂ w
    simp only [_root_.map_add, LinearMap.add_apply]
  have hsmul_left : ∀ (t : K') (v w : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K'),
      θ (β (Ψ.symm (t • v)) (Ψ.symm w)) = t • θ (β (Ψ.symm v) (Ψ.symm w)) := by
    intro t v w
    simp only [hsymm_smul, LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul,
      _root_.map_mul, RingEquiv.apply_symm_apply]
  have hadd_right : ∀ v w₁ w₂ : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K',
      θ (β (Ψ.symm v) (Ψ.symm (w₁ + w₂))) =
        θ (β (Ψ.symm v) (Ψ.symm w₁)) + θ (β (Ψ.symm v) (Ψ.symm w₂)) := by
    intro v w₁ w₂
    simp only [_root_.map_add]
  have hsmul_right : ∀ (t : K') (v w : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K'),
      θ (β (Ψ.symm v) (Ψ.symm (t • w))) = t • θ (β (Ψ.symm v) (Ψ.symm w)) := by
    intro t v w
    simp only [hsymm_smul, LinearMap.map_smul, smul_eq_mul, _root_.map_mul,
      RingEquiv.apply_symm_apply]
  obtain ⟨β', hβ'⟩ : ∃ β' : LinearMap.BilinForm K' (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K'),
      ∀ v w : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K',
        β' v w = θ (β (Ψ.symm v) (Ψ.symm w)) :=
    ⟨LinearMap.mk₂ K' (fun v w => θ (β (Ψ.symm v) (Ψ.symm w)))
      hadd_left hsmul_left hadd_right hsmul_right, fun v w => rfl⟩
  have hsymm : ∀ (g : Γ) (v : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K'),
      Ψ.symm (((φ g : GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K') :
        Matrix (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K') *ᵥ v) =
        act g (Ψ.symm v) := by
    intro g v
    apply Ψ.injective
    rw [Ψ.apply_symm_apply, hact, Ψ.apply_symm_apply]
  have hinv' : ∀ A : GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K',
      A ∈ CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 2 K' b c) →
      ∀ x y : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K',
        β' ((A : Matrix (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2)
          (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K') *ᵥ x)
          ((A : Matrix (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2)
          (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K') *ᵥ y) = β' x y := by
    intro A hA x y
    obtain ⟨g, rfl⟩ : A ∈ φ.range := hφ ▸ hA
    rw [hβ', hβ', hsymm, hsymm, hinv]
  obtain ⟨κ, hκ⟩ := sec7_invariant_form_scalar hirr β' hinv'
  refine ⟨κ, fun x y => ?_⟩
  rw [← hκ (Ψ x) (Ψ y), hβ', Ψ.symm_apply_apply, Ψ.symm_apply_apply]

end CFSG.RankThree.GF2n.Stroth80
