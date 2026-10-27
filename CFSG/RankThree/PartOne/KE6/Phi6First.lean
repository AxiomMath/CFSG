module

public import CFSG.RankThree.PartOne.KE6.Phi6Rigid

public section

namespace CFSG.RankThree.PartOne.KE6

open Matrix CFSG.RankThree.Classical CFSG.RankThree.Classical2
open scoped MatrixGroups

variable {Ω : Type} [Field Ω]

theorem map_map_specialLinearGroup (ς β : Ω →+* Ω) (X : SL(3, Ω)) :
    Matrix.SpecialLinearGroup.map ς (Matrix.SpecialLinearGroup.map β X) =
      Matrix.SpecialLinearGroup.map (ς.comp β) X :=
  Subtype.ext (by
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_map]
    rfl)

theorem rigid_first_pos (ς β : Ω →+* Ω) (hς : Function.Bijective ς) (hβ : Function.Bijective β)
    (k₂ : Subfield Ω) (g₁ h₁ hs : SL(3, Ω)) (A₀ : GL (Fin 3) Ω) (N : SL(3, Ω) →* SL(3, Ω))
    (hN : ∀ X : SL(3, Ω), Matrix.SpecialLinearGroup.toGL (N X) =
      A₀ * Matrix.SpecialLinearGroup.toGL X * A₀⁻¹)
    (h : ∀ A : SL(3, k₂), ∃ z ∈ (Matrix.GeneralLinearGroup.scalar (Fin 3) :
        Ωˣ →* GL (Fin 3) Ω).range,
      Matrix.SpecialLinearGroup.toGL (g₁ * N (Matrix.SpecialLinearGroup.map ς
        (hs * Matrix.SpecialLinearGroup.map β (Matrix.SpecialLinearGroup.map k₂.subtype A) *
          hs⁻¹)) * g₁⁻¹) =
        z * Matrix.SpecialLinearGroup.toGL (h₁ * Matrix.SpecialLinearGroup.map k₂.subtype A *
          h₁⁻¹)) :
    ∀ t ∈ k₂, ς (β t) = t := by
  set τ : Ω ≃+* Ω := RingEquiv.ofBijective (ς.comp β) (hς.comp hβ) with hτ
  have hτ' : τ.toRingHom = ς.comp β := RingHom.ext fun _ => rfl
  intro t ht
  have key := rigid_pos τ k₂ (Matrix.SpecialLinearGroup.toGL g₁ * A₀ *
    Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map ς hs))
    (Matrix.SpecialLinearGroup.toGL h₁) (fun A => ?_) t ht
  · exact key
  obtain ⟨z, hz, hzeq⟩ := h A
  refine ⟨z, hz, ?_⟩
  simp only [map_mul, map_inv, hN, map_map_specialLinearGroup] at hzeq
  rw [hτ']
  refine Eq.trans ?_ hzeq
  group

theorem rigid_first_neg (ς β : Ω →+* Ω) (hς : Function.Bijective ς) (hβ : Function.Bijective β)
    (k₂ : Subfield Ω) (g₁ h₁ hs : SL(3, Ω)) (A₀ : GL (Fin 3) Ω) (N : SL(3, Ω) →* SL(3, Ω))
    (hN : ∀ X : SL(3, Ω), Matrix.SpecialLinearGroup.toGL (N X) =
      A₀ * invTransposeHom (Matrix.SpecialLinearGroup.toGL X) * A₀⁻¹)
    (h : ∀ A : SL(3, k₂), ∃ z ∈ (Matrix.GeneralLinearGroup.scalar (Fin 3) :
        Ωˣ →* GL (Fin 3) Ω).range,
      Matrix.SpecialLinearGroup.toGL (g₁ * N (Matrix.SpecialLinearGroup.map ς
        (hs * Matrix.SpecialLinearGroup.map β (Matrix.SpecialLinearGroup.map k₂.subtype A) *
          hs⁻¹)) * g₁⁻¹) =
        z * Matrix.SpecialLinearGroup.toGL (h₁ * Matrix.SpecialLinearGroup.map k₂.subtype A *
          h₁⁻¹)) :
    False := by
  set τ : Ω ≃+* Ω := RingEquiv.ofBijective (ς.comp β) (hς.comp hβ) with hτ
  have hτ' : τ.toRingHom = ς.comp β := RingHom.ext fun _ => rfl
  refine rigid_neg τ k₂ (Matrix.SpecialLinearGroup.toGL g₁ * A₀ *
    invTransposeHom (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map ς hs)))
    (Matrix.SpecialLinearGroup.toGL h₁) (fun A => ?_)
  obtain ⟨z, hz, hzeq⟩ := h A
  refine ⟨z, hz, ?_⟩
  simp only [map_mul, map_inv, hN, map_map_specialLinearGroup] at hzeq
  rw [hτ']
  refine Eq.trans ?_ hzeq
  group

end CFSG.RankThree.PartOne.KE6
