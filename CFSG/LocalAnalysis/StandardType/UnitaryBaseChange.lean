module

public import CFSG.LocalAnalysis.StandardType.UnitaryAlgClosure
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

public section

namespace CFSG.StandardType

namespace UnitaryBaseChange

open Matrix

variable {F : Type} [Field F] {ι : Type} [Fintype ι] [DecidableEq ι] {Γ : Type*} [Group Γ]

@[expose] noncomputable def baseChangeHom (ρ : Γ →* Matrix ι ι F) :
    Γ →* Matrix ι ι (AlgebraicClosure F) :=
  (RingHom.mapMatrix (algebraMap F (AlgebraicClosure F))).toMonoidHom.comp ρ

theorem baseChangeHom_apply (ρ : Γ →* Matrix ι ι F) (g : Γ) :
    baseChangeHom ρ g = (ρ g).map (algebraMap F (AlgebraicClosure F)) :=
  rfl

theorem baseChangeHom_eq_one_iff (ρ : Γ →* Matrix ι ι F) (g : Γ) :
    baseChangeHom ρ g = 1 ↔ ρ g = 1 := by
  rw [baseChangeHom_apply]
  constructor
  · intro h
    apply UnitaryAlg.map_algebraMap_injective
    change (ρ g).map (algebraMap F (AlgebraicClosure F)) =
      (1 : Matrix ι ι F).map (algebraMap F (AlgebraicClosure F))
    rw [h, Matrix.map_one (algebraMap F (AlgebraicClosure F)) (map_zero _) (map_one _)]
  · intro h
    rw [h, Matrix.map_one (algebraMap F (AlgebraicClosure F)) (map_zero _) (map_one _)]

theorem map_form {σ : F ≃+* F} {σ' : AlgebraicClosure F ≃+* AlgebraicClosure F}
    (hσ' : ∀ x : F, σ' (algebraMap F (AlgebraicClosure F) x) =
      algebraMap F (AlgebraicClosure F) (σ x))
    (A G : Matrix ι ι F) :
    (A.map (algebraMap F (AlgebraicClosure F)))ᵀ * G.map (algebraMap F (AlgebraicClosure F)) *
        (A.map (algebraMap F (AlgebraicClosure F))).map σ' =
      (Aᵀ * G * A.map σ).map (algebraMap F (AlgebraicClosure F)) := by
  have hσ'' : (A.map (algebraMap F (AlgebraicClosure F))).map σ' =
      (A.map σ).map (algebraMap F (AlgebraicClosure F)) := by
    ext i j
    simp only [Matrix.map_apply]
    exact hσ' (A i j)
  rw [← Matrix.transpose_map, hσ'', ← Matrix.map_mul, ← Matrix.map_mul]

theorem baseChangeHom_form {σ : F ≃+* F} {σ' : AlgebraicClosure F ≃+* AlgebraicClosure F}
    (hσ' : ∀ x : F, σ' (algebraMap F (AlgebraicClosure F) x) =
      algebraMap F (AlgebraicClosure F) (σ x))
    {G : Matrix ι ι F} (ρ : Γ →* Matrix ι ι F) (hρ : ∀ g, (ρ g)ᵀ * G * (ρ g).map σ = G) (g : Γ) :
    (baseChangeHom ρ g)ᵀ * G.map (algebraMap F (AlgebraicClosure F)) * (baseChangeHom ρ g).map σ' =
      G.map (algebraMap F (AlgebraicClosure F)) := by
  rw [baseChangeHom_apply]
  rw [map_form hσ' (ρ g) G, hρ g]

theorem map_ne_smul_one {M : Matrix ι ι F} (hM : ∀ c : F, M ≠ c • 1) (e : AlgebraicClosure F) :
    M.map (algebraMap F (AlgebraicClosure F)) ≠ e • 1 := by
  intro h
  by_cases hne : Nonempty ι
  · obtain ⟨i₀⟩ := hne
    have hinj : Function.Injective (algebraMap F (AlgebraicClosure F)) :=
      (algebraMap F (AlgebraicClosure F)).injective
    have hoff : ∀ i j : ι, i ≠ j → M i j = 0 := by
      intro i j hij
      apply hinj
      have hh : (M.map (algebraMap F (AlgebraicClosure F))) i j =
          (e • (1 : Matrix ι ι (AlgebraicClosure F))) i j := by rw [h]
      rw [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, if_neg hij] at hh
      simpa using hh
    have hdiag : ∀ i : ι, M i i = M i₀ i₀ := by
      intro i
      apply hinj
      have hi : (M.map (algebraMap F (AlgebraicClosure F))) i i =
          (e • (1 : Matrix ι ι (AlgebraicClosure F))) i i := by rw [h]
      have h0 : (M.map (algebraMap F (AlgebraicClosure F))) i₀ i₀ =
          (e • (1 : Matrix ι ι (AlgebraicClosure F))) i₀ i₀ := by rw [h]
      rw [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, if_pos rfl] at hi
      rw [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, if_pos rfl] at h0
      rw [hi, h0]
    have hMscal : M = (M i₀ i₀) • 1 := by
      ext i j
      by_cases hij : i = j
      · subst hij
        rw [Matrix.smul_apply, Matrix.one_apply, if_pos rfl, smul_eq_mul, mul_one]
        exact hdiag i
      · rw [Matrix.smul_apply, Matrix.one_apply, if_neg hij, smul_zero]
        exact hoff i j hij
    exact hM (M i₀ i₀) hMscal
  · have hMone : M = 1 := by
      ext i j
      exact (hne ⟨i⟩).elim
    exact hM 1 (by rw [one_smul]; exact hMone)

end UnitaryBaseChange

end CFSG.StandardType

