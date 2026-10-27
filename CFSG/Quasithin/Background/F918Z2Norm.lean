module

public import CFSG.Quasithin.Background.F918Z2Core
public import CFSG.Quasithin.Background.F918Z2Act
public import CFSG.Quasithin.Background.F918Z2Model
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Quasithin.SwapModel

open scoped Matrix

variable {V : Type} [CommGroup V] {D X : Subgroup (MulAut V)} {F : Type} [Field F] {d : ℕ}
  {β : V ≃* Multiplicative (Matrix (Fin d) (Fin d) F)}
  {ρ : ↥D →* Matrix.GeneralLinearGroup (Fin d) F}
  {σ : ↥X →* Matrix.GeneralLinearGroup (Fin d) F}

theorem exists_normalizer_data (hM : IsMatModel D X β ρ σ) (hd : 0 < d) {a : MulAut V}
    (haD : D.map (MulAut.conj a).toMonoidHom = D) :
    ∃ α : Matrix (Fin d) (Fin d) F →+* Matrix (Fin d) (Fin d) F, Function.Injective α ∧
      ∀ A M : Matrix (Fin d) (Fin d) F, matAut β a (A * M) = α A * matAut β a M := by
  have hconj : ∀ g : ↥D, a * (g : MulAut V) * a⁻¹ ∈ D := fun g => by
    have h : a * (g : MulAut V) * a⁻¹ ∈ D.map (MulAut.conj a).toMonoidHom := ⟨g, g.2, by simp⟩
    rwa [haD] at h
  have hex : ∀ A ∈ Set.range (fun g : ↥D => (ρ g : Matrix (Fin d) (Fin d) F)),
      ∃ B : Matrix (Fin d) (Fin d) F, ∀ m, matAut β a (leftAct F d d A m) =
        leftAct F d d B (matAut β a m) := by
    rintro _ ⟨g, rfl⟩
    refine ⟨(ρ ⟨a * g * a⁻¹, hconj g⟩ : Matrix (Fin d) (Fin d) F), fun m => ?_⟩
    exact matAut_mul_left_of_normalizes hM a g ⟨a * g * a⁻¹, hconj g⟩ (by simp [mul_assoc]) m
  obtain ⟨α, hα⟩ := exists_ringHom_of_intertwine (leftAct F d d) (leftAct F d d)
    (leftAct_injective hd) (matAut β a) (closure_rho_eq_top hd hM) hex
  exact ⟨α, injective_of_intertwine (leftAct F d d) (leftAct F d d) (leftAct_injective hd)
    (matAut β a) hα, fun A M => hα A M⟩

end CFSG.Quasithin.SwapModel

namespace CFSG.Quasithin

open scoped Matrix

variable {V : Type} [CommGroup V] {D X : Subgroup (MulAut V)} {F : Type} [Field F] [Finite F]
  {d : ℕ} {β : V ≃* Multiplicative (Matrix (Fin d) (Fin d) F)}
  {ρ : ↥D →* Matrix.GeneralLinearGroup (Fin d) F}
  {σ : ↥X →* Matrix.GeneralLinearGroup (Fin d) F}

theorem normalizer_form_of_sqModel_left (hM : IsMatModel D X β ρ σ) (hd : 0 < d) {a : MulAut V}
    (haD : D.map (MulAut.conj a).toMonoidHom = D) :
    ∃ (ϑ : F ≃+* F) (B₁ B₂ : Matrix (Fin d) (Fin d) F), IsUnit B₁ ∧ IsUnit B₂ ∧
      ∀ v : V, Multiplicative.toAdd (β (a v)) =
        B₁ * (Multiplicative.toAdd (β v)).map ϑ * B₂ := by
  obtain ⟨α, hαinj, hα⟩ := SwapModel.exists_normalizer_data hM hd haD
  obtain ⟨ϑ, T, hT, hαT⟩ := SwapModel.exists_conj_of_ringHom hd α hαinj
  have hφM : ∀ M, SwapModel.matAut β a M = α M * SwapModel.matAut β a 1 := fun M => by
    have := hα M 1
    rwa [Matrix.mul_one] at this
  have hP : IsUnit (SwapModel.matAut β a 1) := by
    obtain ⟨M, hM1⟩ := (SwapModel.matAut β a).surjective 1
    have := hφM M
    rw [hM1] at this
    exact SwapModel.isUnit_right_of_mul_eq_one this.symm
  have hTinv : IsUnit T⁻¹ := Matrix.isUnit_nonsing_inv_iff.mpr hT
  refine ⟨ϑ, T, T⁻¹ * SwapModel.matAut β a 1, hT, hTinv.mul hP, fun v => ?_⟩
  rw [← SwapModel.matAut_apply β a v, hφM, hαT, Matrix.mul_assoc, Matrix.mul_assoc]

theorem normalizer_form_of_sqModel (hM : IsMatModel D X β ρ σ) (hd : 0 < d) {a : MulAut V}
    (haD : D.map (MulAut.conj a).toMonoidHom = D)
    (_haX : X.map (MulAut.conj a).toMonoidHom = X) :
    ∃ (ϑ : F ≃+* F) (B₁ B₂ : Matrix (Fin d) (Fin d) F), IsUnit B₁ ∧ IsUnit B₂ ∧
      ∀ v : V, Multiplicative.toAdd (β (a v)) =
        B₁ * (Multiplicative.toAdd (β v)).map ϑ * B₂ :=
  normalizer_form_of_sqModel_left hM hd haD

end CFSG.Quasithin
