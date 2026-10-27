module

public import CFSG.Quasithin.Background.F918Z2Core
public import CFSG.Quasithin.Background.F918Z2Act
public import CFSG.Quasithin.Background.F918Z2Model
public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Quasithin.SwapModel

open scoped Matrix

section Data

variable {V : Type} [CommGroup V] {D X : Subgroup (MulAut V)} {F : Type} [Field F] [Finite F]
  {d r : ℕ} {β : V ≃* Multiplicative (Matrix (Fin d) (Fin r) F)}
  {ρ : ↥D →* Matrix.GeneralLinearGroup (Fin d) F}
  {σ : ↥X →* Matrix.GeneralLinearGroup (Fin r) F}

theorem exists_swap_data (hM : IsMatModel D X β ρ σ) (hd : 0 < d) (hr : 0 < r)
    {s : MulAut V} (hDX : X = D.map (MulAut.conj s).toMonoidHom) :
    ∃ (γ : Matrix (Fin d) (Fin d) F →+* Matrix (Fin r) (Fin r) F) (ϑ : F ≃+* F)
      (T : Matrix (Fin r) (Fin d) F),
      (∀ (A : Matrix (Fin d) (Fin d) F) (M : Matrix (Fin d) (Fin r) F),
        matAut β s (A * M) = matAut β s M * (γ A)ᵀ) ∧
      Function.Bijective T.mulVec ∧ ∀ A, γ (A.map ϑ.symm) * T = T * A := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hconj : ∀ g : ↥D, s * (g : MulAut V) * s⁻¹ ∈ X := fun g => by
    rw [hDX]
    exact ⟨g, g.2, by simp⟩
  have hex : ∀ A ∈ Set.range (fun g : ↥D => (ρ g : Matrix (Fin d) (Fin d) F)),
      ∃ B : Matrix (Fin r) (Fin r) F, ∀ m, matAut β s (leftAct F d r A m) =
        rightAct F d r B (matAut β s m) := by
    rintro _ ⟨g, rfl⟩
    refine ⟨(σ ⟨s * g * s⁻¹, hconj g⟩ : Matrix (Fin r) (Fin r) F), fun m => ?_⟩
    exact matAut_mul_left hM s g ⟨s * g * s⁻¹, hconj g⟩ (by simp [mul_assoc]) m
  obtain ⟨γ, hγ⟩ := exists_ringHom_of_intertwine (leftAct F d r) (rightAct F d r)
    (rightAct_injective hd) (matAut β s) (closure_rho_eq_top hd hM) hex
  have hγσ : ∀ x : ↥X, ∃ g : ↥D,
      ((σ x : Matrix.GeneralLinearGroup (Fin r) F) : Matrix (Fin r) (Fin r) F) = γ (ρ g) := by
    intro x
    have hx : (x : MulAut V) ∈ D.map (MulAut.conj s).toMonoidHom := by
      rw [← hDX]
      exact x.2
    obtain ⟨g, hg, hgx⟩ := hx
    refine ⟨⟨g, hg⟩, ?_⟩
    have hsg : s * g = (x : MulAut V) * s := by
      rw [← hgx]
      simp [MulAut.conj_apply, mul_assoc]
    exact eq_of_intertwine (leftAct F d r) (rightAct F d r) (rightAct_injective hd)
      (matAut β s) (fun m => matAut_mul_left hM s ⟨g, hg⟩ x hsg m) (hγ _)
  have hY : ∀ W : Submodule F (Fin r → F),
      (∀ y ∈ Set.range (fun x : ↥X => ((σ x : Matrix.GeneralLinearGroup (Fin r) F) :
        Matrix (Fin r) (Fin r) F)), ∀ w ∈ W, y.mulVec w ∈ W) → W = ⊥ ∨ W = ⊤ :=
    fun W hW => hM.U_irr W fun x w hw => hW _ ⟨x, rfl⟩ w hw
  have hscal : ∀ c : F, ∃ a : F,
      (γ.comp (Matrix.scalar (Fin d))) c = Matrix.scalar (Fin r) a := by
    intro c
    refine exists_scalar_of_pow_card_eq hr hY ?_ ?_
    · rintro _ ⟨x, rfl⟩
      obtain ⟨g, hg⟩ := hγσ x
      show γ (Matrix.scalar (Fin d) c) * _ = _ * γ (Matrix.scalar (Fin d) c)
      beta_reduce
      rw [hg, ← map_mul, ← map_mul,
        (Matrix.scalar_commute c (fun _ => Commute.all _ _) (ρ g : Matrix (Fin d) (Fin d) F)).eq]
    · rw [← map_pow, FiniteField.pow_card]
  obtain ⟨ϑ, hϑ⟩ := exists_ringEquiv_of_scalar hr (γ.comp (Matrix.scalar (Fin d))) hscal
  have hϑ' : ∀ c, γ (Matrix.scalar (Fin d) c) = Matrix.scalar (Fin r) (ϑ c) := hϑ
  have hγinj : Function.Injective γ :=
    injective_of_intertwine (leftAct F d r) (rightAct F d r) (leftAct_injective hr)
      (matAut β s) hγ
  obtain ⟨T, hTi, hT⟩ := exists_matrix_intertwiner hd (untwist γ ϑ) (untwist_smul γ ϑ hϑ')
    (untwist_injective hγinj ϑ)
  have hirr : ∀ W : Submodule F (Fin r → F),
      (∀ A, ∀ w ∈ W, ((untwist γ ϑ) A).mulVec w ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    refine hM.U_irr W fun x w hw => ?_
    obtain ⟨g, hg⟩ := hγσ x
    rw [hg, ← untwist_map_apply γ ϑ (ρ g : Matrix (Fin d) (Fin d) F)]
    exact hW _ w hw
  exact ⟨γ, ϑ, T, fun A M => hγ A M, ⟨hTi, surjective_mulVec_of_irr hd hTi hT hirr⟩,
    fun A => hT A⟩

end Data

section Form

variable {F : Type} [Field F] {d : ℕ}

theorem swap_form_of_data (φ : Matrix (Fin d) (Fin d) F ≃+ Matrix (Fin d) (Fin d) F)
    (γ : Matrix (Fin d) (Fin d) F →+* Matrix (Fin d) (Fin d) F)
    (hγ : ∀ A M, φ (A * M) = φ M * (γ A)ᵀ) (ϑ : F ≃+* F) {T : Matrix (Fin d) (Fin d) F}
    (hT : IsUnit T) (hTγ : ∀ A, γ (A.map ϑ.symm) * T = T * A) :
    ∃ Q R : Matrix (Fin d) (Fin d) F, IsUnit Q ∧ IsUnit R ∧
      ∀ M, φ M = Q * (M.map ϑ)ᵀ * R := by
  have hγM : ∀ M, γ M = T * M.map ϑ * T⁻¹ := fun M => by
    apply eq_mul_mul_inv_of_mul_eq hT
    have := hTγ (M.map ϑ)
    rwa [← untwist_apply, untwist_map_apply] at this
  have hφM : ∀ M, φ M = φ 1 * (γ M)ᵀ := fun M => by
    have := hγ M 1
    rwa [Matrix.mul_one] at this
  have hP : IsUnit (φ 1) := by
    obtain ⟨M, hM⟩ := φ.surjective 1
    have := hφM M
    rw [hM] at this
    exact isUnit_left_of_mul_eq_one this.symm
  have hTinv : IsUnit T⁻¹ := Matrix.isUnit_nonsing_inv_iff.mpr hT
  refine ⟨φ 1 * (T⁻¹)ᵀ, Tᵀ, hP.mul (isUnit_transpose hTinv), isUnit_transpose hT, fun M => ?_⟩
  rw [hφM M, hγM M, Matrix.transpose_mul, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

end Form

section Square

variable {V : Type} [CommGroup V] {D X : Subgroup (MulAut V)} {F : Type} [Field F] [Finite F]

theorem swap_dim_eq {d r : ℕ} {β : V ≃* Multiplicative (Matrix (Fin d) (Fin r) F)}
    {ρ : ↥D →* Matrix.GeneralLinearGroup (Fin d) F}
    {σ : ↥X →* Matrix.GeneralLinearGroup (Fin r) F} (hM : IsMatModel D X β ρ σ) (hd : 0 < d)
    (hr : 0 < r) {s : MulAut V} (hDX : X = D.map (MulAut.conj s).toMonoidHom) : r = d := by
  obtain ⟨_, _, _, -, hTb, -⟩ := exists_swap_data hM hd hr hDX
  exact eq_of_bijective_mulVec hTb.1 hTb.2

theorem swap_form_of_sqModel {d : ℕ} {β : V ≃* Multiplicative (Matrix (Fin d) (Fin d) F)}
    {ρ : ↥D →* Matrix.GeneralLinearGroup (Fin d) F}
    {σ : ↥X →* Matrix.GeneralLinearGroup (Fin d) F} (hM : IsMatModel D X β ρ σ) (hd : 0 < d)
    {s : MulAut V} (hDX : X = D.map (MulAut.conj s).toMonoidHom) :
    ∃ (ϑ : F ≃+* F) (Q R : Matrix (Fin d) (Fin d) F), IsUnit Q ∧ IsUnit R ∧
      ∀ v : V, Multiplicative.toAdd (β (s v)) =
        Q * ((Multiplicative.toAdd (β v)).map ϑ)ᵀ * R := by
  obtain ⟨γ, ϑ, T, hγ, hTb, hT⟩ := exists_swap_data hM hd hd hDX
  have hTu : IsUnit T := Matrix.mulVec_injective_iff_isUnit.mp hTb.1
  obtain ⟨Q, R, hQ, hR, hform⟩ := swap_form_of_data (matAut β s) γ hγ ϑ hTu hT
  refine ⟨ϑ, Q, R, hQ, hR, fun v => ?_⟩
  rw [← matAut_apply β s v]
  exact hform _

end Square

end CFSG.Quasithin.SwapModel
