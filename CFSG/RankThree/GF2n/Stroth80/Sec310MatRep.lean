module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.RankThree.GF2n.Stroth80

open scoped Matrix

@[expose] noncomputable def matrixLinEquiv (m : ℕ) (K : Type) [Field K] :
    GL (Fin m) K ≃* ((Fin m → K) ≃ₗ[K] (Fin m → K)) :=
  Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin m → K))

theorem matrixLinEquiv_apply {m : ℕ} {K : Type} [Field K] (A : GL (Fin m) K)
    (v : Fin m → K) :
    matrixLinEquiv m K A v = (A : Matrix (Fin m) (Fin m) K) *ᵥ v :=
  rfl

theorem exists_matrixRep_of_linearRep {K : Type} [Field K] {W : Type} [AddCommGroup W]
    [Module K W] [Module.Finite K W] {m : ℕ} (hW : Module.finrank K W = m) {R : Type} [Group R]
    (ρ : R →* (W ≃ₗ[K] W)) :
    ∃ (φ : R →* GL (Fin m) K) (c : W ≃ₗ[K] (Fin m → K)),
      (∀ (r : R) (w : W), c (ρ r w) = (φ r : Matrix (Fin m) (Fin m) K) *ᵥ c w) ∧
        φ.ker = ρ.ker := by
  obtain ⟨c⟩ : Nonempty (W ≃ₗ[K] (Fin m → K)) :=
    ⟨(Module.finBasisOfFinrankEq K W hW).equivFun⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : R →* ((Fin m → K) ≃ₗ[K] (Fin m → K)),
      ∀ (r : R) (v : Fin m → K), ψ r v = c (ρ r (c.symm v)) :=
    ⟨{ toFun := fun r => c.symm.trans ((ρ r).trans c)
       map_one' := by
         ext v
         simp
       map_mul' := by
         intro r s
         ext v
         simp [map_mul] }, fun r v => rfl⟩
  refine ⟨(matrixLinEquiv m K).symm.toMonoidHom.comp ψ, c, ?_, ?_⟩
  · intro r w
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← matrixLinEquiv_apply,
      MulEquiv.apply_symm_apply, hψ, LinearEquiv.symm_apply_apply]
  · ext r
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
    constructor
    · intro h
      ext w
      apply c.injective
      have h2 : ψ r (c w) = (1 : (Fin m → K) ≃ₗ[K] (Fin m → K)) (c w) := by
        rw [h]
      rw [hψ, LinearEquiv.symm_apply_apply] at h2
      simpa using h2
    · intro h
      ext v
      rw [hψ, h]
      simp

@[expose] noncomputable def actionOnSubspace {R : Type} [Group R] {K E : Type} [Field K]
    [AddCommGroup E] [Module K E] (φ : R →* (E ≃ₗ[K] E)) (W : Submodule K E)
    (hW : ∀ r, ∀ w ∈ W, φ r w ∈ W) : R →* (W ≃ₗ[K] W) where
  toFun r := LinearEquiv.ofSubmodules (φ r) W W (by
    apply le_antisymm
    · rintro _ ⟨w, hw, rfl⟩
      exact hW r w hw
    · intro w hw
      refine ⟨φ r⁻¹ w, hW r⁻¹ w hw, ?_⟩
      show φ r (φ r⁻¹ w) = w
      rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl)
  map_one' := by
    apply LinearEquiv.ext
    intro w
    apply Subtype.ext
    simp [LinearEquiv.ofSubmodules_apply]
  map_mul' := by
    intro r s
    apply LinearEquiv.ext
    intro w
    apply Subtype.ext
    simp [LinearEquiv.ofSubmodules_apply]

theorem actionOnSubspace_apply {R : Type} [Group R] {K E : Type} [Field K] [AddCommGroup E]
    [Module K E] (φ : R →* (E ≃ₗ[K] E)) (W : Submodule K E) (hW : ∀ r, ∀ w ∈ W, φ r w ∈ W)
    (r : R) (w : W) : ((actionOnSubspace φ W hW r w : W) : E) = φ r (w : E) := by
  simp [actionOnSubspace, LinearEquiv.ofSubmodules_apply]


theorem matrix_eq_of_forall_mulVec {m : ℕ} {K : Type} [Field K] {A B : Matrix (Fin m) (Fin m) K}
    (h : ∀ x, A *ᵥ x = B *ᵥ x) : A = B :=
  Matrix.toLin'.injective (LinearMap.ext fun x => by simpa [Matrix.toLin'_apply] using h x)

theorem mulVec_one_add_vecMulVec {m : ℕ} {K : Type} [Field K] (u f x : Fin m → K) :
    (1 + Matrix.vecMulVec u f) *ᵥ x = x + (f ⬝ᵥ x) • u := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec]
  simp

theorem exists_vecMulVec_of_sub_smul {m : ℕ} {K : Type} [Field K] {u : Fin m → K}
    {A : Matrix (Fin m) (Fin m) K} (hA : ∀ x, ∃ s : K, A *ᵥ x - x = s • u) :
    ∃ f : Fin m → K, A = 1 + Matrix.vecMulVec u f := by
  choose s hs using hA
  refine ⟨fun j => s (Pi.single j 1), ?_⟩
  ext i j
  have h1 := congrFun (hs (Pi.single j 1)) i
  rw [Matrix.mulVec_single_one] at h1
  simp only [Pi.sub_apply, Matrix.col_apply, Pi.smul_apply, smul_eq_mul] at h1
  rw [Matrix.add_apply, Matrix.vecMulVec_apply]
  have h2 : (Pi.single j (1 : K) : Fin m → K) i = (1 : Matrix (Fin m) (Fin m) K) i j := by
    rw [Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      simp
    · rw [Pi.single_eq_of_ne hij, if_neg hij]
  rw [h2] at h1
  rw [mul_comm] at h1
  linear_combination h1


theorem exists_matrix_of_elation_action {m : ℕ} {K E : Type} [Field K] [AddCommGroup E]
    [Module K E] {W : Submodule K E} (c : W ≃ₗ[K] (Fin m → K)) {b : E} (hbW : b ∈ W)
    (hb0 : b ≠ 0) (T : E ≃ₗ[K] E) (hTW : ∀ w ∈ W, T w ∈ W) (A : Matrix (Fin m) (Fin m) K)
    (hA : ∀ w : W, A *ᵥ c w = c ⟨T w, hTW w w.2⟩) (hTb : T b = b)
    (hTw : ∀ w : W, ∃ s : K, T w - w = s • b) :
    ∃ f : Fin m → K, f ⬝ᵥ c ⟨b, hbW⟩ = 0 ∧ A = 1 + Matrix.vecMulVec (c ⟨b, hbW⟩) f := by
  have hu0 : c ⟨b, hbW⟩ ≠ 0 := fun h0 =>
    hb0 (congrArg Subtype.val (c.injective (h0.trans c.map_zero.symm)))
  have hA' : ∀ x, ∃ s : K, A *ᵥ x - x = s • c ⟨b, hbW⟩ := by
    intro x
    obtain ⟨s, hs⟩ := hTw (c.symm x)
    refine ⟨s, ?_⟩
    have h1 := hA (c.symm x)
    rw [LinearEquiv.apply_symm_apply] at h1
    rw [h1]
    have h2 : (⟨T (c.symm x : E), hTW _ (c.symm x).2⟩ : W) - c.symm x =
        s • (⟨b, hbW⟩ : W) := Subtype.ext hs
    have h3 : c ⟨T (c.symm x : E), hTW _ (c.symm x).2⟩ - c (c.symm x) = s • c ⟨b, hbW⟩ := by
      rw [← map_sub, h2, map_smul]
    rw [LinearEquiv.apply_symm_apply] at h3
    exact h3
  obtain ⟨f, hf⟩ := exists_vecMulVec_of_sub_smul hA'
  refine ⟨f, ?_, hf⟩
  have h3 := hA ⟨b, hbW⟩
  have h4 : (⟨T ((⟨b, hbW⟩ : W) : E), hTW _ hbW⟩ : W) = ⟨b, hbW⟩ := Subtype.ext hTb
  rw [h4] at h3
  have h5 : (1 + Matrix.vecMulVec (c ⟨b, hbW⟩) f) *ᵥ c ⟨b, hbW⟩ = c ⟨b, hbW⟩ := by
    rw [← hf]
    exact h3
  rw [mulVec_one_add_vecMulVec] at h5
  have h6 : (f ⬝ᵥ c ⟨b, hbW⟩) • c ⟨b, hbW⟩ = 0 := by
    have := congrArg (fun z => z - c ⟨b, hbW⟩) h5
    simpa using this
  rcases smul_eq_zero.mp h6 with h7 | h7
  · exact h7
  · exact absurd h7 hu0

theorem elation_action_of_matrix {m : ℕ} {K E : Type} [Field K] [AddCommGroup E] [Module K E]
    {W : Submodule K E} (c : W ≃ₗ[K] (Fin m → K)) {b : E} (hbW : b ∈ W) (T : E ≃ₗ[K] E)
    (hTW : ∀ w ∈ W, T w ∈ W) (A : Matrix (Fin m) (Fin m) K)
    (hA : ∀ w : W, A *ᵥ c w = c ⟨T w, hTW w w.2⟩) {f : Fin m → K}
    (hf : A = 1 + Matrix.vecMulVec (c ⟨b, hbW⟩) f) (w : W) :
    T w = w + (f ⬝ᵥ c w) • b := by
  have h1 := hA w
  rw [hf, mulVec_one_add_vecMulVec] at h1
  have h2 : (⟨T w, hTW w w.2⟩ : W) = w + (f ⬝ᵥ c w) • (⟨b, hbW⟩ : W) := by
    apply c.injective
    rw [map_add, map_smul]
    exact h1.symm
  exact congrArg Subtype.val h2

end CFSG.RankThree.GF2n.Stroth80
