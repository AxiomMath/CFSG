module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} {U : Type} [AddCommGroup U] [Module (ZMod p) U] {n : ℕ}

theorem diagMap_apply_basis (b : Module.Basis (Fin n) (ZMod p) U) (d : Fin n → (ZMod p)ˣ)
    (k : Fin n) : diagMap p b d (b k) = (d k : ZMod p) • b k := by
  rw [diagMap]
  have h1 : (LinearEquiv.piCongrRight fun i => LinearEquiv.smulOfUnit (d i))
      (b.equivFun (b k)) = Pi.single k (d k : ZMod p) := by
    funext j
    rw [LinearEquiv.piCongrRight_apply, LinearEquiv.smulOfUnit,
      DistribMulAction.toLinearEquiv_apply, Module.Basis.equivFun_self]
    by_cases hjk : j = k
    · subst hjk; simp [Units.smul_def]
    · rw [if_neg (Ne.symm hjk), smul_zero, Pi.single_eq_of_ne hjk]
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, h1, Module.Basis.equivFun_symm_apply,
    Finset.sum_eq_single k]
  · simp
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, zero_smul]
  · intro hk
    exact (hk (Finset.mem_univ k)).elim

theorem permMap_apply_basis (b : Module.Basis (Fin n) (ZMod p) U) (σ : Equiv.Perm (Fin n))
    (k : Fin n) : permMap p b σ (b k) = b (σ k) := by
  rw [permMap, Module.Basis.equiv_apply]

theorem diagMap_mul (b : Module.Basis (Fin n) (ZMod p) U) (d d' : Fin n → (ZMod p)ˣ) :
    diagMap p b d * diagMap p b d' = diagMap p b (d * d') := by
  refine b.ext' fun k => ?_
  rw [LinearEquiv.mul_apply, diagMap_apply_basis, map_smul, diagMap_apply_basis,
    diagMap_apply_basis, Pi.mul_apply, Units.val_mul, mul_comm (d k : ZMod p) (d' k), smul_smul]

theorem diagMap_one (b : Module.Basis (Fin n) (ZMod p) U) : diagMap p b 1 = 1 := by
  refine b.ext' fun k => ?_
  rw [diagMap_apply_basis]
  simp

theorem permMap_mul (b : Module.Basis (Fin n) (ZMod p) U) (σ τ : Equiv.Perm (Fin n)) :
    permMap p b σ * permMap p b τ = permMap p b (σ * τ) := by
  refine b.ext' fun k => ?_
  rw [LinearEquiv.mul_apply, permMap_apply_basis, permMap_apply_basis, permMap_apply_basis]
  rfl

theorem permMap_mul_diagMap_mul_inv (b : Module.Basis (Fin n) (ZMod p) U)
    (σ : Equiv.Perm (Fin n)) (d : Fin n → (ZMod p)ˣ) :
    permMap p b σ * diagMap p b d * (permMap p b σ)⁻¹ = diagMap p b (d ∘ σ.symm) := by
  have h : permMap p b σ * diagMap p b d = diagMap p b (d ∘ σ.symm) * permMap p b σ := by
    refine b.ext' fun k => ?_
    simp only [LinearEquiv.mul_apply, diagMap_apply_basis, map_smul, permMap_apply_basis,
      Function.comp_apply, Equiv.symm_apply_apply]
  calc permMap p b σ * diagMap p b d * (permMap p b σ)⁻¹
      = (diagMap p b (d ∘ σ.symm) * permMap p b σ) * (permMap p b σ)⁻¹ := by rw [h]
    _ = diagMap p b (d ∘ σ.symm) * (permMap p b σ * (permMap p b σ)⁻¹) := by rw [mul_assoc]
    _ = diagMap p b (d ∘ σ.symm) := by rw [mul_inv_cancel, mul_one]

theorem eq_diagMap_mul_permMap (b : Module.Basis (Fin n) (ZMod p) U) {g : U ≃ₗ[ZMod p] U}
    (σ : Equiv.Perm (Fin n)) (c : Fin n → (ZMod p)ˣ)
    (hg : ∀ i, g (b i) = (c i : ZMod p) • b (σ i)) :
    g = diagMap p b (c ∘ σ.symm) * permMap p b σ := by
  refine b.ext' fun i => ?_
  simp only [hg i, LinearEquiv.mul_apply, permMap_apply_basis, diagMap_apply_basis,
    Function.comp_apply, Equiv.symm_apply_apply]

theorem pairUnit_mul (i j : Fin n) (c c' : (ZMod p)ˣ) :
    pairUnit p i j (c * c') = pairUnit p i j c * pairUnit p i j c' := by
  funext k
  by_cases hki : k = i
  · subst hki; simp [pairUnit]
  · by_cases hkj : k = j
    · subst hkj; simp [pairUnit, hki, mul_comm]
    · simp [pairUnit, hki, hkj]

theorem pairUnit_one (i j : Fin n) : pairUnit p i j 1 = 1 := by
  funext k
  by_cases hki : k = i
  · simp [pairUnit, hki]
  · by_cases hkj : k = j
    · simp [pairUnit, hkj]
    · simp [pairUnit, hki, hkj]

end CFSG.StandardType.ZS
