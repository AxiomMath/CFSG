module

public import CFSG.Quasithin.Background.GoldschmidtD35CoreStab

public section

namespace CFSG.Quasithin.D35Core

open CFSG.QuasithinUnique.Setup.X3 CFSG.QuasithinUnique.Setup.Offender Equiv
open scoped LinearAlgebra.Projectivization

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]

theorem repr_sum' (b : Module.Basis (Fin 3) F V) (c : Fin 3 → F) (j : Fin 3) :
    b.repr (∑ i, c i • b i) j = c j :=
  congrFun (b.repr_sum_self c) j

@[expose] noncomputable def semiPerm (b : Module.Basis (Fin 3) F V) (σ : F ≃+* F) : Perm V where
  toFun v := ∑ i, σ (b.repr v i) • b i
  invFun v := ∑ i, σ.symm (b.repr v i) • b i
  left_inv v := by
    beta_reduce
    simp only [repr_sum', RingEquiv.symm_apply_apply]
    exact b.sum_repr v
  right_inv v := by
    beta_reduce
    simp only [repr_sum', RingEquiv.apply_symm_apply]
    exact b.sum_repr v

theorem semiPerm_apply (b : Module.Basis (Fin 3) F V) (σ : F ≃+* F) (v : V) :
    semiPerm b σ v = ∑ i, σ (b.repr v i) • b i := rfl

theorem repr_semiPerm (b : Module.Basis (Fin 3) F V) (σ : F ≃+* F) (v : V) (j : Fin 3) :
    b.repr (semiPerm b σ v) j = σ (b.repr v j) := by
  rw [semiPerm_apply, repr_sum']

theorem semiPerm_add (b : Module.Basis (Fin 3) F V) (σ : F ≃+* F) (x y : V) :
    semiPerm b σ (x + y) = semiPerm b σ x + semiPerm b σ y := by
  simp only [semiPerm_apply, map_add, Finsupp.add_apply, add_smul, Finset.sum_add_distrib]

theorem semiPerm_smul (b : Module.Basis (Fin 3) F V) (σ : F ≃+* F) (c : F) (w : V) :
    semiPerm b σ (c • w) = σ c • semiPerm b σ w := by
  simp only [semiPerm_apply, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, mul_smul,
    Finset.smul_sum]

theorem semiPerm_mem (b : Module.Basis (Fin 3) F V) (σ : F ≃+* F) :
    semiPerm b σ ∈ gammaL F V :=
  ⟨semiPerm_add b σ, σ, semiPerm_smul b σ⟩

theorem semiPerm_basis (b : Module.Basis (Fin 3) F V) (σ : F ≃+* F) (i : Fin 3) :
    semiPerm b σ (b i) = b i := by
  rw [semiPerm_apply, Finset.sum_eq_single i]
  · simp
  · intro x _ hx
    simp [hx]
  · simp

theorem exists_conj_linear (n : gammaL F V) (g : V ≃ₗ[F] V) :
    ∃ g' : V ≃ₗ[F] V, ∀ v, g' v = n.1 (g (n.1⁻¹ v)) := by
  obtain ⟨hadd, σ, hσ⟩ := n.2
  have hadd' : ∀ x y, n.1⁻¹ (x + y) = n.1⁻¹ x + n.1⁻¹ y := fun x y => by
    apply n.1.injective
    rw [hadd]
    simp
  have hsm' : ∀ (c : F) (w : V), n.1⁻¹ (c • w) = σ.symm c • n.1⁻¹ w := fun c w => by
    apply n.1.injective
    rw [hσ]
    simp
  refine ⟨{ toFun := fun v => n.1 (g (n.1⁻¹ v))
            invFun := fun v => n.1 (g.symm (n.1⁻¹ v))
            left_inv := fun v => by simp
            right_inv := fun v => by simp
            map_add' := fun x y => by rw [hadd', map_add, hadd]
            map_smul' := fun c v => by
              rw [hsm', map_smul, hσ]
              simp }, fun v => rfl⟩

theorem lineAction_conj_apply {pt : Fin 6 → ℙ F V} {n : gammaL F V} {σ π : Perm (Fin 6)}
    (hn : ∀ i, pointAct n (pt i) = pt (σ i)) {g g' : V ≃ₗ[F] V}
    (hg : ∀ i, lineAction F V g (pt i) = pt (π i)) (hg' : ∀ v, g' v = n.1 (g (n.1⁻¹ v)))
    (i : Fin 6) : lineAction F V g' (pt i) = pt (σ (π (σ⁻¹ i))) := by
  have hconj : toGamma F V g' = n * toGamma F V g * n⁻¹ := by
    apply Subtype.ext
    apply Equiv.ext
    intro v
    exact hg' v
  have hinv : pointAct n⁻¹ (pt i) = pt (σ⁻¹ i) := by
    calc pointAct n⁻¹ (pt i) = pointAct n⁻¹ (pointAct n (pt (σ⁻¹ i))) := by rw [hn]; simp
      _ = pointAct (n⁻¹ * n) (pt (σ⁻¹ i)) := (pointAct_mul _ _ _).symm
      _ = pt (σ⁻¹ i) := by rw [inv_mul_cancel, pointAct_one]
  change pointAct (toGamma F V g') (pt i) = _
  rw [hconj, pointAct_mul, pointAct_mul, hinv]
  change pointAct n (lineAction F V g (pt (σ⁻¹ i))) = _
  rw [hg, hn]

theorem IsSixOrbit.exists_conj_mem [FiniteDimensional F V] {L : Subgroup (V ≃ₗ[F] V)}
    {pt : Fin 6 → ℙ F V} (hV : Module.finrank F V = 3) (hO : IsSixOrbit L pt)
    (hirr : ∀ W : Submodule F V, (∀ g ∈ L, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hscal : ∀ c : Fˣ, scalarHom F V c ∈ L) {n : gammaL F V} {σ : Perm (Fin 6)}
    (hn : ∀ i, pointAct n (pt i) = pt (σ i)) {g : V ≃ₗ[F] V} (hg : g ∈ L) :
    ∃ g' ∈ L, ∀ v, g' v = n.1 (g (n.1⁻¹ v)) := by
  obtain ⟨g', hg'⟩ := exists_conj_linear n g
  obtain ⟨π, hπ⟩ := hO.exists_perm (fun i => hO.mem g hg i)
  exact ⟨g', hO.mem_of_preserves hV hirr hscal
    (fun i => ⟨σ (π (σ⁻¹ i)), lineAction_conj_apply hn hπ hg' i⟩), hg'⟩

end CFSG.Quasithin.D35Core
