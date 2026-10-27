module

public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLLinePSL

public section

namespace CFSG.StandardType.LinUnitL

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification CFSG.Assembly TypeA TypeANbrDvd

variable {d p : ℕ} {K : Type} [Field K]

theorem conj_proj_eq_conjAut (g : SpecialLinearGroup (Fin d) K) :
    MulAut.conj (proj d K g) = conjAut d K (SpecialLinearGroup.toGL g) := by
  ext r
  obtain ⟨h, rfl⟩ := proj_surjective d K r
  rw [MulAut.conj_apply, conjAut_proj, slConjugation_toGL_eq, map_mul, map_mul, map_inv]

@[expose] noncomputable def rootGL {ζ : K} (hζ0 : ζ ≠ 0) {i j : Fin d} (hij : i ≠ j) :
    GL (Fin d) K :=
  SpecialLinearGroup.toGL (diagSLOf (rootT ζ i j) (prod_rootT hζ0 hij))

theorem coe_rootGL {ζ : K} (hζ0 : ζ ≠ 0) {i j : Fin d} (hij : i ≠ j) :
    ((rootGL hζ0 hij : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (rootT ζ i j) :=
  rfl

variable [Finite K] [CharP K 2]

omit [CharP K 2] in
theorem mapsTo_unitriangular_of_comm_rootT (hp : p.Prime) (hp2 : p ≠ 2) (hd : 5 ≤ d) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) {φ : MulAut (projectiveSL d K)} (hodd : Odd (orderOf φ))
    (hcomm : ∀ (i j : Fin d) (hij : i ≠ j),
      φ * conjAut d K (rootGL (hζ.ne_zero hp.ne_zero) hij) =
        conjAut d K (rootGL (hζ.ne_zero hp.ne_zero) hij) * φ) :
    ∀ u ∈ projUnitriangular d K, φ u ∈ projUnitriangular d K := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  have hζ1 : ζ ≠ 1 := hζ.ne_one hp.one_lt
  obtain ⟨A, σ, rfl⟩ := mem_semilinearAutGroup_iff.mp
    (CFSG.ComponentClassification.UnbalancedCatalog.EvenLinearSL.mem_semilinearAutGroup_of_odd
      (by omega) hodd)
  have hσζ : σ ζ ≠ (σ ζ)⁻¹ := ne_inv_of_isPrimitiveRoot (hζ.map_of_injective σ.injective) hp hp2
  have hσr : ∀ i j : Fin d, (fun k => (σ : K →+* K) (rootT ζ i j k)) = rootT (σ ζ) i j := by
    intro i j
    funext k
    unfold rootT
    split_ifs <;> simp [map_inv₀]
  have hkey : ∀ (i j : Fin d) (hij : i ≠ j), ∃ c : K,
      (A : Matrix (Fin d) (Fin d) K) * diagonal (rootT (σ ζ) i j) =
        diagonal (fun k => rootT ζ i j k * c) * (A : Matrix (Fin d) (Fin d) K) := by
    intro i j hij
    set D := rootGL hζ0 hij with hD
    have h1 : conjAut d K (A * GeneralLinearGroup.map (σ : K →+* K) D * A⁻¹) = conjAut d K D := by
      rw [← conjAut_semilinear_conj, hcomm i j hij, mul_inv_cancel_right]
    obtain ⟨c, hc⟩ := exists_scalar_of_conjAut_eq_one
      (A := D⁻¹ * (A * GeneralLinearGroup.map (σ : K →+* K) D * A⁻¹))
      (by rw [map_mul, map_inv, h1, inv_mul_cancel])
    refine ⟨c, ?_⟩
    have e : (A * GeneralLinearGroup.map (σ : K →+* K) D : GL (Fin d) K) =
        D * (D⁻¹ * (A * GeneralLinearGroup.map (σ : K →+* K) D * A⁻¹)) * A := by group
    have h2 : (A : Matrix (Fin d) (Fin d) K) *
        ((GeneralLinearGroup.map (σ : K →+* K) D : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        (D : Matrix (Fin d) (Fin d) K) * scalar (Fin d) c * (A : Matrix (Fin d) (Fin d) K) := by
      rw [← Units.val_mul, e, Units.val_mul, Units.val_mul, hc]
    rw [coe_map_GL, hD, coe_rootGL, diagonal_map (map_zero _), hσr, scalar_apply,
      diagonal_mul_diagonal] at h2
    exact h2
  obtain ⟨π, hπ⟩ := exists_perm_mul_diagonal hσζ A (fun i j hij => by
    obtain ⟨c, hc⟩ := hkey i j hij
    exact ⟨_, hc⟩)
  have hrel : ∀ (i j : Fin d) (hij : i ≠ j), ∃ c : K,
      ∀ k, rootT (σ ζ) i j (π k) = rootT ζ i j k * c := by
    intro i j hij
    obtain ⟨c, hc⟩ := hkey i j hij
    rw [hπ] at hc
    have hc' := congrArg (· * ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) hc
    simp only [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.mul_one] at hc'
    refine ⟨c, fun k => ?_⟩
    have := congrFun (congrFun hc' k) k
    simpa [diagonal_apply_eq] using this
  have hrel1 : ∀ (i j : Fin d), i ≠ j → ∀ k, rootT (σ ζ) i j (π k) = rootT ζ i j k := by
    intro i j hij k
    obtain ⟨c, hc⟩ := hrel i j hij
    obtain ⟨m, hmi, hmj, hmi', hmj'⟩ := exists_ne_of_four hd i j (π.symm i) (π.symm j)
    have h1 := hc m
    have hπmi : π m ≠ i := fun h => hmi' (by rw [← h, Equiv.symm_apply_apply])
    have hπmj : π m ≠ j := fun h => hmj' (by rw [← h, Equiv.symm_apply_apply])
    rw [rootT_other _ hπmi hπmj, rootT_other _ hmi hmj, one_mul] at h1
    rw [hc k, ← h1, mul_one]
  have hπ1 : ∀ k, π k = k := by
    intro k
    by_contra hk
    obtain ⟨j, hjk, hjπ⟩ := exists_ne_of_two (by omega) k (π k)
    have h1 := hrel1 k j (Ne.symm hjk) k
    rw [rootT_other _ hk (Ne.symm hjπ), rootT_left] at h1
    exact hζ1 h1.symm
  have hAd : (A : Matrix (Fin d) (Fin d) K) =
      diagonal (fun i => (A : Matrix (Fin d) (Fin d) K) i i) := by
    apply eq_diagonal_of_commute_diagonal
    intro u
    have h := hπ u
    have e : u ∘ π = u := funext fun k => by rw [Function.comp_apply, hπ1 k]
    rwa [e] at h
  rintro _ ⟨v, hv, rfl⟩
  refine ⟨CatalogueBHigherLinearAction.slConjugation d K A (SpecialLinearGroup.map σ.toRingHom v),
    mem_unitriangular_diag_conj A hAd σ hv, ?_⟩
  rw [MulAut.mul_apply, fieldAut_proj, conjAut_proj]

omit [CharP K 2] in
theorem mapsTo_unitriangular_conj_of_comm (hp : p.Prime) (hp2 : p ≠ 2) (hd : 5 ≤ d) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (A₀ : GL (Fin d) K) {φ : MulAut (projectiveSL d K)}
    (hodd : Odd (orderOf φ))
    (hcomm : ∀ (i j : Fin d) (hij : i ≠ j),
      φ * conjAut d K (A₀⁻¹ * rootGL (hζ.ne_zero hp.ne_zero) hij * A₀) =
        conjAut d K (A₀⁻¹ * rootGL (hζ.ne_zero hp.ne_zero) hij * A₀) * φ) :
    ∀ u ∈ (projUnitriangular d K).map (conjAut d K A₀⁻¹).toMonoidHom,
      φ u ∈ (projUnitriangular d K).map (conjAut d K A₀⁻¹).toMonoidHom := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  set ψ := conjAut d K A₀ * φ * (conjAut d K A₀)⁻¹ with hψ
  have hψodd : Odd (orderOf ψ) := by
    have hsc : SemiconjBy (conjAut d K A₀) φ ψ := by
      rw [SemiconjBy, hψ]
      group
    rw [← hsc.orderOf_eq]
    exact hodd
  have hψc : ∀ (i j : Fin d) (hij : i ≠ j),
      ψ * conjAut d K (rootGL hζ0 hij) = conjAut d K (rootGL hζ0 hij) * ψ := by
    intro i j hij
    have h := hcomm i j hij
    simp only [map_mul, map_inv] at h
    have h2 : conjAut d K A₀ * φ * (conjAut d K A₀)⁻¹ * conjAut d K (rootGL hζ0 hij) =
        conjAut d K A₀ * (φ * ((conjAut d K A₀)⁻¹ * conjAut d K (rootGL hζ0 hij) *
          conjAut d K A₀)) * (conjAut d K A₀)⁻¹ := by group
    rw [hψ, h2, h]
    group
  have hU := mapsTo_unitriangular_of_comm_rootT hp hp2 hd hζ hψodd hψc
  rintro _ ⟨u, hu, rfl⟩
  refine ⟨ψ u, hU u hu, ?_⟩
  simp [hψ, MulAut.mul_apply]

end CFSG.StandardType.LinUnitL

end
