module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordInnerDefs

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open CFSG.StandardType.UCoord
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary Matrix

private theorem qTwoLMDivCoordInner_tormono_ggPermSU_coe {K : Type} [Field K] [Finite K]
    [CharP K 2] {f n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (((ggPermSU (K := K) (f := f) σ : Su K 2 f n) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = σ.permMatrix K := by
  rfl

theorem qTwoLMDivCoordInner_tormono {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {m : ℕ}
    {δ : ↥(sumZero m 3) →* Su F0 2 1 m} (hdiag : ∀ f, ggIsDiagMat (δ f : GL (Fin m) F0))
    (hperm : ∀ (σ : Equiv.Perm (Fin m)) f,
      ggPermSU σ⁻¹ * δ f * (ggPermSU σ⁻¹)⁻¹ = δ (permAutV σ f))
    (hsep : ∀ i j : Fin m, i ≠ j → ∃ f,
      ((δ f : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) i i ≠
        ((δ f : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) j j)
    (u : GL (Fin m) F0) (hu : ∀ f, ∃ f', ∃ z : F0, z ≠ 0 ∧
      (u : Matrix (Fin m) (Fin m) F0) * ((δ f : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) =
        z • ((δ f' : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *
          (u : Matrix (Fin m) (Fin m) F0)) :
    ∃ ρ : Equiv.Perm (Fin m), ∀ f,
      u * (δ f : GL (Fin m) F0) = (δ (permAutV ρ f) : GL (Fin m) F0) * u := by
  classical
  choose d hd using hdiag
  let M : Matrix (Fin m) (Fin m) F0 := (u : Matrix (Fin m) (Fin m) F0)
  let N : Matrix (Fin m) (Fin m) F0 := ((u⁻¹ : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0)
  have hMN : M * N = 1 := by
    have h := congrArg (fun g : GL (Fin m) F0 => (g : Matrix (Fin m) (Fin m) F0))
      (mul_inv_cancel u)
    simpa [M, N] using h
  have hNM : N * M = 1 := by
    have h := congrArg (fun g : GL (Fin m) F0 => (g : Matrix (Fin m) (Fin m) F0))
      (inv_mul_cancel u)
    simpa [M, N] using h
  have hrow : ∀ (g : ↥(sumZero m 3)) (k l l' : Fin m),
      M k l ≠ 0 → M k l' ≠ 0 → d g l = d g l' := by
    intro g k l l' hl hl'
    obtain ⟨g', z, hz, heq⟩ := hu g
    have h1 : M k l * d g l = z * (d g' k * M k l) := by
      have h := congrFun (congrFun heq k) l
      rw [hd g, hd g'] at h
      rw [Matrix.mul_diagonal] at h
      rw [smul_mul_assoc, Matrix.smul_apply, Matrix.diagonal_mul] at h
      simpa using h
    have h2 : M k l' * d g l' = z * (d g' k * M k l') := by
      have h := congrFun (congrFun heq k) l'
      rw [hd g, hd g'] at h
      rw [Matrix.mul_diagonal] at h
      rw [smul_mul_assoc, Matrix.smul_apply, Matrix.diagonal_mul] at h
      simpa using h
    have e1 : d g l = z * d g' k := by
      have hh : M k l * d g l = M k l * (z * d g' k) := by rw [h1]; ring
      exact mul_left_cancel₀ hl hh
    have e2 : d g l' = z * d g' k := by
      have hh : M k l' * d g l' = M k l' * (z * d g' k) := by rw [h2]; ring
      exact mul_left_cancel₀ hl' hh
    rw [e1, e2]
  have huniqrow : ∀ (k l l' : Fin m), M k l ≠ 0 → M k l' ≠ 0 → l = l' := by
    intro k l l' hl hl'
    by_contra hne
    obtain ⟨g, hg⟩ := hsep l l' hne
    rw [hd g] at hg
    have hg' : d g l ≠ d g l' := by simpa [Matrix.diagonal_apply_eq] using hg
    exact hg' (hrow g k l l' hl hl')
  have hex : ∀ k : Fin m, ∃ l : Fin m, M k l ≠ 0 := by
    intro k
    by_contra h
    have hzero : ∀ l, M k l = 0 := by
      intro l
      by_contra hl
      exact h ⟨l, hl⟩
    have hsum : (M * N) k k = 0 := by
      rw [Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro l _
      rw [hzero l, zero_mul]
    have hone : (M * N) k k = 1 := by simp [hMN]
    rw [hsum] at hone
    exact one_ne_zero hone.symm
  let r : Fin m → Fin m := fun k => Classical.choose (hex k)
  have hr : ∀ k, M k (r k) ≠ 0 := fun k => Classical.choose_spec (hex k)
  have hr_eq : ∀ (k l : Fin m), M k l ≠ 0 → l = r k :=
    fun k l hl => huniqrow k l (r k) hl (hr k)
  have hrinj : Function.Injective r := by
    intro k k' hkk
    by_contra hne
    have hmk : M k' (r k) ≠ 0 := by rw [hkk]; exact hr k'
    have h0 : (M * N) k' k = 0 := by
      simp [hMN, Matrix.one_apply, Ne.symm hne]
    have hcalc : (M * N) k' k = M k' (r k) * N (r k) k := by
      rw [Matrix.mul_apply, Finset.sum_eq_single (r k)]
      · intro j _ hj
        have hMj : M k' j = 0 := by
          by_contra hjj
          exact hj ((hr_eq k' j hjj).trans hkk.symm)
        rw [hMj, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ _) h
    have hNk : N (r k) k = 0 := by
      rw [hcalc] at h0
      exact (mul_eq_zero.mp h0).resolve_left hmk
    have hcalc2 : (M * N) k k = M k (r k) * N (r k) k := by
      rw [Matrix.mul_apply, Finset.sum_eq_single (r k)]
      · intro j _ hj
        have hMj : M k j = 0 := by
          by_contra hjj
          exact hj (hr_eq k j hjj)
        rw [hMj, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ _) h
    have h1 : (M * N) k k = 1 := by simp [hMN]
    rw [hcalc2, hNk, mul_zero] at h1
    exact one_ne_zero h1.symm
  have hdiagperm : ∀ (σ : Equiv.Perm (Fin m)) (g : ↥(sumZero m 3)) (k : Fin m),
      d (permAutV σ g) k = d g (σ⁻¹ k) := by
    intro σ g k
    have h2 : (ggPermSU (K := F0) (f := 1) σ⁻¹ : Su F0 2 1 m) * δ g =
        δ (permAutV σ g) * (ggPermSU (K := F0) (f := 1) σ⁻¹ : Su F0 2 1 m) := by
      have h := congrArg (fun x => x * (ggPermSU (K := F0) (f := 1) σ⁻¹ : Su F0 2 1 m))
        (hperm σ g)
      group at h
      exact h
    have hmat : ((σ⁻¹).permMatrix F0) * Matrix.diagonal (d g) =
        Matrix.diagonal (d (permAutV σ g)) * ((σ⁻¹).permMatrix F0) := by
      have h := congrArg (fun x : Su F0 2 1 m =>
        ((x : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0)) h2
      simpa [qTwoLMDivCoordInner_tormono_ggPermSU_coe, hd g, hd (permAutV σ g)] using h
    have hkk := congrFun (congrFun hmat k) (σ⁻¹ k)
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at hkk
    have hp : (σ⁻¹).permMatrix F0 k (σ⁻¹ k) = 1 := by
      simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
    rw [hp, one_mul, mul_one] at hkk
    exact hkk.symm
  let ρ : Equiv.Perm (Fin m) := (Equiv.ofBijective r hrinj.bijective_of_finite).symm
  refine ⟨ρ, fun g => ?_⟩
  apply Units.ext
  apply Matrix.ext
  intro k l
  simp only [Units.val_mul, hd g, hd (permAutV ρ g)]
  by_cases hl : l = r k
  · subst hl
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, hdiagperm ρ g k]
    have hρ : ρ⁻¹ k = r k := rfl
    rw [hρ]
    ring
  · have hMkl : (u : Matrix (Fin m) (Fin m) F0) k l = 0 := by
      by_contra h
      exact hl (hr_eq k l h)
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, hMkl]
    ring

end CFSG.StandardType.QTwo

end
