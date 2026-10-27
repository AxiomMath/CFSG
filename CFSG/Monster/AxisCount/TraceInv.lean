module

public import CFSG.Monster.AxisCount.Abstract
public import CFSG.Monster.Visible.Pair

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.AxisCount

open CFSG.Monster CFSG.Monster.Griess CFSG.Monster.ScalarKernel CFSG.Monster.Visible Matrix

@[expose] def trA2 (v : SpaceB) : ℚ :=
  ∑ i : Fin 24, ∑ j : Fin 24, ((v.1 : Matrix (Fin 24) (Fin 24) ℚ) i j) ^ 2

theorem sumSq_eq_trace (M : Matrix (Fin 24) (Fin 24) ℚ) :
    ∑ i, ∑ j, M i j ^ 2 = Matrix.trace (M * Mᵀ) := by
  simp [Matrix.trace, Matrix.mul_apply, pow_two]

theorem trA2_eq_trace (v : SpaceB) :
    trA2 v =
      Matrix.trace ((v.1 : Matrix (Fin 24) (Fin 24) ℚ) * (v.1 : Matrix (Fin 24) (Fin 24) ℚ)) := by
  have h : (v.1 : Matrix (Fin 24) (Fin 24) ℚ)ᵀ = v.1 := v.1.2
  have h2 := sumSq_eq_trace (v.1 : Matrix (Fin 24) (Fin 24) ℚ)
  rw [h] at h2
  exact h2

theorem sumSq_conj (g A : Matrix (Fin 24) (Fin 24) ℚ) (hg : g * gᵀ = 1) :
    ∑ i, ∑ j, (gᵀ * A * g) i j ^ 2 = ∑ i, ∑ j, A i j ^ 2 := by
  rw [sumSq_eq_trace, sumSq_eq_trace]
  have e : gᵀ * A * g * (gᵀ * A * g)ᵀ = gᵀ * (A * Aᵀ) * g := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
    calc gᵀ * A * g * (gᵀ * (Aᵀ * g)) = gᵀ * A * (g * gᵀ) * (Aᵀ * g) := by
          simp only [Matrix.mul_assoc]
      _ = gᵀ * (A * Aᵀ) * g := by
          rw [hg, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
  rw [e, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hg, Matrix.one_mul]

theorem trA2_theta (p : Pvis) (v : SpaceB) : trA2 (theta p v) = trA2 v := by
  rw [trA2, trA2, theta_apply]
  exact sumSq_conj _ _ (mat_mul_transpose p.1.2)

theorem trA2_thetaEquiv (p : Pvis) (v : SpaceB) : trA2 (thetaEquiv p v) = trA2 v :=
  trA2_theta p v

theorem trA2_apply_of_mem_Gvis {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ Gvis) (v : SpaceB) :
    trA2 (g v) = trA2 v := by
  obtain ⟨p, rfl⟩ := mem_Gvis.1 hg
  exact trA2_theta p v

theorem trA2_smul_of_mem_Gvis {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ Gvis) (v : SpaceB) :
    trA2 (g • v) = trA2 v :=
  trA2_apply_of_mem_Gvis hg v

theorem ne_apply_of_trA2_ne {v v' : SpaceB} (h : trA2 v ≠ trA2 v') {g : SpaceB ≃ₗ[ℚ] SpaceB}
    (hg : g ∈ Gvis) : g v ≠ v' := fun e =>
  h ((trA2_apply_of_mem_Gvis hg v).symm.trans (congrArg trA2 e))

theorem not_mem_orbit_of_trA2_ne {v v' : SpaceB} (h : trA2 v ≠ trA2 v') :
    v' ∉ MulAction.orbit Gvis v := by
  rintro ⟨⟨g, hg⟩, hgv⟩
  exact ne_apply_of_trA2_ne h hg hgv

theorem orbit_ne_of_trA2_ne {v v' : SpaceB} (h : trA2 v ≠ trA2 v') :
    MulAction.orbit Gvis v ≠ MulAction.orbit Gvis v' := fun e =>
  not_mem_orbit_of_trA2_ne h (e ▸ MulAction.mem_orbit_self v')

@[expose] def trA2Num : Fin 12 → ℕ :=
  ![4, 8, 104, 232, 192, 3976, 3080, 3008, 2816, 3136, 2912, 2920]

@[expose] def trA2Exp : Fin 12 → ℕ := ![0, 2, 4, 5, 5, 7, 7, 7, 7, 7, 7, 7]

@[expose] def trA2Values (i : Fin 12) : ℚ := (trA2Num i : ℚ) / 4 ^ trA2Exp i

theorem trA2Num_mul_ne : ∀ i j : Fin 12, i ≠ j →
    trA2Num i * 4 ^ trA2Exp j ≠ trA2Num j * 4 ^ trA2Exp i := by decide

theorem trA2Values_injective : Function.Injective trA2Values := by
  intro i j h
  by_contra hij
  have h1 := trA2Num_mul_ne i j hij
  apply h1
  have h2 : ((trA2Num i : ℚ)) * 4 ^ trA2Exp j = (trA2Num j : ℚ) * 4 ^ trA2Exp i := by
    unfold trA2Values at h
    rwa [div_eq_div_iff (by positivity) (by positivity)] at h
  exact_mod_cast h2

theorem Setup.orb_injective_of_trA2 {I : Type*} {R : I → Type*}
    (S : Setup (SpaceB ≃ₗ[ℚ] SpaceB) SpaceB I R) (hH : S.H ≤ Gvis)
    (hinj : Function.Injective fun i => trA2 (S.v i)) : Function.Injective S.orb :=
  S.orb_injective_of_invariant trA2 (fun _ hc x => trA2_smul_of_mem_Gvis (hH hc) x) hinj

theorem Setup.orb_injective_of_trA2Values {R : Fin 12 → Type*}
    (S : Setup (SpaceB ≃ₗ[ℚ] SpaceB) SpaceB (Fin 12) R) (hH : S.H ≤ Gvis)
    (hv : ∀ i, trA2 (S.v i) = trA2Values i) : Function.Injective S.orb :=
  S.orb_injective_of_trA2 hH fun i j h => trA2Values_injective (by rwa [← hv i, ← hv j])

end CFSG.Monster.AxisCount
