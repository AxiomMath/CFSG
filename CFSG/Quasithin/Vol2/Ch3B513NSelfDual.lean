module

public import CFSG.Quasithin.Background.JonesParshallBasic

public section

namespace CFSG.Quasithin.B513N

open CFSG.Quasithin.JonesParshall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {ι : Type} [Fintype ι] [DecidableEq ι] (K : Type) [Field K] [CharP K 2]

noncomputable local instance algZ2K : Algebra (ZMod 2) K := ZMod.algebra K 2

@[expose] noncomputable def psiB (B : (ι → K) →ₗ[K] (ι → K) →ₗ[K] K) :
    (ι → K) →ₗ[ZMod 2] Module.Dual (ZMod 2) (ι → K) where
  toFun u := (Algebra.trace (ZMod 2) K).comp ((B u).restrictScalars (ZMod 2))
  map_add' u v := by
    ext x
    simp
  map_smul' c u := by
    ext x
    simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply,
      RingHom.id_apply, LinearMap.smul_apply]
    rw [LinearMap.map_smul_of_tower, LinearMap.smul_apply, LinearMap.map_smul_of_tower]

theorem psiB_apply (B : (ι → K) →ₗ[K] (ι → K) →ₗ[K] K) (u x : ι → K) :
    psiB K B u x = Algebra.trace (ZMod 2) K (B u x) := rfl

variable [Finite K]

theorem psiB_injective (B : (ι → K) →ₗ[K] (ι → K) →ₗ[K] K)
    (hB : ∀ u, (∀ x, B u x = 0) → u = 0) : Function.Injective (psiB K B) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro u hu
  refine hB u fun x => ?_
  have hnd := traceForm_nondegenerate (ZMod 2) K
  refine hnd.1 (B u x) fun c => ?_
  have h1 := congrArg (fun l => l (c • x)) hu
  simp only [psiB_apply, LinearMap.map_smul, smul_eq_mul, LinearMap.zero_apply] at h1
  rw [Algebra.traceForm_apply, mul_comm]
  exact h1

theorem psiB_bijective (B : (ι → K) →ₗ[K] (ι → K) →ₗ[K] K)
    (hB : ∀ u, (∀ x, B u x = 0) → u = 0) : Function.Bijective (psiB K B) := by
  have : Module.Finite (ZMod 2) (ι → K) := Module.Finite.of_finite
  refine ⟨psiB_injective K B hB, ?_⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (Subspace.dual_finrank_eq (K := ZMod 2) (V := ι → K)).symm).mp (psiB_injective K B hB)

omit [Finite K] in
theorem dual_psiB {Γ : Type*} [Group Γ] (ρ : Representation (ZMod 2) Γ (ι → K))
    (B : (ι → K) →ₗ[K] (ι → K) →ₗ[K] K) (hinv : ∀ γ u x, B (ρ γ u) (ρ γ x) = B u x) (γ : Γ)
    (u : ι → K) : Representation.dual ρ γ (psiB K B u) = psiB K B (ρ γ u) := by
  refine LinearMap.ext fun x => ?_
  rw [Representation.dual_apply]
  show psiB K B u (ρ γ⁻¹ x) = psiB K B (ρ γ u) x
  rw [psiB_apply, psiB_apply, ← hinv γ u (ρ γ⁻¹ x), ← Module.End.mul_apply, ← map_mul,
    mul_inv_cancel, map_one, Module.End.one_apply]

theorem card_H1_dual_of_selfDual {Γ G : Type*} [Group Γ] [Group G] [Finite Γ]
    (ρ : Representation (ZMod 2) Γ (ι → K)) (B : (ι → K) →ₗ[K] (ι → K) →ₗ[K] K)
    (hB : ∀ u, (∀ x, B u x = 0) → u = 0) (hinv : ∀ γ u x, B (ρ γ u) (ρ γ x) = B u x)
    (θ : Γ ≃* G) (μ : G →* AddMonoid.End (ι → K)) (hμ : ∀ γ x, ρ γ x = μ (θ γ) x) {k : ℕ}
    (hk : Nat.card (Z1A μ) = k * Nat.card (B1A μ)) :
    Nat.card (H1 (Representation.dual ρ)) = k := by
  let e : (ι → K) ≃+ Module.Dual (ZMod 2) (ι → K) :=
    (LinearEquiv.ofBijective (psiB K B) (psiB_bijective K B hB)).toAddEquiv
  have he : ∀ u, e u = psiB K B u := fun _ => rfl
  have : Finite (Module.Dual (ZMod 2) (ι → K)) := Finite.of_equiv _ e.toEquiv
  refine card_H1_eq_of_card (Representation.dual ρ) (β := e.symm) (θ := θ) (μ := μ) ?_ hk
  intro γ f
  obtain ⟨u, rfl⟩ := e.surjective f
  rw [e.symm_apply_apply, he, dual_psiB K ρ B hinv γ u, ← he, e.symm_apply_apply, hμ]

end CFSG.Quasithin.B513N
