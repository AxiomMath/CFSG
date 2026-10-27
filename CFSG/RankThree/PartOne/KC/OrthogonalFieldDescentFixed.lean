module

public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentForm
public import CFSG.LieType.Universal.Spin.Forms
public import CFSG.GroupTheory.SteinbergBKSemilinearFixedBasis

public section

namespace CFSG.RankThree.PartOne.KCOrthogonalDescent

open Module TensorProduct CFSG.GroupTheory.SteinbergBK

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

@[expose] noncomputable def extScalars (k : Subfield K) (V₀ : Submodule k V) :
    K ⊗[k] V₀ →ₗ[K] V :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun := fun x => x • (V₀.subtype : V₀ →ₗ[k] V)
      map_add' := fun x y => by
        ext w
        simp [add_smul]
      map_smul' := fun c x => by
        ext w
        simp [mul_smul] }

theorem extScalars_tmul (k : Subfield K) (V₀ : Submodule k V) (x : K) (w : V₀) :
    extScalars k V₀ (x ⊗ₜ w) = x • (w : V) := by
  simp [extScalars]

section Nonisotropic

variable {ι : Type}

theorem exists_fixed_quadratic_ne_zero [Nontrivial V] (b : Basis ι K V) (a : V ≃+ V)
    (hb : ∀ i, a (b i) = b i) (Q : QuadraticForm K V)
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate) : ∃ w : V, a w = w ∧ Q w ≠ 0 := by
  by_contra hall
  push Not at hall
  obtain ⟨i⟩ := b.index_nonempty
  have hlin : QuadraticMap.polarBilin Q (b i) = 0 := by
    refine b.ext fun j => ?_
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
      hall _ (by rw [map_add, hb, hb]), hall _ (hb i), hall _ (hb j)]
    simp
  refine b.ne_zero i (hnd.1 (b i) fun y => ?_)
  rw [hlin]
  rfl

end Nonisotropic

theorem exists_descent {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) [Finite K] [FiniteDimensional K V]
    [Nontrivial V] (hK : Nat.card K = ℓ ^ f) (σ : K ≃+* K) (hσ : orderOf σ = p) (a : V ≃+ V)
    (ha : ∀ (c : K) (v : V), a (c • v) = σ c • a v) (hap : ∀ v, (⇑a)^[p] v = v)
    (Q : QuadraticForm K V) (hnd : (QuadraticMap.polarBilin Q).Nondegenerate) (η : K)
    (hQa : ∀ v, Q (a v) = η * σ (Q v)) :
    p ∣ f ∧ Nat.card (semilinearFixedSubfield σ) = ℓ ^ (f / p) ∧
      ∃ (d : Kˣ) (Q₀ : QuadraticForm (semilinearFixedSubfield σ) (semilinearFixedSubmodule σ a ha)),
        (∀ w, ((Q₀ w : semilinearFixedSubfield σ) : K) = d * Q w) ∧
        (QuadraticMap.polarBilin Q₀).Nondegenerate ∧
        finrank (semilinearFixedSubfield σ) (semilinearFixedSubmodule σ a ha) = finrank K V ∧
        ∃ Φ : K ⊗[semilinearFixedSubfield σ] semilinearFixedSubmodule σ a ha ≃ₗ[K] V,
          (∀ x w, Φ (x ⊗ₜ w) = x • (w : V)) ∧
          ∀ x w, a (Φ (x ⊗ₜ w)) = Φ (σ x ⊗ₜ w) := by
  obtain ⟨hdvd, hcard, b, b₀, hfix, hb₀, hfr, -⟩ :=
    coprime_finite_field_semilinear_fixed_basis hℓ hf hK σ hσ (rfl : finrank K V = finrank K V)
      a ha hap
  refine ⟨hdvd, hcard, ?_⟩
  obtain ⟨w₀, hw₀, hQw₀⟩ := exists_fixed_quadratic_ne_zero b a hfix Q hnd
  have hσQ : η * σ (Q w₀) = Q w₀ := by rw [← hQa, hw₀]
  have hσQne : σ (Q w₀) ≠ 0 := fun h => hQw₀ (by rw [← hσQ, h, mul_zero])
  have hηd : σ (Q w₀)⁻¹ = η * (Q w₀)⁻¹ := by
    rw [map_inv₀]
    field_simp
    linear_combination (-1 : K) * hσQ
  set d : Kˣ := Units.mk0 (Q w₀)⁻¹ (inv_ne_zero hQw₀) with hd
  have hR : ∀ w ∈ semilinearFixedSubmodule σ a ha, ((d : K) • Q) w ∈ semilinearFixedSubfield σ := by
    intro w hw
    have hw' : a w = w := hw
    have h1 : η * σ (Q w) = Q w := by rw [← hQa, hw']
    rw [RingHom.mem_eqLocusField]
    change σ ((d : K) * Q w) = (d : K) * Q w
    rw [map_mul]
    have : σ (d : K) = η * (d : K) := by simpa [hd] using hηd
    change σ (d : K) * σ (Q w) = (d : K) * Q w
    rw [this]
    linear_combination (d : K) * h1
  refine ⟨d, descendQuadratic ((d : K) • Q) hR, fun w => ?_, ?_, hfr, ?_⟩
  · rw [coe_descendQuadratic]
    rfl
  ·
    refine CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_of_forall fun w hw => ?_
    have hperp : ∀ w' : semilinearFixedSubmodule σ a ha,
        QuadraticMap.polar Q (w : V) (w' : V) = 0 := by
      intro w'
      have h1 := hw w'
      have h2 := congrArg (fun z : semilinearFixedSubfield σ => (z : K)) h1
      simp only [coe_polar_descendQuadratic, ZeroMemClass.coe_zero] at h2
      simp only [FunLike.coe_smul, QuadraticMap.polar_smul, smul_eq_mul] at h2
      have hd0 : (d : K) ≠ 0 := d.ne_zero
      simpa [hd0] using h2
    have hlin : QuadraticMap.polarBilin Q (w : V) = 0 := by
      refine b.ext fun j => ?_
      rw [QuadraticMap.polarBilin_apply_apply, ← hb₀ j]
      exact hperp (b₀ j)
    have hw0 : (w : V) = 0 := by
      refine hnd.1 (w : V) fun y => ?_
      rw [hlin]
      rfl
    exact Subtype.ext hw0
  ·
    let b₁ : Basis (Fin (finrank K V)) K
        (K ⊗[semilinearFixedSubfield σ] semilinearFixedSubmodule σ a ha) := b₀.baseChange K
    let Φ := b₁.equiv b (Equiv.refl _)
    have hΦ : ∀ t, Φ t = extScalars (semilinearFixedSubfield σ)
        (semilinearFixedSubmodule σ a ha) t := by
      intro t
      refine LinearMap.congr_fun (b₁.ext fun i => ?_) t
      change Φ (b₁ i) = _
      rw [Basis.equiv_apply, Equiv.refl_apply]
      have hbi : b₁ i = 1 ⊗ₜ b₀ i := Basis.baseChange_apply K b₀ i
      rw [hbi, extScalars_tmul, one_smul, hb₀]
    refine ⟨Φ, fun x w => ?_, fun x w => ?_⟩
    · rw [hΦ, extScalars_tmul]
    · rw [hΦ, hΦ, extScalars_tmul, extScalars_tmul, ha]
      have hw : a (w : V) = (w : V) := w.2
      rw [hw]

end CFSG.RankThree.PartOne.KCOrthogonalDescent
