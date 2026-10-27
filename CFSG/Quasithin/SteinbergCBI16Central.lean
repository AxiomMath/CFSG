module

public import CFSG.Quasithin.Background.JonesParshallBasic

public section

namespace CFSG.Quasithin.SteinbergCB.I16

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit Matrix

variable {Γ : Type*} [Group Γ] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem finrank_H1_eq_zero_of_le {ρ : Representation (ZMod 2) Γ W} (h : Z1 ρ ≤ B1 ρ) :
    Module.finrank (ZMod 2) (H1 ρ) = 0 := by
  have htop : (B1 ρ).comap (Z1 ρ).subtype = ⊤ := by
    rw [eq_top_iff]
    intro x _
    exact h x.2
  have : Subsingleton (H1 ρ) := Submodule.Quotient.subsingleton_iff.2 htop
  exact Module.finrank_zero_of_subsingleton

theorem Z1_le_B1_of_central (ρ : Representation (ZMod 2) Γ W) (z : Γ)
    (hc : ∀ g, z * g = g * z) (hbij : Function.Bijective fun w => ρ z w - w) :
    Z1 ρ ≤ B1 ρ := by
  intro f hf
  obtain ⟨m, hm⟩ := hbij.2 (f z)
  refine ⟨m, funext fun g => ?_⟩
  change ρ g m - m = f g
  apply hbij.1
  change ρ z (ρ g m - m) - (ρ g m - m) = ρ z (f g) - f g
  have h1 : f (z * g) = f z + ρ z (f g) := hf z g
  have h2 : f (g * z) = f g + ρ g (f z) := hf g z
  rw [hc g] at h1
  have h3 : ρ z (f g) - f g = ρ g (f z) - f z := by
    have := h1.symm.trans h2
    linear_combination (norm := abel_nf) this
  rw [h3, ← hm]
  have hzg : ρ z (ρ g m) = ρ g (ρ z m) := by
    rw [← Module.End.mul_apply, ← map_mul, hc g, map_mul, Module.End.mul_apply]
  simp only [map_sub, hzg]
  abel

@[expose] noncomputable def scalarGL {K : Type*} [Field K] (c : K) (hc : c ≠ 0) :
    GL (Fin 3) K :=
  ⟨c • 1, c⁻¹ • 1, by rw [smul_mul_smul, mul_inv_cancel₀ hc, one_mul, one_smul],
    by rw [smul_mul_smul, inv_mul_cancel₀ hc, one_mul, one_smul]⟩

theorem scalarGL_inv {K : Type*} [Field K] (c : K) (hc : c ≠ 0) :
    (((scalarGL c hc)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = c⁻¹ • 1 := rfl

theorem tripleTwistMat_scalar {K : Type} [Field K] [Fintype K] (hK : Fintype.card K = 4)
    (ε : TripleTwist) {ω : K} (hω0 : ω ≠ 0) (hω1 : ω ≠ 1) :
    ∃ c : K, c ≠ 1 ∧ tripleTwistMat ε (scalarGL ω hω0) = c • 1 := by
  have hω3 : ω ^ 3 = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one ω hω0
    rwa [hK] at this
  have hsq : ω ^ 2 ≠ 1 := fun h => hω1 (by
    calc ω = ω ^ 3 / ω ^ 2 := by field_simp
      _ = 1 := by rw [hω3, h, div_one])
  have hmap : ∀ c : K, (c • (1 : Matrix (Fin 3) (Fin 3) K)).map (· ^ 2) = c ^ 2 • 1 := by
    intro c
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Matrix.one_apply_ne hij]
  cases ε with
  | natural => exact ⟨ω, hω1, rfl⟩
  | dual =>
    refine ⟨ω⁻¹, fun h => hω1 (inv_eq_one.1 h), ?_⟩
    change (((scalarGL ω hω0)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ = _
    rw [scalarGL_inv, Matrix.transpose_smul, Matrix.transpose_one]
  | frobenius =>
    refine ⟨ω ^ 2, hsq, ?_⟩
    exact hmap ω
  | dualFrobenius =>
    refine ⟨ω⁻¹ ^ 2, fun h => hsq (by rw [inv_pow] at h; exact inv_eq_one.1 h), ?_⟩
    change ((((scalarGL ω hω0)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ).map (· ^ 2) = _
    rw [scalarGL_inv, Matrix.transpose_smul, Matrix.transpose_one, hmap]

theorem finrank_H1_tripleA6Six {ρ : Representation (ZMod 2) Γ W} {ε : TripleTwist}
    (h : Explicit.TripleA6Six ρ ε) : Module.finrank (ZMod 2) (H1 ρ) = 0 := by
  classical
  obtain ⟨P, _, -, K, _, _, hK, τ, hτ, -, hcen, θ, β, hw⟩ := h
  obtain ⟨ω, -, hω⟩ : ∃ ω, ω ∈ (Finset.univ : Finset K) ∧ ω ∉ ({0, 1} : Finset K) := by
    apply Finset.exists_mem_notMem_of_card_lt_card
    rw [Finset.card_univ, hK]
    exact (Finset.card_le_two).trans_lt (by norm_num)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hω
  obtain ⟨hω0, hω1⟩ := hω
  obtain ⟨z, hz, hzτ⟩ : scalarGL ω hω0 ∈ (Subgroup.center P).map τ :=
    (hcen _).2 ⟨ω, hω0, rfl⟩
  obtain ⟨c, hc1, hcmat⟩ := tripleTwistMat_scalar hK ε hω0 hω1
  have hamb := Witness.ambient (D := matModel τ.range fun g => tripleTwistMat ε
    (g : GL (Fin 3) K)) rfl rfl hw
  set e := β.trans (secEquivAmb (matModel τ.range fun g => tripleTwistMat ε
    (g : GL (Fin 3) K)) rfl rfl).toAdditive with he
  set z' := θ.symm z with hz'
  have hθz : ((θ.trans (MonoidHom.ofInjective hτ)) z' : GL (Fin 3) K) = scalarGL ω hω0 := by
    rw [MulEquiv.trans_apply, hz', MulEquiv.apply_symm_apply, MonoidHom.ofInjective_apply,
      hzτ]
  set φ : W → (Fin 3 → K) := fun w => Multiplicative.toAdd (Additive.toMul (e w)) with hφ
  have hφinj : Function.Injective φ := fun w w' hww' =>
    e.injective (Additive.toMul.injective (Multiplicative.toAdd.injective hww'))
  have hφsub : ∀ w w', φ (w - w') = φ w - φ w' := fun w w' => by
    simp only [hφ, map_sub]
    rfl
  have hφz : ∀ w, φ (ρ z' w) = c • φ w := by
    intro w
    change Multiplicative.toAdd (Additive.toMul (e (ρ z' w))) = _
    rw [hamb z' w]
    change tripleTwistMat ε ((θ.trans (MonoidHom.ofInjective hτ)) z' : GL (Fin 3) K) *ᵥ
      φ w = c • φ w
    rw [hθz, hcmat, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hinj : Function.Injective fun w => ρ z' w - w := by
    intro w w' hww'
    have h1 := congrArg φ hww'
    simp only [hφsub, hφz] at h1
    have h2 : (c - 1) • φ w = (c - 1) • φ w' := by
      rw [sub_smul, sub_smul, one_smul, one_smul]
      exact h1
    exact hφinj (smul_right_injective _ (sub_ne_zero.2 hc1) h2)
  have : Finite W := Finite.of_injective φ hφinj
  refine finrank_H1_eq_zero_of_le (Z1_le_B1_of_central ρ z' (fun g => ?_)
    ⟨hinj, Finite.injective_iff_surjective.1 hinj⟩)
  apply θ.injective
  rw [map_mul, map_mul, hz', MulEquiv.apply_symm_apply]
  exact (Subgroup.mem_center_iff.1 hz (θ g)).symm

end CFSG.Quasithin.SteinbergCB.I16
