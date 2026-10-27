module

public import CFSG.Quasithin.Vol2.Ch10Reselect.ModelAlgUniq
public import CFSG.Quasithin.Vol2.Ch10Reselect.ModelAlgNorm
public import CFSG.Quasithin.Vol2.Ch10Reselect.InvariantLine
public import CFSG.Quasithin.Vol2.Ch10Reselect.GaloisDescent

public section

namespace CFSG.Quasithin.Vol2.Ch10Reselect

open Matrix

private theorem ml_glMap_coe_inv {K : Type*} [Field K] (σ : RingAut K) (B : GL (Fin 2) K) :
    ((glMap K σ⁻¹ B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (B : Matrix (Fin 2) (Fin 2) K).map σ.symm := rfl

private theorem ml_key {K : Type*} [Field K] (τ : RingAut K) (B : Matrix (Fin 2) (Fin 2) K)
    (u : Fin 2 → K) (i : Fin 2) :
    τ ((B.map τ.symm *ᵥ u) i) = (B *ᵥ fun j => τ (u j)) i := by
  simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem wMap_mul {K : Type*} [Field K] (σ₁ σ₂ : RingAut K) (B₁ B₂ : GL (Fin 2) K) :
    wMap K σ₁ B₁ * wMap K σ₂ B₂ = wMap K (σ₁ * σ₂) (glMap K σ₂⁻¹ B₁ * B₂) := by
  apply Equiv.ext
  intro w
  funext i
  show σ₁ (((B₁ : Matrix (Fin 2) (Fin 2) K) *ᵥ fun j => σ₂ (((B₂ : Matrix (Fin 2) (Fin 2) K) *ᵥ w) j)) i)
    = σ₁ (σ₂ ((((glMap K σ₂⁻¹ B₁ * B₂ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ w) i))
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, ml_glMap_coe_inv]
  congr 1
  exact (ml_key σ₂ _ _ i).symm

theorem wMap_semilinear {K : Type*} [Field K] (σ : RingAut K) (B : GL (Fin 2) K) :
    IsSemilinear σ (wMap K σ B) := by
  unfold IsSemilinear
  refine ⟨fun v w => ?_, fun c v => ?_⟩
  · funext i
    show σ (((B : Matrix (Fin 2) (Fin 2) K) *ᵥ (v + w)) i) =
      σ (((B : Matrix (Fin 2) (Fin 2) K) *ᵥ v) i) + σ (((B : Matrix (Fin 2) (Fin 2) K) *ᵥ w) i)
    rw [Matrix.mulVec_add, Pi.add_apply, map_add]
  · funext i
    show σ (((B : Matrix (Fin 2) (Fin 2) K) *ᵥ (c • v)) i) =
      σ c * σ (((B : Matrix (Fin 2) (Fin 2) K) *ᵥ v) i)
    rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, map_mul]

theorem wMap_one_apply {K : Type*} [Field K] (B : GL (Fin 2) K) (w : Fin 2 → K) :
    wMap K 1 B w = (B : Matrix (Fin 2) (Fin 2) K) *ᵥ w := rfl

theorem phi_mem_linePair {K : Type*} [Field K] (g : Matrix.SpecialLinearGroup (Fin 2) K)
    (σ : RingAut K) (B : GL (Fin 2) K) (w : Fin 2 → K) {p : UTilde K} (hp : p ∈ linePair K w) :
    phi K g σ B p ∈ linePair K (wMap K σ B w) := by
  obtain ⟨v, rfl⟩ := hp
  show ∃ v' : Fin 2 → K,
    phi K g σ B (w 0 • v, w 1 • v) = ((wMap K σ B w) 0 • v', (wMap K σ B w) 1 • v')
  refine ⟨(g : Matrix (Fin 2) (Fin 2) K) *ᵥ fun i => σ (v i), ?_⟩
  have hb : bPerm K B (w 0 • v, w 1 • v) =
      (((B : Matrix (Fin 2) (Fin 2) K) *ᵥ w) 0 • v, ((B : Matrix (Fin 2) (Fin 2) K) *ᵥ w) 1 • v) := by
    rw [bPerm_apply]
    refine Prod.ext ?_ ?_ <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, add_smul, smul_smul]
  have hσv : ∀ a b : K, sigmaPerm K σ (a • v, b • v) =
      (σ a • (fun i => σ (v i)), σ b • (fun i => σ (v i))) := by
    intro a b
    rw [sigmaPerm_apply]
    refine Prod.ext ?_ ?_ <;> funext i <;> simp [map_mul, smul_eq_mul]
  show rhoSL K g (sigmaPerm K σ (bPerm K B (w 0 • v, w 1 • v))) = _
  rw [hb, hσv, rhoSL_apply]
  dsimp only
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul]
  rfl

private theorem ml_semilinear_unique {K : Type*} [Field K] (Φ : Equiv.Perm (Fin 2 → K))
    (σ τ : RingAut K) (hσ : IsSemilinear σ Φ) (hτ : IsSemilinear τ Φ) : σ = τ := by
  obtain ⟨-, hσs⟩ := hσ
  obtain ⟨-, hτs⟩ := hτ
  have h0 : Φ 0 = 0 := by simpa using hσs 0 0
  have hne : (![1, 0] : Fin 2 → K) ≠ 0 := by
    intro h
    have h0' := congrFun h 0
    simp at h0'
  have hv : Φ ![1, 0] ≠ 0 := by
    intro h
    apply hne
    apply Φ.injective
    rw [h, h0]
  apply RingEquiv.ext
  intro c
  exact smul_left_injective K hv ((hσs c ![1, 0]).symm.trans (hτs c ![1, 0]))

private theorem ml_wMap_one_pow {K : Type*} [Field K] (B : GL (Fin 2) K) (n : ℕ)
    (v : Fin 2 → K) :
    (wMap K 1 B ^ n) v = ((B ^ n : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
    rw [pow_succ (wMap K 1 B) n, Equiv.Perm.mul_apply, wMap_one_apply, ih, Matrix.mulVec_mulVec,
      pow_succ B n, Units.val_mul]

private theorem ml_scalar_mulVec {K : Type*} [Field K] (c : K) (v : Fin 2 → K) :
    Matrix.scalar (Fin 2) c *ᵥ v = c • v := by
  funext i
  simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]

theorem exists_fixed_line (hAut : AutSL2Exists) {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K) {Γ : Type*} [Group Γ] (φ : Γ →* Equiv.Perm (UTilde K))
    (hadd : ∀ γ v w, φ γ (v + w) = φ γ v + φ γ w)
    (hnorm : ∀ (γ : Γ) (g : Matrix.SpecialLinearGroup (Fin 2) K),
      ∃ g' : Matrix.SpecialLinearGroup (Fin 2) K, φ γ * rhoSL K g = rhoSL K g' * φ γ)
    (hH2 : ∀ (γ : Γ) (g : Matrix.SpecialLinearGroup (Fin 2) K) (B : GL (Fin 2) K),
      φ γ = phi K g 1 B → ∃ (k : ℕ) (c : K),
        ((B : Matrix (Fin 2) (Fin 2) K)) ^ (2 ^ k) = Matrix.scalar (Fin 2) c) :
    ∃ w : Fin 2 → K, w ≠ 0 ∧ ∀ (γ : Γ) (p : UTilde K), p ∈ linePair K w → φ γ p ∈ linePair K w := by
  choose G S Bm hG using fun γ => normStruct hAut hK (φ γ) (hadd γ) (hnorm γ)
  let W : Γ →* Equiv.Perm (Fin 2 → K) :=
    MonoidHom.mk' (fun γ => wMap K (S γ) (Bm γ)) (by
      intro γ₁ γ₂
      have h1 : φ (γ₁ * γ₂) = φ γ₁ * φ γ₂ := map_mul φ γ₁ γ₂
      rw [hG (γ₁ * γ₂), hG γ₁, hG γ₂, phi_mul] at h1
      obtain ⟨-, hS, hB⟩ := phi_inj h1
      show wMap K (S (γ₁ * γ₂)) (Bm (γ₁ * γ₂)) = wMap K (S γ₁) (Bm γ₁) * wMap K (S γ₂) (Bm γ₂)
      rw [hS, hB, wMap_mul])
  have hWapp : ∀ γ, W γ = wMap K (S γ) (Bm γ) := fun γ => rfl
  have hsemi' : ∀ γ, IsSemilinear (S γ) (W γ) := fun γ => by
    rw [hWapp]
    exact wMap_semilinear (S γ) (Bm γ)
  have h2 : ∀ h ∈ W.range, IsSemilinear (1 : RingAut K) h →
      ∃ (k : ℕ) (c : K), ∀ v, (h ^ (2 ^ k)) v = c • v := by
    intro h hh h1
    obtain ⟨γ, rfl⟩ := MonoidHom.mem_range.mp hh
    have hS1 : S γ = 1 := ml_semilinear_unique (W γ) (S γ) 1 (hsemi' γ) h1
    have hφ : φ γ = phi K (G γ) 1 (Bm γ) := by rw [hG γ, hS1]
    obtain ⟨k, c, hk⟩ := hH2 γ (G γ) (Bm γ) hφ
    refine ⟨k, c, fun v => ?_⟩
    rw [hWapp γ, hS1, ml_wMap_one_pow, Units.val_pow_eq_pow_val, hk, ml_scalar_mulVec]
  have hsemi : ∀ h ∈ W.range, ∃ σ : RingAut K, IsSemilinear σ h := by
    intro h hh
    obtain ⟨γ, rfl⟩ := MonoidHom.mem_range.mp hh
    exact ⟨S γ, hsemi' γ⟩
  obtain ⟨v, hv0, hvmu⟩ := exists_invariant_line
    (fun σ Φ hΦ hc => exists_eigenvector_of_pow_scalar σ Φ hΦ hc.choose hc.choose_spec)
    W.range hsemi h2
  refine ⟨v, hv0, fun γ p hp => ?_⟩
  have hmem := phi_mem_linePair (G γ) (S γ) (Bm γ) v hp
  rw [← hG γ] at hmem
  obtain ⟨μ, hμ⟩ := hvmu (W γ) (MonoidHom.mem_range.mpr ⟨γ, rfl⟩)
  rw [hWapp γ] at hμ
  rw [hμ] at hmem
  obtain ⟨u, hu⟩ := hmem
  show ∃ u' : Fin 2 → K, φ γ p = (v 0 • u', v 1 • u')
  refine ⟨μ • u, ?_⟩
  rw [hu]
  refine Prod.ext ?_ ?_ <;> simp [smul_smul, mul_comm]

end CFSG.Quasithin.Vol2.Ch10Reselect
