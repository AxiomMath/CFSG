module

public import CFSG.Quasithin.MS93.ASC134NC5Lin

public section

namespace CFSG.Quasithin.MS93.AS

open Matrix

variable {F : Type} [Field F]

theorem dg_injective {g h : SL3 F} (hgh : ∀ n, dg g n = dg h n) : g = h := by
  apply Subtype.ext
  ext i j
  have := congrFun (congrFun (hgh (Pi.single 0 (Pi.single j 1))) 0) i
  simpa [dg, Matrix.mulVec, dotProduct, Pi.single_apply] using this

theorem exists_decomp_of_sq [Finite F] {a : (Fin 2 → Fin 3 → F) ≃+ (Fin 2 → Fin 3 → F)}
    (hsq : ∀ n, a (a n) = n)
    (hnorm : ∀ g : SL3 F, ∃ h : SL3 F, ∀ n, a (dg g n) = dg h (a n)) :
    ∃ (t : (Fin 3 → F) ≃+ (Fin 3 → F)) (Λ : Matrix (Fin 2) (Fin 2) F) (σ : F ≃+* F),
      (∀ g : SL3 F, ∃ h : SL3 F, ∀ w, t (((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w) =
        ((h : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ t w) ∧
      (∀ (μ : F) w, t (μ • w) = σ μ • t w) ∧ ∀ n i, a n i = t (∑ j, Λ i j • n j) := by
  choose θ hθ using hnorm
  have haa := hsq
  have hθs : Function.Surjective θ := by
    intro h
    refine ⟨θ h, dg_injective fun n => ?_⟩
    have e1 := hθ (θ h) (a n)
    rw [haa, ← hθ h n, haa] at e1
    exact e1.symm
  obtain ⟨t, Λ, ht, hrep⟩ := exists_decomp a θ hθ
  obtain ⟨σ, hσ⟩ := exists_semilinear t θ ht hθs
  exact ⟨t, Λ, σ, fun g => ⟨θ g, ht g⟩, hσ, hrep⟩

@[expose] def IsRep (a : (Fin 2 → Fin 3 → F) → (Fin 2 → Fin 3 → F)) (Λ : Matrix (Fin 2) (Fin 2) F)
    (t : (Fin 3 → F) ≃+ (Fin 3 → F)) : Prop :=
  (∀ (μ : F) w, t (μ • w) = μ • t w) ∧
    (∀ g : SL3 F, ∃ h : SL3 F, ∀ w, t (((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w) =
      ((h : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ t w) ∧
    ∀ n i, a n i = ∑ j, Λ i j • t (n j)

@[expose] def IsNRep (a : (Fin 2 → Fin 3 → F) → (Fin 2 → Fin 3 → F)) (Λ : Matrix (Fin 2) (Fin 2) F)
    (t : (Fin 3 → F) ≃+ (Fin 3 → F)) : Prop :=
  IsRep a Λ t ∧ Λ * Λ = 1 ∧ ∀ w, t (t w) = w

theorem IsRep.apply_single {a : (Fin 2 → Fin 3 → F) → (Fin 2 → Fin 3 → F)}
    {Λ : Matrix (Fin 2) (Fin 2) F}
    {t : (Fin 3 → F) ≃+ (Fin 3 → F)} (h : IsRep a Λ t) (k : Fin 2) (w : Fin 3 → F) (i : Fin 2) :
    a (Pi.single k w) i = Λ i k • t w := by
  rw [h.2.2, Finset.sum_eq_single k]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

theorem addEquiv_apply_single_ne_zero (t : (Fin 3 → F) ≃+ (Fin 3 → F)) :
    t (Pi.single 0 1) ≠ 0 := by
  intro h
  have h0 : t (Pi.single 0 1) = t 0 := by rw [h, map_zero]
  have := congrFun (t.injective h0) 0
  simp at this

theorem IsRep.unique {a : (Fin 2 → Fin 3 → F) → (Fin 2 → Fin 3 → F)} (ha : Function.Surjective a)
    {Λ₁ Λ₂ : Matrix (Fin 2) (Fin 2) F} {t₁ t₂ : (Fin 3 → F) ≃+ (Fin 3 → F)} (h₁ : IsRep a Λ₁ t₁)
    (h₂ : IsRep a Λ₂ t₂) :
    ∃ c : F, Λ₂ = c • Λ₁ ∧ ∀ w, t₁ w = c • t₂ w := by
  have hsame : ∀ (g : SL3 F) (w : Fin 3 → F), t₂.symm (t₁ (((g : SL3 F) :
      Matrix (Fin 3) (Fin 3) F) *ᵥ w)) = ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
        t₂.symm (t₁ w) := by
    intro g w
    obtain ⟨h, hh⟩ := h₁.2.1 g
    obtain ⟨h', hh'⟩ := h₂.2.1 g
    have hagree : ∀ y : Fin 3 → F, ((h : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ y =
        ((h' : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ y := by
      intro y
      obtain ⟨n, hn⟩ := ha (Pi.single 0 y)
      have hy : a n 0 = y := by rw [hn]; simp
      have e1 : a (dg g n) 0 = ((h : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ a n 0 := by
        rw [h₁.2.2, h₁.2.2]
        simp only [dg_apply, hh, Matrix.mulVec_sum, Matrix.mulVec_smul]
      have e2 : a (dg g n) 0 = ((h' : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ a n 0 := by
        rw [h₂.2.2, h₂.2.2]
        simp only [dg_apply, hh', Matrix.mulVec_sum, Matrix.mulVec_smul]
      rw [← hy, ← e1, e2]
    apply t₂.injective
    rw [AddEquiv.apply_symm_apply, hh, hagree, hh', AddEquiv.apply_symm_apply]
  obtain ⟨c, hc⟩ := schur_W (f := (t₂.symm : (Fin 3 → F) →+ (Fin 3 → F)).comp
    (t₁ : (Fin 3 → F) →+ (Fin 3 → F))) fun g w => hsame g w
  have ht : ∀ w, t₁ w = c • t₂ w := fun w => by
    have := hc w
    simp only [AddMonoidHom.coe_comp, AddMonoidHom.coe_ofClass, Function.comp_apply] at this
    rw [← h₂.1, ← this, AddEquiv.apply_symm_apply]
  refine ⟨c, ?_, ht⟩
  ext i j
  have e := (h₁.apply_single j (Pi.single 0 1) i).symm.trans (h₂.apply_single j (Pi.single 0 1) i)
  rw [ht, smul_smul] at e
  have := smul_left_injective F (addEquiv_apply_single_ne_zero t₂) e
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [← this, mul_comm]

theorem IsNRep.unique [CharP F 2] {a : (Fin 2 → Fin 3 → F) → (Fin 2 → Fin 3 → F)}
    (ha : Function.Surjective a)
    {Λ₁ Λ₂ : Matrix (Fin 2) (Fin 2) F} {t₁ t₂ : (Fin 3 → F) ≃+ (Fin 3 → F)}
    (h₁ : IsNRep a Λ₁ t₁) (h₂ : IsNRep a Λ₂ t₂) : Λ₁ = Λ₂ ∧ ∀ w, t₁ w = t₂ w := by
  obtain ⟨c, hΛ, ht⟩ := IsRep.unique ha h₁.1 h₂.1
  have hc2 : c * c = 1 := by
    have h22 := h₂.2.1
    rw [hΛ, smul_mul_smul_comm, h₁.2.1] at h22
    have := congrFun (congrFun h22 0) 0
    simpa using this
  have hc : c = 1 := by
    have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
    have h0 : (c - 1) ^ 2 = 0 := by linear_combination hc2 + (1 - c) * h2
    exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h0)
  refine ⟨?_, fun w => ?_⟩
  · rw [hΛ, hc, one_smul]
  · rw [ht, hc, one_smul]

theorem IsRep.mul {a b : (Fin 2 → Fin 3 → F) → (Fin 2 → Fin 3 → F)}
    {Λ₁ Λ₂ : Matrix (Fin 2) (Fin 2) F} {t₁ t₂ : (Fin 3 → F) ≃+ (Fin 3 → F)} (h₁ : IsRep a Λ₁ t₁)
    (h₂ : IsRep b Λ₂ t₂) : IsRep (a ∘ b) (Λ₁ * Λ₂) (t₂.trans t₁) := by
  refine ⟨fun μ w => ?_, fun g => ?_, fun n i => ?_⟩
  · simp only [AddEquiv.trans_apply]
    rw [h₂.1, h₁.1]
  · obtain ⟨h, hh⟩ := h₂.2.1 g
    obtain ⟨h', hh'⟩ := h₁.2.1 h
    exact ⟨h', fun w => by simp only [AddEquiv.trans_apply]; rw [hh, hh']⟩
  · show a (b n) i = _
    rw [h₁.2.2]
    simp only [h₂.2.2, map_sum, h₁.1, Finset.smul_sum, smul_smul, AddEquiv.trans_apply,
      Matrix.mul_apply, Finset.sum_smul]
    exact Finset.sum_comm

theorem exists_nrep [Finite F] [CharP F 2] {a : (Fin 2 → Fin 3 → F) ≃+ (Fin 2 → Fin 3 → F)}
    (hsq : ∀ n, a (a n) = n)
    (hnorm : ∀ g : SL3 F, ∃ h : SL3 F, ∀ n, a (dg g n) = dg h (a n))
    (hlin : ∀ (μ : F) n, a (μ • n) = μ • a n) :
    ∃ (Λ : Matrix (Fin 2) (Fin 2) F) (t : (Fin 3 → F) ≃+ (Fin 3 → F)), IsNRep a Λ t := by
  obtain ⟨t, Λ, σ, ht, hσ, hrep⟩ := exists_decomp_of_sq hsq hnorm
  have hσ1 : ∀ μ, σ μ = μ := by
    intro μ
    obtain ⟨n, hn⟩ := a.surjective (Pi.single 0 (Pi.single 0 1))
    have e : a (μ • n) 0 = σ μ • a n 0 := by
      rw [hrep, hrep, ← hσ, Finset.smul_sum]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Pi.smul_apply, smul_comm]
    rw [hlin, hn] at e
    have := congrFun e 0
    simpa using this.symm
  have htlin : ∀ (μ : F) w, t (μ • w) = μ • t w := fun μ w => by rw [hσ, hσ1]
  have hR : IsRep a Λ t := ⟨htlin, ht, fun n i => by rw [hrep, map_sum]; simp only [htlin]⟩
  have haa := hsq
  have hsq' : ∀ i k w, (Λ * Λ) i k • t (t w) = (Pi.single k w : Fin 2 → Fin 3 → F) i := by
    intro i k w
    have := congrFun (haa (Pi.single k w)) i
    rw [← this, hR.2.2]
    simp only [hR.apply_single, htlin, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  set κ := (Λ * Λ) 0 0 with hκ
  have he : (Pi.single 0 1 : Fin 3 → F) ≠ 0 := by
    intro h
    have := congrFun h 0
    simp at this
  have hκ0 : κ ≠ 0 := by
    intro h0
    have := hsq' 0 0 (Pi.single 0 1)
    rw [← hκ, h0, zero_smul, Pi.single_eq_same] at this
    exact he this.symm
  have htt : ∀ w, t (t w) = κ⁻¹ • w := by
    intro w
    have := hsq' 0 0 w
    rw [← hκ, Pi.single_eq_same] at this
    calc t (t w) = κ⁻¹ • (κ • t (t w)) := by rw [smul_smul, inv_mul_cancel₀ hκ0, one_smul]
      _ = κ⁻¹ • w := by rw [this]
  have hΛΛ : Λ * Λ = κ • 1 := by
    ext i k
    have := congrFun (hsq' i k (Pi.single 0 1)) 0
    rw [htt] at this
    simp only [Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, mul_one] at this
    by_cases hik : i = k
    · subst hik
      rw [Pi.single_eq_same, Pi.single_eq_same] at this
      rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
      have := congrArg (· * κ) this
      simpa [mul_assoc, inv_mul_cancel₀ hκ0] using this
    · rw [Pi.single_eq_of_ne hik] at this
      rw [Matrix.smul_apply, Matrix.one_apply_ne hik, smul_zero]
      simp only [Pi.zero_apply, mul_eq_zero, inv_eq_zero, hκ0, or_false] at this
      exact this
  obtain ⟨ν, hν⟩ : ∃ ν : F, ν * ν = κ := by
    obtain ⟨ν, hν⟩ := surjective_frobenius F 2 κ
    exact ⟨ν, by rw [← hν, frobenius_def, pow_two]⟩
  have hν0 : ν ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hν
    exact hκ0 hν.symm
  let t' : (Fin 3 → F) ≃+ (Fin 3 → F) :=
    { toFun := fun w => ν • t w
      invFun := fun w => t.symm (ν⁻¹ • w)
      left_inv := fun w => by simp [smul_smul, inv_mul_cancel₀ hν0]
      right_inv := fun w => by simp [smul_smul, mul_inv_cancel₀ hν0]
      map_add' := fun x y => by simp [smul_add] }
  have ht' : ∀ w, t' w = ν • t w := fun _ => rfl
  refine ⟨ν⁻¹ • Λ, t', ⟨fun μ w => ?_, fun g => ?_, fun n i => ?_⟩, ?_, fun w => ?_⟩
  · rw [ht', ht', htlin, smul_comm]
  · obtain ⟨h, hh⟩ := ht g
    exact ⟨h, fun w => by rw [ht', ht', hh, Matrix.mulVec_smul]⟩
  · rw [hR.2.2]
    refine Finset.sum_congr rfl fun j _ => ?_
    show Λ i j • t (n j) = (ν⁻¹ • Λ) i j • (ν • t (n j))
    rw [Matrix.smul_apply, smul_eq_mul, smul_smul]
    congr 1
    field_simp
  · rw [smul_mul_smul_comm, hΛΛ, smul_smul, ← mul_inv, hν, inv_mul_cancel₀ hκ0, one_smul]
  · rw [ht', ht', htlin, htt, smul_smul, smul_smul, hν, mul_inv_cancel₀ hκ0, one_smul]

end CFSG.Quasithin.MS93.AS
