module

public import CFSG.Quasithin.Background.HSL

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Open.StatedAPI Matrix
open scoped Matrix

namespace P22x

section F2

variable {F : Type} [Field F] [Finite F]

theorem sl2_conj_backward (Θ : (Fin 2 → F) ≃+ (Fin 2 → F))
    (hΘ : ∀ g : ↥(StatedSL 2 F), ∃ g' : ↥(StatedSL 2 F), ∀ v,
      Θ ((((g : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ v) =
        (((g' : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ Θ v) :
    ∀ g : ↥(StatedSL 2 F), ∃ g' : ↥(StatedSL 2 F), ∀ v,
      Θ.symm ((((g : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ v) =
        (((g' : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ Θ.symm v := by
  choose f hf using hΘ
  have hinj : Function.Injective f := by
    intro g₁ g₂ h
    apply Subtype.ext
    apply Units.ext
    ext i j
    have h1 := hf g₁ (Pi.single j 1)
    have h2 := hf g₂ (Pi.single j 1)
    rw [h] at h1
    have h3 := Θ.injective (h1.trans h2.symm)
    have h4 := congrFun h3 i
    rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one] at h4
    exact h4
  have hsurj := Finite.surjective_of_injective hinj
  intro g
  obtain ⟨g₀, rfl⟩ := hsurj g
  refine ⟨g₀, fun v => ?_⟩
  apply Θ.injective
  rw [hf g₀ (Θ.symm v)]
  simp

theorem sl2_linear_of_fixed_line (Θ : (Fin 2 → F) ≃+ (Fin 2 → F))
    (hΘ : ∀ g : ↥(StatedSL 2 F), ∃ g' : ↥(StatedSL 2 F), ∀ v,
      Θ ((((g : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ v) =
        (((g' : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ Θ v)
    {w₀ : Fin 2 → F} (hw₀ : w₀ ≠ 0) (hfix : ∀ c : F, Θ (c • w₀) = c • w₀) :
    ∀ (c : F) (v : Fin 2 → F), Θ (c • v) = c • Θ v := by
  have hb := sl2_conj_backward Θ hΘ
  intro c
  let f : (Fin 2 → F) →+ (Fin 2 → F) :=
    { toFun := fun v => Θ (c • Θ.symm v)
      map_zero' := by simp
      map_add' := fun v w => by simp [smul_add] }
  have hcomm : ∀ γ ∈ StatedSL 2 F, ∀ v, f ((γ : Matrix (Fin 2) (Fin 2) F) *ᵥ v) =
      (γ : Matrix (Fin 2) (Fin 2) F) *ᵥ f v := by
    intro γ hγ v
    obtain ⟨g', hg'⟩ := hb ⟨γ, hγ⟩
    have hrel : ∀ u, Θ ((((g' : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ u) =
        (γ : Matrix (Fin 2) (Fin 2) F) *ᵥ Θ u := by
      intro u
      have := congrArg Θ (hg' (Θ u))
      simp only [AddEquiv.apply_symm_apply, AddEquiv.symm_apply_apply] at this
      exact this.symm
    show Θ (c • Θ.symm ((γ : Matrix (Fin 2) (Fin 2) F) *ᵥ v)) =
      (γ : Matrix (Fin 2) (Fin 2) F) *ᵥ Θ (c • Θ.symm v)
    rw [hg' v, ← Matrix.mulVec_smul, hrel]
  obtain ⟨d, hd⟩ := CFSG.Quasithin.H.hasScalarCommutant_statedSL (K := F) (d := 2) le_rfl f hcomm
  have hΘw : Θ w₀ = w₀ := by simpa using hfix 1
  have hsymm : Θ.symm w₀ = w₀ := by
    rw [AddEquiv.symm_apply_eq]
    exact hΘw.symm
  have h1 : d • w₀ = c • w₀ := by
    have h0 : Θ (c • Θ.symm w₀) = d • w₀ := hd w₀
    rw [hsymm, hfix c] at h0
    exact h0.symm
  obtain ⟨j, hj⟩ : ∃ j, w₀ j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hw₀ (funext hcon)
  have hdc : d = c := by
    have := congrFun h1 j
    simp only [Pi.smul_apply, smul_eq_mul] at this
    exact mul_right_cancel₀ hj this
  intro v
  have key : Θ (c • Θ.symm (Θ v)) = c • Θ v := by
    have h2 := hd (Θ v)
    rw [hdc] at h2
    exact h2
  simpa using key

theorem not_dvd_card_linearEquiv {p : ℕ} (hp : p.Prime) (hpF : ¬ p ∣ Nat.card (StatedSL 2 F)) :
    ¬ p ∣ Nat.card ((Fin 2 → F) ≃ₗ[F] (Fin 2 → F)) := by
  have hGL : Nat.card ((Fin 2 → F) ≃ₗ[F] (Fin 2 → F)) = Nat.card (GL (Fin 2) F) :=
    (Nat.card_congr ((Matrix.GeneralLinearGroup.toLin.trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin 2 → F))).toEquiv)).symm
  have hSL : Nat.card (StatedSL 2 F) = Nat.card (SpecialLinearGroup (Fin 2) F) := card_statedSL 2 F
  have hmul := Matrix.card_SL_mul_card_units (n := Fin 2) (R := F)
  have hunits : Nat.card Fˣ = Nat.card F - 1 := Nat.card_units F
  have hq1 : Nat.card F - 1 ∣ Nat.card (StatedSL 2 F) := by
    rw [card_statedSL_two]
    refine Dvd.dvd.mul_left ?_ _
    obtain ⟨r, hr⟩ : ∃ r, Nat.card F = r + 1 :=
      ⟨Nat.card F - 1, by have := Nat.card_pos (α := F); omega⟩
    rw [hr]
    exact ⟨r + 2, by simp only [Nat.add_sub_cancel]; exact Nat.sub_eq_of_eq_add (by ring)⟩
  rw [hGL, ← hmul, ← hSL, hunits]
  intro hdvd
  rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h
  · exact hpF h
  · exact hpF (h.trans hq1)

theorem sl2_theta_eq_id {p : ℕ} (hp : p.Prime) (hpF : ¬ p ∣ Nat.card (StatedSL 2 F))
    (Θ : (Fin 2 → F) ≃+ (Fin 2 → F))
    (hΘ : ∀ g : ↥(StatedSL 2 F), ∃ g' : ↥(StatedSL 2 F), ∀ v,
      Θ ((((g : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ v) =
        (((g' : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ Θ v)
    {w₀ : Fin 2 → F} (hw₀ : w₀ ≠ 0) (hfix : ∀ c : F, Θ (c • w₀) = c • w₀)
    (hord : ∃ k : ℕ, ∀ v, (⇑Θ)^[p ^ k] v = v) : ∀ v, Θ v = v := by
  have hlin := sl2_linear_of_fixed_line Θ hΘ hw₀ hfix
  obtain ⟨k, hk⟩ := hord
  let Θl : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F) := Θ.toLinearEquiv hlin
  have hpow : Θl ^ (p ^ k) = 1 := by
    apply LinearEquiv.ext
    intro v
    rw [LinearEquiv.pow_apply]
    exact hk v
  have h1 : orderOf Θl ∣ p ^ k := orderOf_dvd_of_pow_eq_one hpow
  have h2 : orderOf Θl ∣ Nat.card ((Fin 2 → F) ≃ₗ[F] (Fin 2 → F)) := orderOf_dvd_natCard Θl
  have hcop : Nat.Coprime (p ^ k) (Nat.card ((Fin 2 → F) ≃ₗ[F] (Fin 2 → F))) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 (not_dvd_card_linearEquiv hp hpF))
  have h3 : orderOf Θl = 1 := Nat.eq_one_of_dvd_one (hcop ▸ Nat.dvd_gcd h1 h2)
  have h4 : Θl = 1 := orderOf_eq_one_iff.1 h3
  intro v
  have := congrArg (fun e : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F) => e v) h4
  simpa [Θl] using this

end F2

end P22x

end CFSG.LocalAnalysis.UniquenessCase.UC22
