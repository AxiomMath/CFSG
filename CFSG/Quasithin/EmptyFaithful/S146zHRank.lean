module

public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice

public section

namespace CFSG.Quasithin

section Rank

@[expose] def sigDivHom {V : Type*} [CommGroup V] (σ : MulAut V) : V →* V :=
  (σ : V →* V) * (MonoidHom.id V)⁻¹

theorem sigDivHom_apply {V : Type*} [CommGroup V] (σ : MulAut V) (w : V) :
    sigDivHom σ w = σ w * w⁻¹ := by simp [sigDivHom]

theorem iterate_eq_pow_mulAut {V : Type*} [Group V] (α : MulAut V) (n : ℕ) (w : V) :
    (⇑α)^[n] w = (α ^ n) w := by
  induction n generalizing w with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', pow_succ', MulAut.mul_apply, ih]

theorem card_le_two_of_swap {V : Type*} [CommGroup V] (σ : MulAut V) (W₁ W₂ : Subgroup V) (v : V)
    (hF : ∀ w, σ w * w⁻¹ = 1 ∨ σ w * w⁻¹ = v) (hswap : ∀ w ∈ W₁, σ w ∈ W₂)
    (hinf : W₁ ⊓ W₂ = ⊥) : Nat.card W₁ ≤ 2 := by
  classical
  have hker : ∀ w ∈ W₁, sigDivHom σ w = 1 → w = 1 := by
    intro w hw h1
    rw [sigDivHom_apply, mul_inv_eq_one] at h1
    have : w ∈ W₁ ⊓ W₂ := ⟨hw, h1 ▸ hswap w hw⟩
    rw [hinf, Subgroup.mem_bot] at this
    exact this
  have hinj : Function.Injective (fun w : W₁ => decide (sigDivHom σ (w : V) = 1)) := by
    intro w₁ w₂ h
    have h' : decide (sigDivHom σ (w₁ : V) = 1) = decide (sigDivHom σ (w₂ : V) = 1) := h
    by_cases h1 : sigDivHom σ (w₁ : V) = 1
    · have h2 : sigDivHom σ (w₂ : V) = 1 := by
        by_contra h2
        simp [h1, h2] at h'
      have e1 := hker _ w₁.2 h1
      have e2 := hker _ w₂.2 h2
      exact Subtype.ext (e1.trans e2.symm)
    · have h2 : ¬ sigDivHom σ (w₂ : V) = 1 := by
        intro h2
        simp [h1, h2] at h'
      have hv1 : sigDivHom σ (w₁ : V) = v := by
        have := hF (w₁ : V)
        rw [← sigDivHom_apply] at this
        exact this.resolve_left h1
      have hv2 : sigDivHom σ (w₂ : V) = v := by
        have := hF (w₂ : V)
        rw [← sigDivHom_apply] at this
        exact this.resolve_left h2
      have h3 : sigDivHom σ ((w₁ : V) * (w₂ : V)⁻¹) = 1 := by
        rw [map_mul, map_inv, hv1, hv2, mul_inv_cancel]
      have h4 := hker _ (w₁ * w₂⁻¹).2 h3
      exact Subtype.ext (by simpa [mul_inv_eq_one] using h4)
  calc Nat.card W₁ ≤ Nat.card Bool := Nat.card_le_card_of_injective _ hinj
    _ = 2 := by simp

theorem card_le_four_of_inv {V : Type*} [CommGroup V] (α σ : MulAut V) (W : Subgroup V) (v : V)
    (hF : ∀ w, σ w * w⁻¹ = 1 ∨ σ w * w⁻¹ = v)
    (hσW : ∀ w ∈ W, σ w ∈ W)
    (hfix : ∀ w ∈ W, α w = w → w = 1)
    (hα2 : ∀ w ∈ W, α (α w) = w → w = 1)
    (hrel : (∀ w ∈ W, α (σ (α w)) = σ w) ∨ (∀ w ∈ W, σ (α w) = α (σ w)))
    (hσ1 : ∃ w ∈ W, σ w ≠ w) : Nat.card W ≤ 4 := by
  classical
  rcases hrel with hrel | hrel
  · let Ψ : W → Bool × Bool := fun w =>
      (decide (sigDivHom σ (w : V) = 1), decide (sigDivHom σ (α (w : V)) = 1))
    have hker : ∀ w ∈ W, sigDivHom σ w = 1 → sigDivHom σ (α w) = 1 → w = 1 := by
      intro w hw h1 h2
      rw [sigDivHom_apply, mul_inv_eq_one] at h1 h2
      apply hα2 w hw
      have := hrel w hw
      rw [h2, h1] at this
      exact this
    have hval : ∀ u : V, sigDivHom σ u ≠ 1 → sigDivHom σ u = v := by
      intro u hu
      have := hF u
      rw [← sigDivHom_apply] at this
      exact this.resolve_left hu
    have hinj : Function.Injective Ψ := by
      intro w₁ w₂ h
      have h' : (decide (sigDivHom σ (w₁ : V) = 1), decide (sigDivHom σ (α (w₁ : V)) = 1)) =
          (decide (sigDivHom σ (w₂ : V) = 1), decide (sigDivHom σ (α (w₂ : V)) = 1)) := h
      rw [Prod.mk.injEq] at h'
      obtain ⟨hh1, hh2⟩ := h'
      have key : ∀ u₁ u₂ : V, decide (sigDivHom σ u₁ = 1) = decide (sigDivHom σ u₂ = 1) →
          sigDivHom σ u₁ = sigDivHom σ u₂ := by
        intro u₁ u₂ hd
        by_cases h1 : sigDivHom σ u₁ = 1
        · have h2 : sigDivHom σ u₂ = 1 := by
            by_contra h2
            simp [h1, h2] at hd
          rw [h1, h2]
        · have h2 : ¬ sigDivHom σ u₂ = 1 := by
            intro h2
            simp [h1, h2] at hd
          rw [hval _ h1, hval _ h2]
      have e1 := key _ _ hh1
      have e2 := key _ _ hh2
      have hm : ((w₁ * w₂⁻¹ : W) : V) ∈ W := (w₁ * w₂⁻¹).2
      have h3 : sigDivHom σ ((w₁ : V) * (w₂ : V)⁻¹) = 1 := by
        rw [map_mul, map_inv, e1, mul_inv_cancel]
      have h4 : sigDivHom σ (α ((w₁ : V) * (w₂ : V)⁻¹)) = 1 := by
        rw [map_mul, map_inv, map_mul, map_inv, e2, mul_inv_cancel]
      have h5 := hker _ hm h3 h4
      exact Subtype.ext (by simpa [mul_inv_eq_one] using h5)
    calc Nat.card W ≤ Nat.card (Bool × Bool) := Nat.card_le_card_of_injective _ hinj
      _ = 4 := by simp
  · exfalso
    obtain ⟨w₀, hw₀, hσw₀⟩ := hσ1
    have hv : σ w₀ * w₀⁻¹ = v := by
      rcases hF w₀ with h1 | h1
      · exact absurd (mul_inv_eq_one.mp h1) hσw₀
      · exact h1
    have hv1 : v ≠ 1 := by
      intro h1
      rw [h1, mul_inv_eq_one] at hv
      exact hσw₀ hv
    have hvW : v ∈ W := hv ▸ W.mul_mem (hσW w₀ hw₀) (W.inv_mem hw₀)
    have hαv : α v = v := by
      have h2 : σ (α w₀) * (α w₀)⁻¹ = α v := by
        rw [hrel w₀ hw₀, ← hv, map_mul, map_inv]
      rcases hF (α w₀) with h1 | h1
      · rw [h1] at h2
        exact absurd (by simpa using (map_eq_one_iff α α.injective).mp h2.symm) hv1
      · rw [h1] at h2
        exact h2.symm
    exact hv1 (hfix v hvW hαv)

theorem prime_lt_card_of_free {V : Type*} [CommGroup V] [Finite V] (α : MulAut V) (W : Subgroup V) {p : ℕ}
    (hp : p.Prime) (hαW : ∀ w ∈ W, α w ∈ W) (hfix : ∀ w ∈ W, α w = w → w = 1)
    (hpow : ∀ w ∈ W, (⇑α)^[p] w = w) (hW : ∃ w ∈ W, w ≠ 1) : p < Nat.card W := by
  classical
  obtain ⟨w₀, hw₀, hw₀1⟩ := hW
  have hper : Function.IsPeriodicPt (⇑α) p w₀ := hpow w₀ hw₀
  have hdvd := hper.minimalPeriod_dvd
  have hne1 : Function.minimalPeriod (⇑α) w₀ ≠ 1 := by
    intro h1
    exact hw₀1 (hfix w₀ hw₀ (Function.minimalPeriod_eq_one_iff_isFixedPt.mp h1))
  have hmp : Function.minimalPeriod (⇑α) w₀ = p :=
    ((Nat.dvd_prime hp).mp hdvd).resolve_left hne1
  have hinjOn := (Function.iterate_injOn_Iio_minimalPeriod (f := ⇑α) (x := w₀))
  rw [hmp] at hinjOn
  have hiter : ∀ n : ℕ, (⇑α)^[n] w₀ ∈ W := by
    intro n
    induction n with
    | zero => exact hw₀
    | succ n ih => rw [Function.iterate_succ_apply']; exact hαW _ ih
  have hiter1 : ∀ n : ℕ, (⇑α)^[n] w₀ ≠ 1 := by
    intro n hn
    rw [iterate_eq_pow_mulAut] at hn
    exact hw₀1 ((map_eq_one_iff (α ^ n) (α ^ n).injective).mp hn)
  let F : Option (Fin p) → W := fun o => match o with
    | none => 1
    | some i => ⟨(⇑α)^[i.val] w₀, hiter i.val⟩
  have hinj : Function.Injective F := by
    intro o₁ o₂ h
    rcases o₁ with _ | i <;> rcases o₂ with _ | j
    · rfl
    · exact absurd (congrArg Subtype.val h).symm (hiter1 j.val)
    · exact absurd (congrArg Subtype.val h) (hiter1 i.val)
    · have h' : (⇑α)^[i.val] w₀ = (⇑α)^[j.val] w₀ := congrArg Subtype.val h
      exact congrArg some (Fin.ext (hinjOn (Set.mem_Iio.mpr i.2) (Set.mem_Iio.mpr j.2) h'))
  have := Nat.card_le_card_of_injective F hinj
  simp at this
  omega

end Rank

end CFSG.Quasithin
