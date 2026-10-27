module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.RankThree.PartOne.NF7H

theorem swap_false_of_conj {G : Type*} [Group G] {a₀ : G}
    (H0 : ∀ b k : G, b * b = 1 → (a₀ * b) ^ 4 = 1 → (a₀ * b) ^ 2 ≠ 1 → k * a₀ * k⁻¹ = b →
      ∀ j : Fin 4, k * b * k⁻¹ ≠ a₀ * (a₀ * b) ^ (j : ℕ))
    {a b k ka : G} (hka : ka * a₀ * ka⁻¹ = a) (hb : b * b = 1) (hab4 : (a * b) ^ 4 = 1)
    (hab2 : (a * b) ^ 2 ≠ 1) (hk : k * a * k⁻¹ = b) (j : Fin 4) :
    k * b * k⁻¹ ≠ a * (a * b) ^ (j : ℕ) := by
  intro heq
  have ha₀ : a₀ = ka⁻¹ * a * ka := by rw [← hka]; group
  have hcp : ∀ (x : G) (n : ℕ), (ka⁻¹ * x * ka) ^ n = ka⁻¹ * x ^ n * ka := by
    intro x n
    simpa using conj_pow (a := ka⁻¹) (b := x) (i := n)
  have h1 : a₀ * (ka⁻¹ * b * ka) = ka⁻¹ * (a * b) * ka := by rw [ha₀]; group
  refine H0 (ka⁻¹ * b * ka) (ka⁻¹ * k * ka) ?_ ?_ ?_ ?_ j ?_
  · calc ka⁻¹ * b * ka * (ka⁻¹ * b * ka) = ka⁻¹ * (b * b) * ka := by group
      _ = 1 := by rw [hb]; group
  · rw [h1, hcp, hab4]; group
  · rw [h1, hcp]
    intro h
    apply hab2
    have h2 := congrArg (fun x => ka * x * ka⁻¹) h
    simpa [mul_assoc] using h2
  · calc ka⁻¹ * k * ka * a₀ * (ka⁻¹ * k * ka)⁻¹ = ka⁻¹ * (k * (ka * a₀ * ka⁻¹) * k⁻¹) * ka := by
          rw [ha₀]; group
      _ = ka⁻¹ * b * ka := by rw [hka, hk]
  · have h2 : ka⁻¹ * k * ka * (ka⁻¹ * b * ka) * (ka⁻¹ * k * ka)⁻¹ = ka⁻¹ * (k * b * k⁻¹) * ka := by
      group
    have h3 : a₀ * (a₀ * (ka⁻¹ * b * ka)) ^ (j : ℕ) = ka⁻¹ * (a * (a * b) ^ (j : ℕ)) * ka := by
      rw [h1, hcp, ha₀]; group
    rw [h2, h3, heq]

abbrev Mat2 : Type := Matrix (Fin 3) (Fin 3) (ZMod 2)

abbrev A0m : Mat2 := !![1, 1, 0; 0, 1, 0; 0, 0, 1]

theorem A0m_det : A0m.det = 1 := by decide

theorem mat_conj_invol : ∀ B : Mat2, B.det = 1 → B * B = 1 → B ≠ 1 →
    ∃ K : Mat2, K.det = 1 ∧ K * A0m = B * K := by
  decide +kernel

@[expose] def NoSwap0 (B : Mat2) : Prop :=
  ∀ K : Mat2, K.det = 1 → K * A0m = B * K → ∀ j : Fin 4, K * B ≠ A0m * (A0m * B) ^ (j : ℕ) * K

instance (B : Mat2) : Decidable (NoSwap0 B) := by unfold NoSwap0; infer_instance

theorem mat_swap0 : ∀ B : Mat2, B.det = 1 → B * B = 1 → (A0m * B) ^ 4 = 1 → (A0m * B) ^ 2 ≠ 1 →
    NoSwap0 B := by
  decide +kernel

theorem det_GL32 (g : GL (Fin 3) (ZMod 2)) : (g : Mat2).det = 1 := by
  have h1 : Matrix.GeneralLinearGroup.det g = 1 := Subsingleton.elim _ _
  have h2 := congrArg (fun u : (ZMod 2)ˣ => (u : ZMod 2)) h1
  simpa using h2

@[expose] noncomputable def matUnit (M : Mat2) (h : M.det = 1) : GL (Fin 3) (ZMod 2) :=
  ((Matrix.isUnit_iff_isUnit_det M).mpr (by rw [h]; exact isUnit_one)).unit

theorem GL32_swap_false {a b k : GL (Fin 3) (ZMod 2)} (ha : a * a = 1) (hb : b * b = 1)
    (hab4 : (a * b) ^ 4 = 1) (hab2 : (a * b) ^ 2 ≠ 1) (hk : k * a * k⁻¹ = b) (j : Fin 4) :
    k * b * k⁻¹ ≠ a * (a * b) ^ (j : ℕ) := by
  have ha1 : a ≠ 1 := by
    rintro rfl
    apply hab2
    rw [one_mul, sq]
    exact hb
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : GL (Fin 3) (ZMod 2), (a₀ : Mat2) = A0m := ⟨matUnit A0m A0m_det, rfl⟩
  have hsq : (a : Mat2) * a = 1 := by
    have := congrArg (fun x : GL (Fin 3) (ZMod 2) => (x : Mat2)) ha
    simpa using this
  have hne : (a : Mat2) ≠ 1 := fun h => ha1 (Units.ext (by simpa using h))
  obtain ⟨K, hK, hKa⟩ := mat_conj_invol a (det_GL32 a) hsq hne
  obtain ⟨ka, hka⟩ : ∃ ka : GL (Fin 3) (ZMod 2), (ka : Mat2) = K := ⟨matUnit K hK, rfl⟩
  have hconj : ka * a₀ * ka⁻¹ = a := by
    have h1 : ka * a₀ = a * ka :=
      Units.ext (by rw [Units.val_mul, Units.val_mul, hka, ha₀]; exact hKa)
    rw [h1]
    group
  refine swap_false_of_conj (a₀ := a₀) ?_ hconj hb hab4 hab2 hk j
  intro b' k' hb' hab4' hab2' hk'' j' heq
  have hmat : (a₀ : Mat2) * b' = A0m * b' := by rw [ha₀]
  have h4 : (A0m * (b' : Mat2)) ^ 4 = 1 := by
    have := congrArg (fun x : GL (Fin 3) (ZMod 2) => (x : Mat2)) hab4'
    simpa [Units.val_pow_eq_pow_val, ha₀] using this
  have h2 : (A0m * (b' : Mat2)) ^ 2 ≠ 1 := by
    intro h
    apply hab2'
    apply Units.ext
    simpa [Units.val_pow_eq_pow_val, ha₀] using h
  have hbb : (b' : Mat2) * b' = 1 := by
    have := congrArg (fun x : GL (Fin 3) (ZMod 2) => (x : Mat2)) hb'
    simpa using this
  have hkA : (k' : Mat2) * A0m = b' * k' := by
    have h1 : k' * a₀ = b' * k' := by rw [← hk'']; group
    have := congrArg (fun x : GL (Fin 3) (ZMod 2) => (x : Mat2)) h1
    simpa [ha₀] using this
  have hkb : (k' : Mat2) * b' = A0m * (A0m * b') ^ (j' : ℕ) * k' := by
    have h1 : k' * b' = a₀ * (a₀ * b') ^ (j' : ℕ) * k' := by
      rw [← heq]; group
    have := congrArg (fun x : GL (Fin 3) (ZMod 2) => (x : Mat2)) h1
    simpa [Units.val_pow_eq_pow_val, ha₀] using this
  exact mat_swap0 b' (det_GL32 b') hbb h4 h2 k' (det_GL32 k') hkA j' hkb

end CFSG.RankThree.PartOne.NF7H
