module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteCoreRho
public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteCalcAbelSq
public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteCoreAlg

public section

namespace CFSG.Quasithin.Fan86.Tutte

variable {H : Type*} [Group H] {s : ℕ} {r l ξ : H} {Hs : ℕ → Subgroup H}

theorem conj_inv_mul_mul {ρ : H} (hρ : ρ * ρ = 1) (X Y W : H) :
    ρ * (X⁻¹ * (Y * W)) * ρ = (ρ * X * ρ)⁻¹ * ((ρ * Y * ρ) * (ρ * W * ρ)) := by
  have hi : ρ⁻¹ = ρ := inv_eq_of_mul_eq_one_right hρ
  have e : ∀ x y : H, ρ * (x * y) * ρ = (ρ * x * ρ) * (ρ * y * ρ) := by
    intro x y
    calc ρ * (x * y) * ρ = ρ * x * (ρ * ρ) * y * ρ := by rw [hρ]; simp [mul_assoc]
      _ = (ρ * x * ρ) * (ρ * y * ρ) := by simp only [mul_assoc]
  have einv : ρ * X⁻¹ * ρ = (ρ * X * ρ)⁻¹ := by simp [mul_inv_rev, hi, mul_assoc]
  rw [e, e, einv]

section Case7

variable (h : IsTutteSys s r l ξ Hs) (h7 : ξ * r * ξ = r⁻¹ ∧ ξ * l * ξ = l⁻¹)

include h h7

theorem rho_nfw7 : ∀ n : ℕ, ∀ K : List ℤ, K.length = 2 * n →
    rho r ξ s * nfw r l (-1) K * rho r ξ s = nfw r l (-1) (K.map fun t => (s : ℤ) - t)
  | 0, K, hK => by
    have : K = [] := List.length_eq_zero_iff.mp (by omega)
    subst this
    simp [nfw, rho_sq7 h h7]
  | n + 1, K, hK => by
    rcases K with _ | ⟨a, _ | ⟨b, K'⟩⟩
    · simp at hK
    · simp at hK
      omega
    · have hnf : ∀ a b K', nfw r l (-1) (a :: b :: K') =
          (tx r l a)⁻¹ * (tx r l b * nfw r l (-1) K') := by
        intro a b K'
        simp [nfw]
      have ih := rho_nfw7 n K' (by simp at hK; omega)
      rw [List.map_cons, List.map_cons, hnf, hnf, conj_inv_mul_mul (rho_sq7 h h7),
        rho_tx7 h h7, rho_tx7 h h7, ih]
      group

theorem hstar7 (L : List ℤ) (hodd : Odd L.length)
    (hLh : nfw r l (-1) L = rho r ξ s * tx r l s) :
    nfw r l (-1) (L.map fun t => (s : ℤ) - t) =
      rho r ξ s * (rho r ξ s * tx r l s) * rho r ξ s * (tx r l s)⁻¹ := by
  obtain ⟨m, hm⟩ := hodd
  have hmL : ¬ Even L.length := by
    rw [hm]
    simp
  have h1 := rho_nfw7 h h7 (m + 1) (L ++ [0]) (by simp [hm]; omega)
  rw [List.map_append, List.map_cons, List.map_nil, nfw_append, nfw_append] at h1
  simp only [List.length_map, hmL, ite_false, neg_neg, nfw, tx_zero, sub_zero, zpow_one,
    mul_one] at h1
  rw [hLh] at h1
  have e := congrArg (fun x => x * (tx r l s)⁻¹) h1
  simp only [mul_inv_cancel_right] at e
  exact e.symm

theorem rel7 {i : ℕ} (hi : 1 ≤ i) (his : 2 * i ≤ s) (hab : Abel Hs (s - i)) (L : List ℤ)
    (hodd : Odd L.length) (hLh : nfw r l (-1) L = rho r ξ s * tx r l s) :
    nfw r l (-1) (L ++ [(i : ℤ)] ++ L.map (fun t => (s : ℤ) - t) ++ [(s : ℤ) - i]) = 1 := by
  obtain ⟨m, hm⟩ := hodd
  have hmL : ¬ Even L.length := by
    rw [hm]
    simp
  have hsplit : nfw r l (-1) (L ++ [(i : ℤ)] ++ L.map (fun t => (s : ℤ) - t) ++ [(s : ℤ) - i]) =
      nfw r l (-1) L * tx r l i * nfw r l (-1) (L.map fun t => (s : ℤ) - t) *
        tx r l ((s : ℤ) - i) := by
    rw [nfw_append, nfw_append, nfw_append]
    simp only [List.length_append, List.length_map, List.length_singleton, hm, nfw, mul_one,
      neg_neg]
    have e1 : ¬ Even (2 * m + 1) := by simp
    have e2 : Even (2 * m + 1 + 1) := by simp [Nat.even_iff]
    have e3 : ¬ Even (2 * m + 1 + 1 + (2 * m + 1)) := by simp [Nat.even_iff]; omega
    simp only [e1, e2, e3, ite_true, ite_false, zpow_one]
  rw [hsplit, hLh, hstar7 h h7 L ⟨m, hm⟩ hLh]
  have hs : ((s - i : ℕ) : ℤ) = (s : ℤ) - i := Nat.cast_sub (by omega)
  have hAA := abel_sq_eq_one h (i := s - i) (k := i) (by have := h.one_le; omega) hab hi
    (by omega)
  have hBB := abel_sq_eq_one h (i := s - i) (k := s - i) (by have := h.one_le; omega) hab
    (by omega) le_rfl
  rw [hs] at hBB
  exact rel7_alg (rho r ξ s) (tx r l s) (tx r l i) (tx r l ((s : ℤ) - i)) (rho_sq7 h h7)
    (rho_tx7_s h h7) (rho_tx7 h h7 i) (by simpa [pow_two] using hAA) (by simpa [pow_two] using hBB)

theorem x_conj7 (a : ℤ) :
    tx r l s * tx r l a * tx r l s =
      (rho r ξ s * (rho r ξ s * tx r l s) * rho r ξ s * (tx r l s)⁻¹) * tx r l ((s : ℤ) - a) *
        (rho r ξ s * tx r l s) :=
  x_conj_alg _ _ _ _ (rho_sq7 h h7) (rho_tx7 h h7 a)

end Case7

end CFSG.Quasithin.Fan86.Tutte
