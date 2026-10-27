module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteEightRho
public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteCoreAlg
public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteCalcAbelSq

public section

namespace CFSG.Quasithin.Fan86.Tutte

variable {H : Type*} [Group H] {s : ℕ} {r l ξ : H} {Hs : ℕ → Subgroup H}

section Case8

variable (h : IsTutteSys s r l ξ Hs) (h8 : ξ * r * ξ = l⁻¹ ∧ ξ * l * ξ = r⁻¹)

include h h8

theorem rho_inv_tx8 (a : ℤ) :
    (rho r ξ s)⁻¹ * tx r l a * rho r ξ s = (tx r l ((s : ℤ) - a))⁻¹ * tx r l s := by
  have hPP := rho_sq8 h h8
  have e1 := rho_tx8 h h8 ((s : ℤ) - a)
  rw [sub_sub_cancel] at e1
  have e2 : tx r l ((s : ℤ) - a) =
      (rho r ξ s)⁻¹ * (tx r l s * (tx r l a)⁻¹) * rho r ξ s := by
    calc tx r l ((s : ℤ) - a) = (rho r ξ s)⁻¹ * (rho r ξ s * tx r l ((s : ℤ) - a) *
          (rho r ξ s)⁻¹) * rho r ξ s := by group
      _ = _ := by rw [e1]
  rw [e2, ← hPP]
  group

theorem rho_nfw8 : ∀ K : List ℤ, Even K.length →
    (rho r ξ s)⁻¹ * nfw r l 1 K * rho r ξ s = nfw r l (-1) (K.map fun t => (s : ℤ) - t) := by
  intro K
  induction K using List.twoStepInduction with
  | nil => intro _; simp [nfw]
  | singleton a => intro hK; exact absurd hK (by simp)
  | cons_cons a b K ih _ =>
    intro hK
    have hK' : Even K.length := by simpa [Nat.even_add_one, Nat.even_add] using hK
    rw [nfw_pair_pos, List.map_cons, List.map_cons, nfw_pair_neg, ← ih hK']
    have e : ∀ W : H, (rho r ξ s)⁻¹ * (tx r l a * ((tx r l b)⁻¹ * W)) * rho r ξ s =
        ((rho r ξ s)⁻¹ * tx r l a * rho r ξ s) *
          (((rho r ξ s)⁻¹ * tx r l b * rho r ξ s)⁻¹ * ((rho r ξ s)⁻¹ * W * rho r ξ s)) :=
      fun W => by group
    rw [e, rho_inv_tx8 h h8 a, rho_inv_tx8 h h8 b]
    generalize tx r l ((s : ℤ) - a) = Y1
    generalize tx r l ((s : ℤ) - b) = Y2
    generalize tx r l s = X
    generalize (rho r ξ s)⁻¹ * nfw r l 1 K * rho r ξ s = V
    group

theorem hstar8 (L : List ℤ) (heven : Even L.length)
    (hLh : nfw r l 1 L = rho r ξ s * tx r l s) :
    nfw r l (-1) (L.map fun t => (s : ℤ) - t) =
      (rho r ξ s)⁻¹ * (rho r ξ s * tx r l s) * rho r ξ s := by
  rw [← hLh]
  exact (rho_nfw8 h h8 L heven).symm

theorem rel8 {i : ℕ} (hi : 1 ≤ i) (his : 2 * i ≤ s) (hab : Abel Hs (s - i)) (L : List ℤ)
    (heven : Even L.length) (hLh : nfw r l 1 L = rho r ξ s * tx r l s) :
    nfw r l 1 (L ++ [(i : ℤ)] ++ L.map (fun t => (s : ℤ) - t) ++ [(s : ℤ) - i]) = 1 := by
  obtain ⟨m, hm⟩ := heven
  have hsplit : nfw r l 1 (L ++ [(i : ℤ)] ++ L.map (fun t => (s : ℤ) - t) ++ [(s : ℤ) - i]) =
      nfw r l 1 L * tx r l i * nfw r l (-1) (L.map fun t => (s : ℤ) - t) *
        (tx r l ((s : ℤ) - i))⁻¹ := by
    rw [nfw_append, nfw_append, nfw_append]
    simp only [List.length_append, List.length_map, List.length_singleton, hm, nfw, mul_one]
    have e1 : Even (m + m) := ⟨m, rfl⟩
    have e2 : ¬ Even (m + m + 1) := by simp [Nat.even_add_one, e1]
    have e3 : ¬ Even (m + m + 1 + (m + m)) := by simp [Nat.even_add_one, e1, Nat.even_add]
    simp only [e1, e2, e3, ite_true, ite_false, zpow_one, zpow_neg_one]
  rw [hsplit, hLh, hstar8 h h8 L ⟨m, hm⟩ hLh]
  have hs : ((s - i : ℕ) : ℤ) = (s : ℤ) - i := Nat.cast_sub (by omega)
  have hAA := abel_sq_eq_one h (i := s - i) (k := i) (by have := h.one_le; omega) hab hi
    (by omega)
  have hBB := abel_sq_eq_one h (i := s - i) (k := s - i) (by have := h.one_le; omega) hab
    (by omega) le_rfl
  rw [hs] at hBB
  have hB : rho r ξ s * tx r l ((s : ℤ) - i) * (rho r ξ s)⁻¹ = tx r l s * (tx r l i)⁻¹ := by
    have := rho_tx8 h h8 ((s : ℤ) - i)
    rwa [sub_sub_cancel] at this
  have hmid : (rho r ξ s)⁻¹ * (rho r ξ s * tx r l s) * rho r ξ s = tx r l s * rho r ξ s := by
    group
  rw [hmid]
  exact rel8_alg (rho r ξ s) (tx r l s) (tx r l i) (tx r l ((s : ℤ) - i)) (rho_sq8 h h8)
    (rho_tx8 h h8 i) hB (by simpa [pow_two] using hAA) (by simpa [pow_two] using hBB)

end Case8

end CFSG.Quasithin.Fan86.Tutte
