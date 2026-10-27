module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteCalcNF
public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteCalcWord

public section

namespace CFSG.Quasithin.Fan86.Tutte

variable {H : Type*} [Group H] {s : ℕ} {r l ξ : H} {Hs : ℕ → Subgroup H}

theorem xi_nfw_7 (h : IsTutteSys s r l ξ Hs) (h7 : ξ * r * ξ = r⁻¹ ∧ ξ * l * ξ = l⁻¹) (e : ℤ)
    (K : List ℤ) : ξ * nfw r l e K * ξ = nfw r l e (K.map Neg.neg) := by
  induction K generalizing e with
  | nil => simpa [nfw] using h.xi_sq
  | cons t K ih =>
    simp only [nfw, List.map_cons]
    rw [xi_mul_conj h.xi_sq, xi_zpow_conj h.xi_sq, xi_tx_7 h h7, ih]

theorem inv_nfw (r l : H) (e : ℤ) (M : List ℤ) :
    (nfw r l e M)⁻¹ = nfw r l (if Even M.length then e else -e) M.reverse := by
  induction M generalizing e with
  | nil => simp [nfw]
  | cons t M ih =>
    have h1 : nfw r l e (t :: M) = tx r l t ^ e * nfw r l (-e) M := rfl
    rw [h1, mul_inv_rev, ih, List.reverse_cons, nfw_append]
    by_cases hM : Even M.length <;>
      simp [hM, nfw, Nat.even_add_one, List.length_reverse, zpow_neg]

theorem nfw_append_zero (r l : H) (e : ℤ) (K : List ℤ) : nfw r l e (K ++ [0]) = nfw r l e K := by
  rw [nfw_append]
  simp [nfw, tx_zero]

theorem nfw_shift_eq (e : ℤ) (he : e = 1 ∨ e = -1) (j : ℤ) {K K' : List ℤ} (hK : Even K.length)
    (hK' : Even K'.length) (heq : nfw r l e K = nfw r l e K') :
    nfw r l e (K.map (· + j)) = nfw r l e (K'.map (· + j)) := by
  rcases he with rfl | rfl
  · rw [← nfw_shift_l r l j K hK, ← nfw_shift_l r l j K' hK', heq]
  · rw [← nfw_shift_r r l j K hK, ← nfw_shift_r r l j K' hK', heq]

theorem xi_inv_conj (hξ : ξ * ξ = 1) (g : H) : ξ * g⁻¹ * ξ = (ξ * g * ξ)⁻¹ := by
  simpa using xi_zpow_conj hξ g (-1)

theorem sq_eq_nfw_reverse (h : IsTutteSys s r l ξ Hs) (h7 : ξ * r * ξ = r⁻¹ ∧ ξ * l * ξ = l⁻¹)
    (i : ℕ) (e : ℤ) (he : e = 1 ∨ e = -1) {L : List ℤ} (hL : Even L.length)
    (heq : nfw r l e L = tx r l i ^ 2) :
    tx r l i ^ 2 = nfw r l e ((L.map ((i : ℤ) - ·)).reverse) := by
  obtain ⟨K₀, hK₀len, hK₀, hK₀'⟩ : ∃ K₀ : List ℤ, Even K₀.length ∧ nfw r l e K₀ = tx r l i ^ 2 ∧
      nfw r l e (K₀.map (· + (-(i : ℤ)))) = (tx r l (-(i : ℤ)))⁻¹ * (tx r l (-(i : ℤ)))⁻¹ := by
    rcases he with rfl | rfl
    · exact ⟨[i, 0, i, 0], ⟨2, rfl⟩, by simp [nfw, tx_zero, pow_two], by simp [nfw, tx_zero]⟩
    · exact ⟨[0, i, 0, i], ⟨2, rfl⟩, by simp [nfw, tx_zero, pow_two], by simp [nfw, tx_zero]⟩
  have h3 := nfw_shift_eq e he (-(i : ℤ)) hK₀len hL (hK₀.trans heq.symm)
  rw [hK₀'] at h3
  have h4 := congrArg (fun g => ξ * g * ξ) h3
  rw [xi_nfw_7 h h7, xi_mul_conj h.xi_sq, xi_inv_conj h.xi_sq, xi_tx_7 h h7, neg_neg,
    List.map_map] at h4
  have hfun : (Neg.neg ∘ fun t : ℤ => t + -(i : ℤ)) = fun t => (i : ℤ) - t := by
    funext t
    show -(t + -(i : ℤ)) = (i : ℤ) - t
    ring
  rw [hfun] at h4
  have h5 := congrArg (fun g => g⁻¹) h4
  simp only [mul_inv_rev, inv_inv] at h5
  have hinv := inv_nfw r l e (L.map ((i : ℤ) - ·))
  simp only [List.length_map, hL, ↓reduceIte] at hinv
  rw [hinv] at h5
  rw [pow_two]
  exact h5

theorem sq_nf_palindromic (h : IsTutteSys s r l ξ Hs)
    (h7 : ξ * r * ξ = r⁻¹ ∧ ξ * l * ξ = l⁻¹) {i : ℕ} (hi : 1 ≤ i) (his : i < s) (e : ℤ)
    (he : e = 1 ∨ e = -1) {L : List ℤ} (hL : L.Pairwise (· > ·))
    (hL1 : ∀ t ∈ L, 1 ≤ t ∧ t < i) (heq : nfw r l e L = tx r l i ^ 2) :
    L = (L.map ((i : ℤ) - ·)).reverse := by
  have hN : ∀ t ∈ (L.map ((i : ℤ) - ·)).reverse, 1 ≤ t ∧ t < i := by
    intro t ht
    rw [List.mem_reverse, List.mem_map] at ht
    obtain ⟨u, hu, rfl⟩ := ht
    have := hL1 u hu
    omega
  by_cases hEven : Even L.length
  · have h1 := sq_eq_nfw_reverse h h7 i e he hEven heq
    refine nf_unique h e he hL ?_ (fun t ht => ⟨(hL1 t ht).1, by have := (hL1 t ht).2; omega⟩)
      (fun t ht => ⟨(hN t ht).1, by have := (hN t ht).2; omega⟩) (heq.trans h1)
    rw [List.pairwise_reverse, List.pairwise_map]
    exact hL.imp fun {a b} hab => by omega
  · exfalso
    have hEven' : Even (L ++ [0]).length := by simpa [Nat.even_add_one] using hEven
    have h1 := sq_eq_nfw_reverse h h7 i e he hEven' ((nfw_append_zero r l e L).trans heq)
    simp only [List.map_append, List.map_cons, List.map_nil, List.reverse_append,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, sub_zero] at h1
    have hhead := nfw_head h hi his e he hN
    apply hhead.2
    rw [← h1, ← heq]
    exact nfw_mem h (by omega) e fun t ht => ⟨(hL1 t ht).1, by have := (hL1 t ht).2; omega⟩

end CFSG.Quasithin.Fan86.Tutte
