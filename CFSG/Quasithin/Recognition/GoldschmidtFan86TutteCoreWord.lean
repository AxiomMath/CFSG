module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteCalcWord
public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteCalcNF
public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteCalcAbelSq

public section

namespace CFSG.Quasithin.Fan86.Tutte

variable {H : Type*} [Group H] {s : ℕ} {r l ξ : H} {Hs : ℕ → Subgroup H}

theorem tx_mem_nonneg (h : IsTutteSys s r l ξ Hs) {c : ℕ} (hc : c ≤ s) {t : ℤ} (ht0 : 0 ≤ t)
    (htc : t ≤ c) : tx r l t ∈ Hs c := by
  rcases eq_or_lt_of_le ht0 with rfl | ht1
  · rw [tx_zero]
    exact one_mem _
  · exact tx_int_mem h hc ht1 htc

theorem nfw_mem_nonneg (h : IsTutteSys s r l ξ Hs) {c : ℕ} (hc : c ≤ s) :
    ∀ (K : List ℤ) (e : ℤ), (∀ t ∈ K, 0 ≤ t ∧ t ≤ c) → nfw r l e K ∈ Hs c
  | [], _, _ => one_mem _
  | t :: K, e, hK => by
    have h1 := tx_mem_nonneg h hc (hK t (List.mem_cons_self ..)).1 (hK t (List.mem_cons_self ..)).2
    have h2 := nfw_mem_nonneg h hc K (-e) fun u hu => hK u (List.mem_cons_of_mem _ hu)
    exact mul_mem (zpow_mem h1 e) h2

theorem zpow_sign {x : H} (hx : x ^ 2 = 1) {e e' : ℤ} (he : e = 1 ∨ e = -1)
    (he' : e' = 1 ∨ e' = -1) : x ^ e = x ^ e' := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by rwa [← pow_two])
  rcases he with rfl | rfl <;> rcases he' with rfl | rfl <;> simp [hxi]

theorem nfw_filter_zero (h : IsTutteSys s r l ξ Hs) {k : ℕ} (hk : k < s) (hab : Abel Hs k) :
    ∀ (K : List ℤ), (∀ t ∈ K, 0 ≤ t ∧ t ≤ k) → ∀ e e' : ℤ, (e = 1 ∨ e = -1) → (e' = 1 ∨ e' = -1) →
      nfw r l e K = nfw r l e' (K.filter fun t => t ≠ 0)
  | [], _, _, _, _, _ => by simp [nfw]
  | t :: K, hK, e, e', he, he' => by
    have ih := nfw_filter_zero h hk hab K (fun u hu => hK u (List.mem_cons_of_mem _ hu))
    have hne : ∀ e : ℤ, (e = 1 ∨ e = -1) → (-e = 1 ∨ -e = -1) := by
      rintro e (rfl | rfl) <;> simp
    by_cases ht : t = 0
    · subst ht
      simp [nfw, tx_zero, ih (-e) e' (hne e he) he']
    · have ht1 : 1 ≤ t := by have := (hK t (List.mem_cons_self ..)).1; omega
      have hsq : tx r l t ^ 2 = 1 := by
        obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ t)
        have hle := (hK _ (List.mem_cons_self ..)).2
        exact abel_sq_eq_one h hk hab (by omega) (by omega)
      simp only [List.filter_cons, decide_not, ht, decide_false, Bool.not_false, ite_true, nfw]
      rw [zpow_sign hsq he he']
      congr 1
      simpa [decide_not] using ih (-e) (-e') (hne e he) (hne e' he')

theorem xi_nfw7 (h : IsTutteSys s r l ξ Hs) (h7 : ξ * r * ξ = r⁻¹ ∧ ξ * l * ξ = l⁻¹) (e : ℤ) :
    ∀ N : List ℤ, ξ * nfw r l e N * ξ = nfw r l e (N.map Neg.neg)
  | [] => by simp [nfw, h.xi_sq]
  | t :: N => by
    simp only [nfw, List.map_cons]
    rw [xi_mul_conj h.xi_sq, xi_zpow_conj h.xi_sq, xi_tx_7 h h7, xi_nfw7 h h7 (-e) N]

theorem xi_nfw8 (h : IsTutteSys s r l ξ Hs) (h8 : ξ * r * ξ = l⁻¹ ∧ ξ * l * ξ = r⁻¹) (e : ℤ) :
    ∀ N : List ℤ, ξ * nfw r l e N * ξ = nfw r l (-e) (N.map Neg.neg)
  | [] => by simp [nfw, h.xi_sq]
  | t :: N => by
    simp only [nfw, List.map_cons]
    rw [xi_mul_conj h.xi_sq, xi_zpow_conj h.xi_sq, xi_tx_8 h h8, inv_zpow', xi_nfw8 h h8 (-e) N]

end CFSG.Quasithin.Fan86.Tutte
