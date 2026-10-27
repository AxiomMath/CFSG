module

public import CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb.Orbit

public section

namespace CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb

variable {n m : ℕ}

theorem shift_iter_half (hnm : n = 2 * m) (hm : 0 < m) {i : ℕ} (hi : i < n) :
    ∃ k < m, (shift n)^[i] {0, m} = {k, k + m} := by
  rw [shift_iter_pair (by omega) (by omega), zero_add]
  rcases Nat.lt_or_ge i m with h | h
  · refine ⟨i, h, ?_⟩
    rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt (by omega), add_comm]
  · refine ⟨i - m, by omega, ?_⟩
    rw [Nat.mod_eq_of_lt hi, show m + i = (i - m) + n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega), show i - m + m = i by omega, Finset.pair_comm]

theorem half_case_false (hnm : n = 2 * m) (hm : 0 < m) (p pY : (Fin 3 → Finset ℕ) → ℕ)
    (hshift : ∀ J, IsLabel n J → p (shiftL n J) = p J)
    (hperm : ∀ J, IsLabel n J → ∀ σ : Equiv.Perm (Fin 3), p (J ∘ σ) = p J)
    (hsum : ∑ J ∈ labels n, p J * 2 ^ lsize J = 8 * n)
    (hbound : ∀ J, IsLabel n J → p J ≤ ∑ i ∈ Finset.range n, pY ((shiftL n)^[n - i] J))
    (hpY : ∀ J, IsLabel n J → pY J ≠ 0 → ∃ l, J = slotLabel l {0, m})
    (hpos : ∃ l, 1 ≤ p (slotLabel l {0, m})) : False := by
  have hn : 0 < n := by omega
  have hmn : m < n := by omega
  have h0m : ∀ i ∈ ({0, m} : Finset ℕ), i < n := pair_lt hn hmn
  set c := p (slotLabel 0 {0, m}) with hc
  have hval : ∀ l, ∀ k < m, p (slotLabel l {k, k + m}) = c := by
    intro l k hk
    have h1 : slotLabel l {k, k + m} = (shiftL n)^[k] (slotLabel l {0, m}) := by
      rw [shiftL_iter_slotLabel, shift_iter_pair hn hmn, zero_add, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega), add_comm m k]
    rw [h1, p_shift_iter p hshift (isLabel_slotLabel h0m l), ← slotLabel_comp_swap 0 l,
      hperm _ (isLabel_slotLabel h0m 0)]
  have hc1 : 1 ≤ c := by
    obtain ⟨l, hl⟩ := hpos
    have := hval l 0 hm
    rw [zero_add] at this
    omega
  let S : Finset (Fin 3 → Finset ℕ) :=
    (Finset.univ ×ˢ Finset.range m).image fun x => slotLabel x.1 {x.2, x.2 + m}
  have hsupp : ∀ J, IsLabel n J → p J ≠ 0 → J ∈ S := by
    intro J hJ hJp
    have h := hbound J hJ
    obtain ⟨i, hi, hne⟩ : ∃ i ∈ Finset.range n, pY ((shiftL n)^[n - i] J) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      rw [Finset.sum_eq_zero hcon] at h
      omega
    have hJi : IsLabel n ((shiftL n)^[n - i] J) := by
      generalize n - i = k
      induction k with
      | zero => exact hJ
      | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact isLabel_shiftL ih
    obtain ⟨l, hl⟩ := hpY _ hJi hne
    rw [Finset.mem_range] at hi
    have hJ' : J = (shiftL n)^[i] (slotLabel l {0, m}) := by
      rw [← hl, ← Function.iterate_add_apply, Nat.add_sub_cancel' hi.le, shiftL_iterate_self hJ]
    obtain ⟨k, hk, hkk⟩ := shift_iter_half hnm hm hi
    rw [hJ', shiftL_iter_slotLabel, hkk]
    exact Finset.mem_image.mpr ⟨(l, k), by simp [hk], rfl⟩
  have hSlab : ∀ J ∈ S, IsLabel n J := by
    intro J hJ
    obtain ⟨⟨l, k⟩, hx, rfl⟩ := Finset.mem_image.mp hJ
    simp only [Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_range] at hx
    exact isLabel_slotLabel (pair_lt (by omega) (by omega)) l
  have hsum' : ∑ J ∈ labels n, p J * 2 ^ lsize J = ∑ J ∈ S, p J * 2 ^ lsize J := by
    symm
    apply Finset.sum_subset (fun J hJ => mem_labels.mpr (hSlab J hJ))
    intro J hJ hJS
    by_contra hne
    exact hJS (hsupp J (mem_labels.mp hJ) (fun h => hne (by rw [h, zero_mul])))
  have hinj : Set.InjOn (fun x : Fin 3 × ℕ => slotLabel x.1 {x.2, x.2 + m})
      ((Finset.univ ×ˢ Finset.range m : Finset (Fin 3 × ℕ)) : Set (Fin 3 × ℕ)) := by
    rintro ⟨l₁, k₁⟩ hx ⟨l₂, k₂⟩ hy h
    simp only [Finset.coe_product, Set.mem_prod, Finset.coe_univ, Set.mem_univ, true_and,
      Finset.coe_range, Set.mem_Iio] at hx hy
    dsimp only at h
    have hl : l₁ = l₂ := by
      by_contra hl
      have := congrFun h l₁
      rw [slotLabel_self, slotLabel_of_ne hl] at this
      exact Finset.insert_ne_empty _ _ this
    subst hl
    have h' := congrFun h l₁
    rw [slotLabel_self, slotLabel_self] at h'
    have hk1 : k₁ ∈ ({k₂, k₂ + m} : Finset ℕ) := h' ▸ Finset.mem_insert_self _ _
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk1
    rcases hk1 with h1 | h1
    · rw [h1]
    · omega
  rw [hsum', Finset.sum_image hinj] at hsum
  have hterm : ∀ x ∈ Finset.univ ×ˢ Finset.range m,
      p (slotLabel x.1 {x.2, x.2 + m}) * 2 ^ lsize (slotLabel x.1 {x.2, x.2 + m}) = c * 4 := by
    rintro ⟨l, k⟩ hx
    simp only [Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_range] at hx
    have hcard : ({k, k + m} : Finset ℕ).card = 2 := Finset.card_pair (by omega)
    rw [hval l k hx]
    congr 1
    fin_cases l <;> simp [lsize, slotLabel, hcard]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_product, Finset.card_univ,
    Fintype.card_fin, Finset.card_range, smul_eq_mul] at hsum
  have : 3 * m * (c * 4) = 16 * m := by rw [hsum]; omega
  have : 3 * c = 4 := by
    have h3 : m * (12 * c) = m * 16 := by nlinarith
    have := Nat.eq_of_mul_eq_mul_left hm h3
    omega
  omega

end CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb
