module

public import CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb.SmallPattern
public import CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb.Twist

public section

namespace CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb

@[expose] def twoLabel (l : Fin 3) (A B : Finset ℕ) : Fin 3 → Finset ℕ :=
  fun s => if s = l then A else B

@[expose] def threeLabel (s l : Fin 3) (A B : Finset ℕ) : Fin 3 → Finset ℕ :=
  fun u => if u = s then A else if u = l then B else ∅

theorem twoLabel_comp_perm (l : Fin 3) (A B : Finset ℕ) (σ : Equiv.Perm (Fin 3)) :
    twoLabel l A B ∘ σ = twoLabel (σ.symm l) A B := by
  funext u
  simp only [Function.comp_apply, twoLabel, Equiv.eq_symm_apply]

theorem threeLabel_comp_perm (s l : Fin 3) (A B : Finset ℕ) (σ : Equiv.Perm (Fin 3)) :
    threeLabel s l A B ∘ σ = threeLabel (σ.symm s) (σ.symm l) A B := by
  funext u
  simp only [Function.comp_apply, threeLabel, Equiv.eq_symm_apply]

variable {n : ℕ}

theorem isLabel_twoLabel {l : Fin 3} {A B : Finset ℕ} (hA : ∀ i ∈ A, i < n)
    (hB : ∀ i ∈ B, i < n) : IsLabel n (twoLabel l A B) := by
  intro s
  unfold twoLabel
  split_ifs
  exacts [hA, hB]

theorem isLabel_threeLabel {s l : Fin 3} {A B : Finset ℕ} (hA : ∀ i ∈ A, i < n)
    (hB : ∀ i ∈ B, i < n) : IsLabel n (threeLabel s l A B) := by
  intro u
  unfold threeLabel
  split_ifs
  exacts [hA, hB, fun i hi => absurd hi (Finset.notMem_empty i)]

theorem singleton_lt {a : ℕ} (ha : a < n) : ∀ i ∈ ({a} : Finset ℕ), i < n :=
  fun i hi => (Finset.mem_singleton.mp hi) ▸ ha

theorem pair_lt {a b : ℕ} (ha : a < n) (hb : b < n) : ∀ i ∈ ({a, b} : Finset ℕ), i < n := by
  intro i hi
  rcases Finset.mem_insert.mp hi with rfl | hi
  · exact ha
  · exact (Finset.mem_singleton.mp hi) ▸ hb

theorem shift_iter_singleton {a : ℕ} (ha : a < n) (k : ℕ) :
    (shift n)^[k] {a} = {(a + k) % n} := by
  rw [shift_iterate (singleton_lt ha), Finset.image_singleton]

theorem shift_iter_empty (k : ℕ) : (shift n)^[k] ∅ = ∅ := by
  rw [shift_iterate (fun i hi => absurd hi (Finset.notMem_empty i)), Finset.image_empty]

theorem shift_iter_pair {a b : ℕ} (ha : a < n) (hb : b < n) (k : ℕ) :
    (shift n)^[k] {a, b} = {(a + k) % n, (b + k) % n} := by
  rw [shift_iterate (pair_lt ha hb), Finset.image_insert, Finset.image_singleton]

theorem shiftL_iter_twoLabel (l : Fin 3) (A B : Finset ℕ) (k : ℕ) :
    (shiftL n)^[k] (twoLabel l A B) = twoLabel l ((shift n)^[k] A) ((shift n)^[k] B) := by
  rw [shiftL_iterate]
  funext s
  simp only [twoLabel]
  split_ifs <;> rfl

theorem shiftL_iter_threeLabel (s l : Fin 3) (A B : Finset ℕ) (k : ℕ) :
    (shiftL n)^[k] (threeLabel s l A B) =
      threeLabel s l ((shift n)^[k] A) ((shift n)^[k] B) := by
  rw [shiftL_iterate]
  funext u
  simp only [threeLabel]
  split_ifs <;> simp [shift_iter_empty]

theorem shiftL_iter_slotLabel (l : Fin 3) (A : Finset ℕ) (k : ℕ) :
    (shiftL n)^[k] (slotLabel l A) = slotLabel l ((shift n)^[k] A) := by
  rw [shiftL_iterate]
  funext s
  simp only [slotLabel]
  split_ifs <;> simp [shift_iter_empty]

variable (p : (Fin 3 → Finset ℕ) → ℕ)

theorem p_shift_iter (hshift : ∀ J, IsLabel n J → p (shiftL n J) = p J) {J : Fin 3 → Finset ℕ}
    (hJ : IsLabel n J) (k : ℕ) : p ((shiftL n)^[k] J) = p J := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hJk : IsLabel n ((shiftL n)^[k] J) := by
      clear ih
      induction k with
      | zero => exact hJ
      | succ k ih' =>
        rw [Function.iterate_succ_apply']
        exact isLabel_shiftL ih'
    rw [Function.iterate_succ_apply', hshift _ hJk, ih]

theorem sum_le_of_pos (hsum : ∑ J ∈ labels n, p J * 2 ^ lsize J ≤ 8 * n)
    (S : Finset (Fin 3 → Finset ℕ)) (hS : ∀ J ∈ S, IsLabel n J ∧ 1 ≤ p J) :
    ∑ J ∈ S, 2 ^ lsize J ≤ 8 * n := by
  calc ∑ J ∈ S, 2 ^ lsize J ≤ ∑ J ∈ S, p J * 2 ^ lsize J :=
        Finset.sum_le_sum fun J hJ => Nat.le_mul_of_pos_left _ (hS J hJ).2
    _ ≤ ∑ J ∈ labels n, p J * 2 ^ lsize J :=
        Finset.sum_le_sum_of_subset fun J hJ => mem_labels.mpr (hS J hJ).1
    _ ≤ 8 * n := hsum

theorem three_mul_le_of_family (hsum : ∑ J ∈ labels n, p J * 2 ^ lsize J ≤ 8 * n)
    (L : Fin 3 × ℕ → Fin 3 → Finset ℕ) {d : ℕ}
    (hinj : Set.InjOn L ((Finset.univ ×ˢ Finset.range n : Finset (Fin 3 × ℕ)) : Set (Fin 3 × ℕ)))
    (hL : ∀ x ∈ Finset.univ ×ˢ Finset.range n, IsLabel n (L x) ∧ 1 ≤ p (L x) ∧ lsize (L x) = d) :
    3 * n * 2 ^ d ≤ 8 * n := by
  have h := sum_le_of_pos p hsum ((Finset.univ ×ˢ Finset.range n).image L) (by
    intro J hJ
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hJ
    exact ⟨(hL x hx).1, (hL x hx).2.1⟩)
  rw [Finset.sum_image hinj, Finset.sum_congr rfl fun x hx => by rw [(hL x hx).2.2],
    Finset.sum_const, Finset.card_product, Finset.card_univ, Fintype.card_fin,
    Finset.card_range, smul_eq_mul] at h
  exact h

variable {p}

section Exclusions

variable (hshift : ∀ J, IsLabel n J → p (shiftL n J) = p J)
  (hperm : ∀ J, IsLabel n J → ∀ σ : Equiv.Perm (Fin 3), p (J ∘ σ) = p J)
  (hsum : ∑ J ∈ labels n, p J * 2 ^ lsize J ≤ 8 * n)
include hshift hperm hsum

theorem p_twoLabel_perm {l l' : Fin 3} {A B : Finset ℕ} (hA : ∀ i ∈ A, i < n)
    (hB : ∀ i ∈ B, i < n) : p (twoLabel l' A B) = p (twoLabel l A B) := by
  rw [← hperm _ (isLabel_twoLabel hA hB) (Equiv.swap l l'), twoLabel_comp_perm,
    Equiv.symm_swap, Equiv.swap_apply_right]

theorem p_twoLabel_empty_zero (hn : 1 ≤ n) (l : Fin 3) : p (twoLabel l ∅ {0}) = 0 := by
  by_contra hne
  have h0 : ∀ i ∈ (∅ : Finset ℕ), i < n := fun i hi => absurd hi (Finset.notMem_empty i)
  have h := three_mul_le_of_family p hsum (fun x => twoLabel x.1 ∅ {x.2}) (d := 2) ?_ ?_
  · have : 3 * n * 4 ≤ 8 * n := h
    omega
  · rintro ⟨l₁, k₁⟩ hx ⟨l₂, k₂⟩ hy h
    simp only [Finset.coe_product, Set.mem_prod, Finset.coe_univ, Set.mem_univ, true_and,
      Finset.coe_range, Set.mem_Iio] at hx hy
    have hl : l₁ = l₂ := by
      by_contra hl
      have := congrFun h l₁
      simp only [twoLabel, if_pos rfl, if_neg hl] at this
      exact Finset.singleton_ne_empty k₂ this.symm
    subst hl
    obtain ⟨t, ht⟩ : ∃ t, t ≠ l₁ := ⟨l₁ + 1, by fin_cases l₁ <;> decide⟩
    have := congrFun h t
    simp only [twoLabel, if_neg ht] at this
    rw [Finset.singleton_injective this]
  · rintro ⟨l', k⟩ hx
    simp only [Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_range] at hx
    refine ⟨isLabel_twoLabel h0 (singleton_lt hx), ?_, ?_⟩
    · have h1 : twoLabel l' ∅ {k} = (shiftL n)^[k] (twoLabel l' ∅ {0}) := by
        rw [shiftL_iter_twoLabel, shift_iter_empty, shift_iter_singleton (by omega), zero_add,
          Nat.mod_eq_of_lt hx]
      rw [h1, p_shift_iter p hshift (isLabel_twoLabel h0 (singleton_lt (by omega))),
        p_twoLabel_perm hshift hperm hsum h0 (singleton_lt (by omega))]
      exact Nat.one_le_iff_ne_zero.mpr hne
    · obtain ⟨t, ht⟩ : ∃ t, t ≠ l' := ⟨l' + 1, by fin_cases l' <;> decide⟩
      fin_cases l' <;> simp [lsize, twoLabel]

theorem p_twoLabel_one_zero (hn : 2 ≤ n) (l : Fin 3) : p (twoLabel l {1} {0}) = 0 := by
  by_contra hne
  have h := three_mul_le_of_family p hsum
    (fun x => twoLabel x.1 {(1 + x.2) % n} {x.2}) (d := 3) ?_ ?_
  · have : 3 * n * 8 ≤ 8 * n := h
    omega
  · rintro ⟨l₁, k₁⟩ hx ⟨l₂, k₂⟩ hy h
    simp only [Finset.coe_product, Set.mem_prod, Finset.coe_univ, Set.mem_univ, true_and,
      Finset.coe_range, Set.mem_Iio] at hx hy
    obtain ⟨t, ht1, ht2⟩ : ∃ t, t ≠ l₁ ∧ t ≠ l₂ := by
      fin_cases l₁ <;> fin_cases l₂ <;> first
        | exact ⟨0, by decide, by decide⟩ | exact ⟨1, by decide, by decide⟩
        | exact ⟨2, by decide, by decide⟩
    have hk := congrFun h t
    simp only [twoLabel, if_neg ht1, if_neg ht2] at hk
    have hk' := Finset.singleton_injective hk
    subst hk'
    by_contra hne'
    have hl : l₁ ≠ l₂ := fun h' => hne' (by rw [h'])
    have := congrFun h l₁
    simp only [twoLabel, if_pos rfl, if_neg hl] at this
    have h2 := Finset.singleton_injective this
    have : (1 + k₁) % n ≠ k₁ := by
      rcases Nat.lt_or_ge (1 + k₁) n with h3 | h3
      · rw [Nat.mod_eq_of_lt h3]; omega
      · have : 1 + k₁ = n := by omega
        rw [this, Nat.mod_self]; omega
    exact this h2
  · rintro ⟨l', k⟩ hx
    simp only [Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_range] at hx
    refine ⟨isLabel_twoLabel (singleton_lt (Nat.mod_lt _ (by omega))) (singleton_lt hx), ?_, ?_⟩
    · have h1 : twoLabel l' {(1 + k) % n} {k} = (shiftL n)^[k] (twoLabel l' {1} {0}) := by
        rw [shiftL_iter_twoLabel, shift_iter_singleton (by omega),
          shift_iter_singleton (by omega), zero_add, Nat.mod_eq_of_lt hx]
      rw [h1, p_shift_iter p hshift (isLabel_twoLabel (singleton_lt (by omega))
        (singleton_lt (by omega))), p_twoLabel_perm hshift hperm hsum (singleton_lt (by omega))
        (singleton_lt (by omega))]
      exact Nat.one_le_iff_ne_zero.mpr hne
    · fin_cases l' <;> simp [lsize, twoLabel]

theorem p_twoLabel_pair_single {a : ℕ} (ha0 : 0 < a) (ha : a < n) (l : Fin 3) :
    p (twoLabel l {0, a} {a}) = 0 := by
  by_contra hne
  have hn : 0 < n := by omega
  have h := sum_le_of_pos p hsum ((Finset.range n).image fun k =>
    twoLabel l {k, (a + k) % n} {(a + k) % n}) (by
      intro J hJ
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hJ
      rw [Finset.mem_range] at hk
      refine ⟨isLabel_twoLabel (pair_lt hk (Nat.mod_lt _ hn)) (singleton_lt (Nat.mod_lt _ hn)),
        ?_⟩
      have h1 : twoLabel l {k, (a + k) % n} {(a + k) % n} =
          (shiftL n)^[k] (twoLabel l {0, a} {a}) := by
        rw [shiftL_iter_twoLabel, shift_iter_pair hn ha, shift_iter_singleton ha, zero_add,
          Nat.mod_eq_of_lt hk]
      rw [h1, p_shift_iter p hshift (isLabel_twoLabel (pair_lt hn ha) (singleton_lt ha))]
      exact Nat.one_le_iff_ne_zero.mpr hne)
  rw [Finset.sum_image] at h
  ·
    have hsz : ∀ k ∈ Finset.range n,
        lsize (twoLabel l {k, (a + k) % n} {(a + k) % n}) = 4 := by
      intro k hk
      rw [Finset.mem_range] at hk
      have hne' : k ≠ (a + k) % n := by
        intro h
        rcases Nat.lt_or_ge (a + k) n with h3 | h3
        · rw [Nat.mod_eq_of_lt h3] at h; omega
        · have : (a + k) % n = a + k - n := by
            rw [Nat.mod_eq_sub_mod h3, Nat.mod_eq_of_lt (by omega)]
          omega
      have hc : ({k, (a + k) % n} : Finset ℕ).card = 2 := Finset.card_pair hne'
      fin_cases l <;> simp [lsize, twoLabel, hc]
    rw [Finset.sum_congr rfl fun k hk => by rw [hsz k hk], Finset.sum_const,
      Finset.card_range, smul_eq_mul] at h
    have : n * 16 ≤ 8 * n := h
    omega
  · intro k₁ hk₁ k₂ hk₂ h
    simp only [Finset.coe_range, Set.mem_Iio] at hk₁ hk₂
    obtain ⟨t, ht⟩ : ∃ t, t ≠ l := ⟨l + 1, by fin_cases l <;> decide⟩
    have := congrFun h t
    simp only [twoLabel, if_neg ht] at this
    have h2 := Finset.singleton_injective this
    have : k₁ ≡ k₂ [MOD n] := Nat.ModEq.add_left_cancel' a h2
    exact Nat.ModEq.eq_of_lt_of_lt this hk₁ hk₂

theorem p_slotLabel_pair {a : ℕ} (ha0 : 0 < a) (ha : a < n) (h2a : 2 * a ≠ n) (l : Fin 3) :
    p (slotLabel l {0, a}) = 0 := by
  by_contra hne
  have hn : 0 < n := by omega
  have hmod : ∀ k < n, k ≠ (a + k) % n := by
    intro k hk h
    rcases Nat.lt_or_ge (a + k) n with h3 | h3
    · rw [Nat.mod_eq_of_lt h3] at h; omega
    · have : (a + k) % n = a + k - n := by
        rw [Nat.mod_eq_sub_mod h3, Nat.mod_eq_of_lt (by omega)]
      omega
  have h := three_mul_le_of_family p hsum (fun x => slotLabel x.1 {x.2, (a + x.2) % n})
    (d := 2) ?_ ?_
  · have : 3 * n * 4 ≤ 8 * n := h
    omega
  · rintro ⟨l₁, k₁⟩ hx ⟨l₂, k₂⟩ hy h
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
    simp only [Prod.mk.injEq, true_and]
    by_contra hk
    have hk1 : k₁ ∈ ({k₂, (a + k₂) % n} : Finset ℕ) := h' ▸ Finset.mem_insert_self _ _
    have hk2 : k₂ ∈ ({k₁, (a + k₁) % n} : Finset ℕ) := h'.symm ▸ Finset.mem_insert_self _ _
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk1 hk2
    rcases hk1 with h1 | h1
    · exact hk h1
    rcases hk2 with h2 | h2
    · exact hk h2.symm
    have e1 : k₁ ≡ a + k₂ [MOD n] := by rw [h1]; exact Nat.mod_modEq _ _
    have e2 : k₂ ≡ a + k₁ [MOD n] := by rw [h2]; exact Nat.mod_modEq _ _
    have e3 : k₁ + 0 ≡ k₁ + 2 * a [MOD n] := by
      calc k₁ + 0 = k₁ := by ring
        _ ≡ a + k₂ [MOD n] := e1
        _ ≡ a + (a + k₁) [MOD n] := Nat.ModEq.add_left a e2
        _ = k₁ + 2 * a := by ring
    have e4 : 0 ≡ 2 * a [MOD n] := Nat.ModEq.add_left_cancel' k₁ e3
    have : n ∣ 2 * a := (Nat.modEq_zero_iff_dvd.mp e4.symm)
    obtain ⟨c, hc⟩ := this
    rcases c with _ | _ | c
    · omega
    · omega
    · nlinarith
  · rintro ⟨l', k⟩ hx
    simp only [Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_range] at hx
    refine ⟨isLabel_slotLabel (pair_lt hx (Nat.mod_lt _ hn)) l', ?_, ?_⟩
    · have h1 : slotLabel l' {k, (a + k) % n} = (shiftL n)^[k] (slotLabel l' {0, a}) := by
        rw [shiftL_iter_slotLabel, shift_iter_pair hn ha, zero_add, Nat.mod_eq_of_lt hx]
      rw [h1, p_shift_iter p hshift (isLabel_slotLabel (pair_lt hn ha) l'),
        ← slotLabel_comp_swap l l', hperm _ (isLabel_slotLabel (pair_lt hn ha) l)]
      exact Nat.one_le_iff_ne_zero.mpr hne
    · have hc : ({k, (a + k) % n} : Finset ℕ).card = 2 := Finset.card_pair (hmod k hx)
      fin_cases l' <;> simp [lsize, slotLabel, hc]

theorem p_threeLabel {a : ℕ} (ha : a < n) {s l : Fin 3} (hsl : s ≠ l) :
    p (threeLabel s l {a} {0}) = 0 := by
  by_contra hne
  have hn : 0 < n := by omega
  have htrans₀ : ∀ s l s' l' : Fin 3, s ≠ l → s' ≠ l' →
      ∃ σ : Equiv.Perm (Fin 3), σ s' = s ∧ σ l' = l := by decide
  have htrans := fun s' l' (h : s' ≠ l') => htrans₀ s l s' l' hsl h
  have hpos : ∀ j : Fin 3, 1 ≤ p (threeLabel (j + 1) j {a} {0}) := by
    intro j
    obtain ⟨σ, h1, h2⟩ := htrans (j + 1) j (by fin_cases j <;> decide)
    have : threeLabel (j + 1) j {a} {0} = threeLabel s l {a} {0} ∘ σ := by
      rw [threeLabel_comp_perm, (Equiv.symm_apply_eq σ).mpr h1.symm,
        (Equiv.symm_apply_eq σ).mpr h2.symm]
    rw [this, hperm _ (isLabel_threeLabel (singleton_lt ha) (singleton_lt hn))]
    exact Nat.one_le_iff_ne_zero.mpr hne
  have h := three_mul_le_of_family p hsum
    (fun x => threeLabel (x.1 + 1) x.1 {(a + x.2) % n} {x.2}) (d := 2) ?_ ?_
  · have : 3 * n * 4 ≤ 8 * n := h
    omega
  · rintro ⟨j₁, k₁⟩ hx ⟨j₂, k₂⟩ hy h
    simp only [Finset.coe_product, Set.mem_prod, Finset.coe_univ, Set.mem_univ, true_and,
      Finset.coe_range, Set.mem_Iio] at hx hy
    have hj : j₁ = j₂ := by
      have h1 := congrFun h (j₁ + 2)
      simp only [threeLabel] at h1
      fin_cases j₁ <;> fin_cases j₂ <;> simp_all
    subst hj
    have h1 := congrFun h j₁
    simp only [threeLabel] at h1
    fin_cases j₁ <;> simp_all
  · rintro ⟨j, k⟩ hx
    simp only [Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_range] at hx
    refine ⟨isLabel_threeLabel (singleton_lt (Nat.mod_lt _ hn)) (singleton_lt hx), ?_, ?_⟩
    · have h1 : threeLabel (j + 1) j {(a + k) % n} {k} =
          (shiftL n)^[k] (threeLabel (j + 1) j {a} {0}) := by
        rw [shiftL_iter_threeLabel, shift_iter_singleton ha, shift_iter_singleton hn, zero_add,
          Nat.mod_eq_of_lt hx]
      rw [h1, p_shift_iter p hshift (isLabel_threeLabel (singleton_lt ha) (singleton_lt hn))]
      exact hpos j
    · fin_cases j <;> simp [lsize, threeLabel]

end Exclusions

end CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb
