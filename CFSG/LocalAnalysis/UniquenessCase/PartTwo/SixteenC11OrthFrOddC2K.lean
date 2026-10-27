module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11OrthFrOddC1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

@[expose] def s16c11_frK_pairKey (t : ℕ × ℕ × ℕ) : ℕ := t.1 * 256 + t.2.1

@[expose] def s16c11_frK_mask (L : List (ℕ × ℕ × ℕ)) : ℕ :=
  L.foldr (fun t acc => acc ||| (1 <<< s16c11_frK_pairKey t)) 0

theorem s16c11_frK_mem_of_mask : ∀ (L : List (ℕ × ℕ × ℕ)) (x : ℕ),
    Nat.testBit (s16c11_frK_mask L) x = true → ∃ t ∈ L, s16c11_frK_pairKey t = x
  | [], x, h => by simp [s16c11_frK_mask] at h
  | t :: L, x, h => by
    rw [s16c11_frK_mask, List.foldr_cons, Nat.testBit_or, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨s, hs, hk⟩ := s16c11_frK_mem_of_mask L x h
      exact ⟨s, List.mem_cons_of_mem _ hs, hk⟩
    · rw [Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_eq] at h
      exact ⟨t, List.mem_cons_self .., h⟩

@[expose] def s16c11_frK_tripsOK (L : List (ℕ × ℕ × ℕ)) : Bool :=
  L.all fun t => decide (t.1 < 256) && decide (t.2.1 < 256) && (t.2.2 == t.1 ^^^ t.2.1)

theorem s16c11_frK_trips4_ok : s16c11_frK_tripsOK s16c11_fr_trips4 = true := by
  decide +kernel

theorem s16c11_frK_sort3_xor (i j : ℕ) :
    (s16c11_fr_sort3 i j (i ^^^ j)).2.2 =
      (s16c11_fr_sort3 i j (i ^^^ j)).1 ^^^ (s16c11_fr_sort3 i j (i ^^^ j)).2.1 := by
  unfold s16c11_fr_sort3
  split_ifs <;> simp [Nat.xor_comm, Nat.xor_left_comm]

theorem s16c11_frK_sort3_lt (i j : ℕ) (hi : i < 256) (hj : j < 256) :
    (s16c11_fr_sort3 i j (i ^^^ j)).1 < 256 ∧ (s16c11_fr_sort3 i j (i ^^^ j)).2.1 < 256 ∧
      (s16c11_fr_sort3 i j (i ^^^ j)).2.2 < 256 := by
  have hx : i ^^^ j < 256 := by simpa using Nat.xor_lt_two_pow (n := 8) hi hj
  unfold s16c11_fr_sort3
  split_ifs <;> dsimp only <;> omega

theorem s16c11_frK_mem_of_bit (L : List (ℕ × ℕ × ℕ)) (hL : s16c11_frK_tripsOK L = true)
    (i j : ℕ) (hi : i < 256) (hj : j < 256)
    (h : Nat.testBit (s16c11_frK_mask L) (s16c11_frK_pairKey (s16c11_fr_sort3 i j (i ^^^ j))) =
      true) :
    s16c11_fr_sort3 i j (i ^^^ j) ∈ L := by
  obtain ⟨s, hs, hk⟩ := s16c11_frK_mem_of_mask L _ h
  have hs' := List.all_eq_true.mp hL s hs
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hs'
  obtain ⟨⟨hs1, hs2⟩, hs3⟩ := hs'
  obtain ⟨ht1, ht2, -⟩ := s16c11_frK_sort3_lt i j hi hj
  have ht3 := s16c11_frK_sort3_xor i j
  generalize s16c11_fr_sort3 i j (i ^^^ j) = t at hk ht1 ht2 ht3 ⊢
  unfold s16c11_frK_pairKey at hk
  have h1 : s.1 = t.1 := by omega
  have h2 : s.2.1 = t.2.1 := by omega
  have hst : s = t := Prod.ext h1 (Prod.ext h2 (by rw [hs3, ht3, h1, h2]))
  rw [← hst]
  exact hs

@[expose] def s16c11_frK_QZ : ℕ :=
  67953565749761120248435550487069634947959270224255042829060734908722712892927

@[expose] def s16c11_frK_valid (i j : ℕ) : Bool :=
  decide (i ≠ 0) && decide (j ≠ 0) && decide (i ^^^ j ≠ 0) &&
    Nat.testBit s16c11_frK_QZ i && Nat.testBit s16c11_frK_QZ j &&
    Nat.testBit s16c11_frK_QZ (i ^^^ j)

@[expose] def s16c11_frK_allRows (M : ℕ) : Bool :=
  (List.range 256).all fun i => (List.range 256).all fun j =>
    !s16c11_frK_valid i j || Nat.testBit M (s16c11_frK_pairKey (s16c11_fr_sort3 i j (i ^^^ j)))

theorem s16c11_frK_allRows_ok :
    s16c11_frK_allRows (s16c11_frK_mask s16c11_fr_trips4) = true := by
  decide +kernel

theorem s16c11_frK_row (V : ℕ → ℕ → Bool) (hV : V = s16c11_frK_valid)
    (mem : ℕ × ℕ × ℕ → Bool) (hmem : ∀ t ∈ s16c11_fr_trips4, mem t = true) (i : ℕ)
    (hi : i < 256) :
    (List.range 256).all (fun j => !V i j || mem (s16c11_fr_sort3 i j (i ^^^ j))) = true := by
  subst hV
  have hrow := List.all_eq_true.mp s16c11_frK_allRows_ok i (List.mem_range.mpr hi)
  rw [List.all_eq_true] at hrow ⊢
  intro j hj
  have hj' := hrow j hj
  cases hv : s16c11_frK_valid i j
  · rfl
  · rw [hv, Bool.not_true, Bool.false_or] at hj'
    rw [Bool.not_true, Bool.false_or]
    exact hmem _ (s16c11_frK_mem_of_bit _ s16c11_frK_trips4_ok i j hi
      (List.mem_range.mp hj) hj')

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
