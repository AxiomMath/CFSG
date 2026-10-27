module

public import CFSG.Sporadic.HNSchreier.MaskCheck
public import CFSG.Sporadic.HN.Local.Partitions
public import CFSG.Sporadic.HN.F5Simple
public import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.Sporadic.HNSchreier

open CFSG.Sporadic.HNSchreier.Native CFSG.Sporadic.HN.Local Finset

@[expose] def maskSet12 (m : ℕ) : Finset (Fin 12) := univ.filter fun i => m.testBit i.val

theorem mem_maskSet12 {m : ℕ} {i : Fin 12} : i ∈ maskSet12 m ↔ m.testBit i.val = true := by
  simp [maskSet12]

theorem testBit_one_shiftLeft (s i : ℕ) : (1 <<< s).testBit i = decide (i = s) := by
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow]
  by_cases h : i = s
  · subst h; simp
  · simp [h, Ne.symm h]

theorem testBit_maskOfList (l : List ℕ) (i : ℕ) : (maskOfList l).testBit i = decide (i ∈ l) := by
  have key : ∀ (l : List ℕ) (m : ℕ), (l.foldl (fun m s => m ||| (1 <<< s)) m).testBit i =
      (m.testBit i || decide (i ∈ l)) := by
    intro l
    induction l with
    | nil => intro m; simp
    | cons s l ih =>
      intro m
      rw [List.foldl_cons, ih, Nat.testBit_or, testBit_one_shiftLeft]
      by_cases h1 : i = s <;> by_cases h2 : i ∈ l <;> simp [h1, h2]
  rw [maskOfList, key]
  simp

theorem testBit_permMask (p : Array ℕ) (m j : ℕ) :
    (permMask p m).testBit j = true ↔ ∃ i < 12, m.testBit i = true ∧ p[i]! = j := by
  have key : ∀ (l : List ℕ) (acc : ℕ), (l.foldl (fun acc i => if m.testBit i then
      acc ||| (1 <<< p[i]!) else acc) acc).testBit j = true ↔
        acc.testBit j = true ∨ ∃ i ∈ l, m.testBit i = true ∧ p[i]! = j := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons a l ih =>
      intro acc
      rw [List.foldl_cons, ih]
      by_cases ha : m.testBit a = true
      · rw [ite_eq_left ha, Nat.testBit_or, testBit_one_shiftLeft]
        constructor
        · rintro (h | h)
          · rcases Bool.or_eq_true_iff.1 h with h | h
            · exact Or.inl h
            · right; exact ⟨a, List.mem_cons_self .., ha, (of_decide_eq_true h).symm⟩
          · obtain ⟨i, hi, h1, h2⟩ := h
            right; exact ⟨i, List.mem_cons_of_mem _ hi, h1, h2⟩
        · rintro (h | ⟨i, hi, h1, h2⟩)
          · left; simp [h]
          · rcases List.mem_cons.1 hi with rfl | hi
            · left; simp [h2]
            · right; exact ⟨i, hi, h1, h2⟩
      · rw [ite_eq_right ha]
        constructor
        · rintro (h | ⟨i, hi, h1, h2⟩)
          · exact Or.inl h
          · right; exact ⟨i, List.mem_cons_of_mem _ hi, h1, h2⟩
        · rintro (h | ⟨i, hi, h1, h2⟩)
          · exact Or.inl h
          · rcases List.mem_cons.1 hi with rfl | hi
            · exact absurd h1 ha
            · right; exact ⟨i, hi, h1, h2⟩
  rw [permMask, key]
  simp

theorem maskSet12_permMask {p : Array ℕ} {σ : Equiv.Perm (Fin 12)}
    (hp : ∀ i : Fin 12, p[i.val]! = (σ i).val) (m : ℕ) :
    maskSet12 (permMask p m) = (maskSet12 m).map σ.toEmbedding := by
  ext j
  rw [mem_maskSet12, testBit_permMask, Finset.mem_map]
  constructor
  · rintro ⟨i, hi, h1, h2⟩
    refine ⟨⟨i, hi⟩, mem_maskSet12.2 h1, Fin.ext ?_⟩
    rw [Equiv.coe_toEmbedding, ← hp ⟨i, hi⟩]
    exact h2
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i.val, i.isLt, mem_maskSet12.1 hi, hp i⟩

theorem testBit_xor_4095 {m i : ℕ} (hi : i < 12) : (4095 ^^^ m).testBit i = !m.testBit i := by
  rw [Nat.testBit_xor]
  have : (4095 : ℕ).testBit i = true := by
    rw [show (4095 : ℕ) = 2 ^ 12 - 1 by norm_num, Nat.testBit_two_pow_sub_one]
    simpa using hi
  rw [this]
  simp

theorem maskSet12_canonMask (m : ℕ) : maskSet12 (canonMask m) = canon (maskSet12 m) := by
  unfold canonMask canon
  by_cases h0 : m.testBit 0 = true
  · rw [ite_eq_left h0, ite_eq_left (mem_maskSet12.2 h0)]
  · rw [ite_eq_right h0, ite_eq_right (fun h => h0 (mem_maskSet12.1 h))]
    ext i
    rw [mem_maskSet12, testBit_xor_4095 i.isLt, Finset.mem_compl, mem_maskSet12]
    simp

theorem card_maskSet12 (m : ℕ) : (maskSet12 m).card = popc12 m := by
  rw [popc12, CFSG.Sporadic.F5.fold_ite_add_eq_sum (fun i => m.testBit i = true) (fun _ => 1),
    maskSet12, Finset.card_filter, ← Fin.sum_univ_eq_sum_range]

end CFSG.Sporadic.HNSchreier
