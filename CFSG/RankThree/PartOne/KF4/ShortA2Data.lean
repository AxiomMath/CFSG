module

public import CFSG.RankThree.PartOne.KF4.StrNativeBruhat
public import CFSG.RankThree.PartOne.KF4.Strings

public section

namespace CFSG.RankThree.PartOne.KF4

open CFSG.Blueprint.Chevalley

@[expose] def f4ShortSupport : Set (Fin Tag.F4.rank) := {f4Index 2, f4Index 3}

@[expose] def f4ShortWeight : Fin 6 → Fin Tag.F4.rank → ℤ :=
  (![![0, 1, 2, 2], ![0, 1, 2, 1], ![0, 1, 1, 1], ![0, 1, 2, 0], ![0, 1, 1, 0],
    ![0, 1, 0, 0]] : Fin 6 → Fin 4 → ℤ)

theorem mem_f4ShortSupport (i : Fin Tag.F4.rank) :
    i ∈ f4ShortSupport ↔ i = f4Index 2 ∨ i = f4Index 3 := by
  simp only [f4ShortSupport, Set.mem_insert_iff, Set.mem_singleton_iff]

section Data

private theorem short_roots_dec : ∀ k : Fin 6, f4IsRootB (f4ShortWeight k) = true := by
  decide +kernel

private theorem short_inj : Function.Injective f4ShortWeight := by
  intro k k' h
  revert k k'
  decide +kernel

private theorem short_ne_single : ∀ k : Fin 6, ∀ i : Fin Tag.F4.rank,
    (i = f4Index 2 ∨ i = f4Index 3) →
      f4ShortWeight k ≠ Pi.single i 1 ∧ f4ShortWeight k ≠ -Pi.single i 1 := by
  decide +kernel

private theorem short_up_dec : ∀ k : Fin 6, ∀ i : Fin Tag.F4.rank,
    (i = f4Index 2 ∨ i = f4Index 3) → ∀ j : Fin 4, (j : ℕ) ≤ f4StrUp i (f4ShortWeight k) →
      ∃ k', f4ShortWeight k' = f4ShortWeight k + ((j : ℕ) : ℤ) • Pi.single i 1 := by
  decide +kernel

private theorem short_down_dec : ∀ k : Fin 6, ∀ i : Fin Tag.F4.rank,
    (i = f4Index 2 ∨ i = f4Index 3) → ∀ j : Fin 4, (j : ℕ) ≤ f4StrDown i (f4ShortWeight k) →
      ∃ k', f4ShortWeight k' = f4ShortWeight k - ((j : ℕ) : ℤ) • Pi.single i 1 := by
  decide +kernel

private theorem f4StrUp_le (i : Fin Tag.F4.rank) (v : Fin Tag.F4.rank → ℤ) : f4StrUp i v ≤ 3 := by
  unfold f4StrUp
  split_ifs <;> omega

private theorem f4StrDown_le (i : Fin Tag.F4.rank) (v : Fin Tag.F4.rank → ℤ) :
    f4StrDown i v ≤ 3 := by
  unfold f4StrDown
  split_ifs <;> omega


theorem f4Short_data : StrNativeData Tag.F4 6 f4ShortSupport f4ShortWeight where
  isRoot k := isRoot_iff_f4IsRootB.2 (short_roots_dec k)
  injective := short_inj
  ne_single k i hi := short_ne_single k i ((mem_f4ShortSupport i).1 hi)
  up_mem k i hi j hj := by
    obtain ⟨h1, -⟩ := stringUp_down_F4 i (isRoot_iff_f4IsRootB.2 (short_roots_dec k))
      (short_ne_single k i ((mem_f4ShortSupport i).1 hi)).1
      (short_ne_single k i ((mem_f4ShortSupport i).1 hi)).2
    rw [h1] at hj
    have hj3 : j < 4 := Nat.lt_succ_of_le (hj.trans (f4StrUp_le _ _))
    exact short_up_dec k i ((mem_f4ShortSupport i).1 hi) ⟨j, hj3⟩ hj
  down_mem k i hi j hj := by
    obtain ⟨-, h2⟩ := stringUp_down_F4 i (isRoot_iff_f4IsRootB.2 (short_roots_dec k))
      (short_ne_single k i ((mem_f4ShortSupport i).1 hi)).1
      (short_ne_single k i ((mem_f4ShortSupport i).1 hi)).2
    rw [h2] at hj
    have hj3 : j < 4 := Nat.lt_succ_of_le (hj.trans (f4StrDown_le _ _))
    exact short_down_dec k i ((mem_f4ShortSupport i).1 hi) ⟨j, hj3⟩ hj

end Data

@[expose] def f4ShortU : Fin 3 → Fin Tag.F4.rank → ℤ :=
  ![0, Pi.single (f4Index 2) 1, Pi.single (f4Index 2) 1 + Pi.single (f4Index 3) 1]

@[expose] def f4ShortSigma (i j : Fin 3) : Fin Tag.F4.rank → ℤ := f4ShortU i - f4ShortU j

theorem f4ShortSigma_values :
    f4ShortSigma 1 0 = Pi.single (f4Index 2) 1 ∧ f4ShortSigma 2 1 = Pi.single (f4Index 3) 1 ∧
    f4ShortSigma 0 1 = -Pi.single (f4Index 2) 1 ∧ f4ShortSigma 1 2 = -Pi.single (f4Index 3) 1 := by
  decide +kernel

theorem f4ShortSigma_add (i j k : Fin 3) :
    f4ShortSigma i j + f4ShortSigma j k = f4ShortSigma i k := by
  unfold f4ShortSigma
  abel

theorem f4ShortSigma_neg (i j : Fin 3) : f4ShortSigma j i = -f4ShortSigma i j := by
  unfold f4ShortSigma
  abel

theorem f4ShortSigma_mem : ∀ k l : Fin 3, k ≠ l → ∃ m : Fin 48,
    f4RootVec m = f4ShortSigma k l ∧
      ∀ i : Fin Tag.F4.rank, ¬(i = f4Index 2 ∨ i = f4Index 3) → f4RootVec m i = 0 := by
  decide +kernel

theorem exists_f4ShortSigma_of_support : ∀ m : Fin 48,
    (∀ i : Fin Tag.F4.rank, ¬(i = f4Index 2 ∨ i = f4Index 3) → f4RootVec m i = 0) →
      ∃ k l : Fin 3, k ≠ l ∧ f4ShortSigma k l = f4RootVec m := by
  decide +kernel

@[expose] def f4ShortPosRoot : Fin 3 → Fin Tag.F4.rank → ℤ :=
  ![f4ShortSigma 1 0, f4ShortSigma 2 1, f4ShortSigma 2 0]

theorem f4ShortPosRoot_injective : Function.Injective f4ShortPosRoot := by
  intro k k' h
  revert k k'
  decide +kernel

theorem f4ShortSigma_height_pos : ∀ k l : Fin 3, k ≠ l →
    (0 < height (f4ShortSigma k l) ↔ l < k) := by
  decide +kernel

theorem exists_f4ShortPosRoot : ∀ k l : Fin 3, l < k →
    ∃ m, f4ShortPosRoot m = f4ShortSigma k l := by
  decide +kernel

theorem exists_sigma_of_f4ShortPosRoot : ∀ m : Fin 3, ∃ k l : Fin 3, l < k ∧
    f4ShortPosRoot m = f4ShortSigma k l := by
  decide +kernel

theorem f4Short_pairing : ∀ k : Fin 6,
    (∑ j, Tag.F4.cartan (f4Index 2) j * f4ShortWeight k j) =
      (![0, 1, -1, 2, 0, -2] : Fin 6 → ℤ) k ∧
    (∑ j, Tag.F4.cartan (f4Index 3) j * f4ShortWeight k j) =
      (![2, 0, 1, -2, -1, 0] : Fin 6 → ℤ) k := by
  decide +kernel

theorem f4ShortSigma_reflect :
    reflect Tag.F4 (f4Index 2) (f4ShortSigma 2 1) = f4ShortSigma 2 0 ∧
    reflect Tag.F4 (f4Index 2) (f4ShortSigma 1 2) = f4ShortSigma 0 2 := by
  decide +kernel

theorem f4Short_height_of_lt : ∀ i j : Fin 6, i < j →
    height (f4ShortWeight j) < height (f4ShortWeight i) ∨
      (height (f4ShortWeight i) = height (f4ShortWeight j) ∧ i = 2 ∧ j = 3) := by
  decide +kernel

theorem f4Short_lt_of_height : ∀ i j : Fin 6, height (f4ShortWeight j) < height (f4ShortWeight i) →
    i < j := by
  decide +kernel

theorem f4Short_height_eq : ∀ i j : Fin 6, height (f4ShortWeight i) = height (f4ShortWeight j) →
    (i = j ∨ (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2)) := by
  decide +kernel

theorem f4Short_lex : toLex (f4ShortWeight 2) < toLex (f4ShortWeight 3) := by
  refine ⟨f4Index 2, fun j (hj : j < f4Index 2) => ?_, by decide⟩
  have hj' : j = f4Index 0 ∨ j = f4Index 1 := by
    revert hj
    revert j
    decide +kernel
  rcases hj' with rfl | rfl
  · show f4ShortWeight 2 (f4Index 0) = f4ShortWeight 3 (f4Index 0)
    decide +kernel
  · show f4ShortWeight 2 (f4Index 1) = f4ShortWeight 3 (f4Index 1)
    decide +kernel

theorem f4Short_not_lex : ¬toLex (f4ShortWeight 3) < toLex (f4ShortWeight 2) := fun h =>
  (lt_asymm h) f4Short_lex

theorem f4Short_order (i j : Fin 6) :
    (height (f4ShortWeight j) < height (f4ShortWeight i) ∨
      (height (f4ShortWeight i) = height (f4ShortWeight j) ∧
        toLex (f4ShortWeight i) < toLex (f4ShortWeight j))) ↔ i < j := by
  constructor
  · rintro (h | ⟨h, hlt⟩)
    · exact f4Short_lt_of_height i j h
    · rcases f4Short_height_eq i j h with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact absurd hlt (lt_irrefl _)
      · decide
      · exact absurd hlt f4Short_not_lex
  · intro h
    rcases f4Short_height_of_lt i j h with h1 | ⟨h1, rfl, rfl⟩
    · exact Or.inl h1
    · exact Or.inr ⟨h1, f4Short_lex⟩

theorem f4Short_outside : ∀ k : Fin 6, ∀ i : Fin Tag.F4.rank,
    ¬(i = f4Index 2 ∨ i = f4Index 3) → f4ShortWeight k i = f4ShortWeight 0 i := by
  decide +kernel

theorem f4Short_perm_closed : ∀ m : Fin 48,
    (∀ i : Fin Tag.F4.rank, ¬(i = f4Index 2 ∨ i = f4Index 3) →
      f4RootVec m i = f4ShortWeight 0 i) → ∃ k, f4ShortWeight k = f4RootVec m := by
  decide +kernel

theorem f4Short_single_eq_sub :
    (Pi.single (f4Index 2) 1 : Fin Tag.F4.rank → ℤ) = f4ShortWeight 4 - f4ShortWeight 5 ∧
    (Pi.single (f4Index 3) 1 : Fin Tag.F4.rank → ℤ) = f4ShortWeight 2 - f4ShortWeight 4 := by
  decide +kernel


theorem f4Short_bruhat : StrNativeBruhat f4Short_data 0 where
  precedes i j := by
    simp only [Label.Precedes, Label.weight]
    exact f4Short_order i j
  outside k i hi := f4Short_outside k i (by rwa [← mem_f4ShortSupport])
  perm_closed β hβ hout := by
    obtain ⟨m, rfl⟩ := isRoot_iff_exists_f4RootVec.1 hβ
    exact f4Short_perm_closed m fun i hi => hout i (fun h => hi ((mem_f4ShortSupport i).1 h))
  single_eq_sub i hi := by
    rcases (mem_f4ShortSupport i).1 hi with rfl | rfl
    · exact ⟨4, 5, f4Short_single_eq_sub.1⟩
    · exact ⟨2, 4, f4Short_single_eq_sub.2⟩

end CFSG.RankThree.PartOne.KF4
