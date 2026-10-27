module

public import CFSG.RankThree.PartOne.KF4.MinNativeBruhat

public section

namespace CFSG.RankThree.PartOne.KF4

open CFSG.Blueprint.Chevalley
open CFSG.RankThree.E6 (chainRoot)

@[expose] def f4LongSupport : Set (Fin Tag.F4.rank) := {f4Index 0, f4Index 1}

@[expose] def f4LongWeight : Fin 3 → Fin Tag.F4.rank → ℤ :=
  (![![1, 1, 1, 0], ![0, 1, 1, 0], ![0, 0, 1, 0]] : Fin 3 → Fin 4 → ℤ)

theorem mem_f4LongSupport (i : Fin Tag.F4.rank) :
    i ∈ f4LongSupport ↔ i = f4Index 0 ∨ i = f4Index 1 := by
  simp only [f4LongSupport, Set.mem_insert_iff, Set.mem_singleton_iff]

section Data

private theorem long_data_dec : ∀ k : Fin 3, ∀ i : Fin Tag.F4.rank,
    (i = f4Index 0 ∨ i = f4Index 1) →
    (f4LongWeight k ≠ Pi.single i 1 ∧ f4LongWeight k ≠ -Pi.single i 1) ∧
    ¬(f4IsRootB (f4LongWeight k + Pi.single i 1) = true ∧
      f4IsRootB (f4LongWeight k - Pi.single i 1) = true) ∧
    f4IsRootB (f4LongWeight k + (2 : ℤ) • Pi.single i 1) = false ∧
    f4IsRootB (f4LongWeight k - (2 : ℤ) • Pi.single i 1) = false ∧
    (f4IsRootB (f4LongWeight k + Pi.single i 1) = true →
      ∃ k', f4LongWeight k' = f4LongWeight k + Pi.single i 1) ∧
    (f4IsRootB (f4LongWeight k - Pi.single i 1) = true →
      ∃ k', f4LongWeight k' = f4LongWeight k - Pi.single i 1) := by
  decide +kernel

private theorem long_roots_dec : ∀ k : Fin 3, f4IsRootB (f4LongWeight k) = true := by
  decide +kernel

private theorem long_inj : Function.Injective f4LongWeight := by
  intro k k' h
  revert k k'
  decide +kernel

theorem f4Long_height : ∀ i j : Fin 3,
    (height (f4LongWeight j) < height (f4LongWeight i) ↔ i < j) ∧
      (height (f4LongWeight i) = height (f4LongWeight j) ↔ i = j) := by
  decide +kernel

theorem f4Long_outside : ∀ k : Fin 3, ∀ i : Fin Tag.F4.rank,
    ¬(i = f4Index 0 ∨ i = f4Index 1) → f4LongWeight k i = f4LongWeight 0 i := by
  decide +kernel

theorem f4Long_perm_closed : ∀ m : Fin 48,
    (∀ i : Fin Tag.F4.rank, ¬(i = f4Index 0 ∨ i = f4Index 1) →
      f4RootVec m i = f4LongWeight 0 i) → ∃ k, f4LongWeight k = f4RootVec m := by
  decide +kernel

theorem f4Long_single_eq_sub :
    (Pi.single (f4Index 0) 1 : Fin Tag.F4.rank → ℤ) = f4LongWeight 0 - f4LongWeight 1 ∧
    (Pi.single (f4Index 1) 1 : Fin Tag.F4.rank → ℤ) = f4LongWeight 1 - f4LongWeight 2 := by
  decide +kernel

theorem f4Long_pairing : ∀ k : Fin 3,
    (∑ j, Tag.F4.cartan (f4Index 0) j * f4LongWeight k j) = (![1, -1, 0] : Fin 3 → ℤ) k ∧
    (∑ j, Tag.F4.cartan (f4Index 1) j * f4LongWeight k j) = (![0, 1, -1] : Fin 3 → ℤ) k := by
  decide +kernel

theorem f4Long_steps :
    (∀ i j : Fin 3, f4LongWeight j + Pi.single (f4Index 0) 1 = f4LongWeight i ↔ (i = 0 ∧ j = 1)) ∧
    (∀ i j : Fin 3, f4LongWeight j - Pi.single (f4Index 0) 1 = f4LongWeight i ↔ (i = 1 ∧ j = 0)) ∧
    (∀ i j : Fin 3, f4LongWeight j + Pi.single (f4Index 1) 1 = f4LongWeight i ↔ (i = 1 ∧ j = 2)) ∧
    (∀ i j : Fin 3,
      f4LongWeight j - Pi.single (f4Index 1) 1 = f4LongWeight i ↔ (i = 2 ∧ j = 1)) := by
  decide +kernel

@[expose] def f4chainLong : Fin 2 → Fin Tag.F4.rank := ![f4Index 0, f4Index 1]

theorem f4chainLong_values :
    chainRoot f4chainLong 0 1 = Pi.single (f4Index 0) 1 ∧
    chainRoot f4chainLong 1 2 = Pi.single (f4Index 1) 1 ∧
    chainRoot f4chainLong 1 0 = -Pi.single (f4Index 0) 1 ∧
    chainRoot f4chainLong 2 1 = -Pi.single (f4Index 1) 1 := by
  decide +kernel

theorem f4chainLong_eq_sub :
    ∀ i j : Fin 3, chainRoot f4chainLong i j = f4LongWeight i - f4LongWeight j := by
  decide +kernel

theorem f4chainLong_mem : ∀ k l : Fin 3, k ≠ l → ∃ m : Fin 48,
    f4RootVec m = chainRoot f4chainLong k l ∧
      ∀ i : Fin Tag.F4.rank, ¬(i = f4Index 0 ∨ i = f4Index 1) → f4RootVec m i = 0 := by
  decide +kernel

theorem exists_f4chainLong_of_support : ∀ m : Fin 48,
    (∀ i : Fin Tag.F4.rank, ¬(i = f4Index 0 ∨ i = f4Index 1) → f4RootVec m i = 0) →
      ∃ k l : Fin 3, k ≠ l ∧ chainRoot f4chainLong k l = f4RootVec m := by
  decide +kernel

@[expose] def f4LongPosRoot : Fin 3 → Fin Tag.F4.rank → ℤ :=
  ![chainRoot f4chainLong 1 2, chainRoot f4chainLong 0 1, chainRoot f4chainLong 0 2]

theorem f4LongPosRoot_injective : Function.Injective f4LongPosRoot := by
  intro k k' h
  revert k k'
  decide +kernel

theorem f4chainLong_height_pos : ∀ k l : Fin 3, k ≠ l →
    (0 < height (chainRoot f4chainLong k l) ↔ k < l) := by
  decide +kernel

theorem exists_f4LongPosRoot : ∀ k l : Fin 3, k < l →
    ∃ m, f4LongPosRoot m = chainRoot f4chainLong k l := by
  decide +kernel

theorem exists_chain_of_f4LongPosRoot : ∀ m : Fin 3, ∃ k l : Fin 3, k < l ∧
    f4LongPosRoot m = chainRoot f4chainLong k l := by
  decide +kernel

theorem f4chainLong_add :
    ∀ i j k : Fin 3, chainRoot f4chainLong i j + chainRoot f4chainLong j k =
      chainRoot f4chainLong i k := by
  decide +kernel

theorem f4chainLong_neg :
    ∀ i j : Fin 3, chainRoot f4chainLong j i = -chainRoot f4chainLong i j := by
  decide +kernel

theorem f4chainLong_sums :
    (chainRoot f4chainLong 0 1 + chainRoot f4chainLong 1 2 = chainRoot f4chainLong 0 2) ∧
    (chainRoot f4chainLong 2 1 + chainRoot f4chainLong 1 0 = chainRoot f4chainLong 2 0) := by
  decide +kernel


theorem f4Long_data : MinNativeData Tag.F4 3 f4LongSupport f4LongWeight where
  isRoot k := isRoot_iff_f4IsRootB.2 (long_roots_dec k)
  injective := long_inj
  ne_single k i hi := (long_data_dec k i ((mem_f4LongSupport i).1 hi)).1
  not_both k i hi := by
    have h := (long_data_dec k i ((mem_f4LongSupport i).1 hi)).2.1
    rwa [isRoot_iff_f4IsRootB, isRoot_iff_f4IsRootB]
  no_two_up k i hi := by
    have h := (long_data_dec k i ((mem_f4LongSupport i).1 hi)).2.2.1
    rw [isRoot_iff_f4IsRootB, h]
    exact Bool.false_ne_true
  no_two_down k i hi := by
    have h := (long_data_dec k i ((mem_f4LongSupport i).1 hi)).2.2.2.1
    rw [isRoot_iff_f4IsRootB, h]
    exact Bool.false_ne_true
  up_mem k i hi hr := (long_data_dec k i ((mem_f4LongSupport i).1 hi)).2.2.2.2.1
    (isRoot_iff_f4IsRootB.1 hr)
  down_mem k i hi hr := (long_data_dec k i ((mem_f4LongSupport i).1 hi)).2.2.2.2.2
    (isRoot_iff_f4IsRootB.1 hr)

theorem f4Long_bruhat : MinNativeBruhat f4Long_data 0 where
  precedes i j := by
    simp only [Label.Precedes, Label.weight]
    constructor
    · rintro (h | ⟨h, h'⟩)
      · exact ((f4Long_height i j).1).1 h
      · obtain rfl := ((f4Long_height i j).2).1 h
        exact absurd h' (lt_irrefl _)
    · intro h
      exact Or.inl (((f4Long_height i j).1).2 h)
  outside k i hi := f4Long_outside k i (by rwa [← mem_f4LongSupport])
  perm_closed β hβ hout := by
    obtain ⟨m, rfl⟩ := isRoot_iff_exists_f4RootVec.1 hβ
    exact f4Long_perm_closed m fun i hi => hout i (fun h => hi ((mem_f4LongSupport i).1 h))
  single_eq_sub i hi := by
    rcases (mem_f4LongSupport i).1 hi with rfl | rfl
    · exact ⟨0, 1, f4Long_single_eq_sub.1⟩
    · exact ⟨1, 2, f4Long_single_eq_sub.2⟩

end Data

end CFSG.RankThree.PartOne.KF4
