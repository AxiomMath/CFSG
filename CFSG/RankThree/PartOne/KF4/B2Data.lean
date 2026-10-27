module

public import CFSG.RankThree.PartOne.KF4.MinNativeBruhat

public section

namespace CFSG.RankThree.PartOne.KF4

open CFSG.Blueprint.Chevalley

@[expose] def f4B2Support : Set (Fin Tag.F4.rank) := {f4Index 1, f4Index 2}

@[expose] def f4B2Weight : Fin 4 → Fin Tag.F4.rank → ℤ :=
  (![![0, 1, 2, 1], ![0, 1, 1, 1], ![0, 0, 1, 1], ![0, 0, 0, 1]] : Fin 4 → Fin 4 → ℤ)

theorem mem_f4B2Support (i : Fin Tag.F4.rank) :
    i ∈ f4B2Support ↔ i = f4Index 1 ∨ i = f4Index 2 := by
  simp only [f4B2Support, Set.mem_insert_iff, Set.mem_singleton_iff]

section Data

private theorem b2_data_dec : ∀ k : Fin 4, ∀ i : Fin Tag.F4.rank,
    (i = f4Index 1 ∨ i = f4Index 2) →
    (f4B2Weight k ≠ Pi.single i 1 ∧ f4B2Weight k ≠ -Pi.single i 1) ∧
    ¬(f4IsRootB (f4B2Weight k + Pi.single i 1) = true ∧
      f4IsRootB (f4B2Weight k - Pi.single i 1) = true) ∧
    f4IsRootB (f4B2Weight k + (2 : ℤ) • Pi.single i 1) = false ∧
    f4IsRootB (f4B2Weight k - (2 : ℤ) • Pi.single i 1) = false ∧
    (f4IsRootB (f4B2Weight k + Pi.single i 1) = true →
      ∃ k', f4B2Weight k' = f4B2Weight k + Pi.single i 1) ∧
    (f4IsRootB (f4B2Weight k - Pi.single i 1) = true →
      ∃ k', f4B2Weight k' = f4B2Weight k - Pi.single i 1) := by
  decide +kernel

private theorem b2_roots_dec : ∀ k : Fin 4, f4IsRootB (f4B2Weight k) = true := by
  decide +kernel

private theorem b2_inj : Function.Injective f4B2Weight := by
  intro k k' h
  revert k k'
  decide +kernel

theorem f4B2_height : ∀ i j : Fin 4,
    (height (f4B2Weight j) < height (f4B2Weight i) ↔ i < j) ∧
      (height (f4B2Weight i) = height (f4B2Weight j) ↔ i = j) := by
  decide +kernel

theorem f4B2_outside : ∀ k : Fin 4, ∀ i : Fin Tag.F4.rank,
    ¬(i = f4Index 1 ∨ i = f4Index 2) → f4B2Weight k i = f4B2Weight 0 i := by
  decide +kernel

theorem f4B2_perm_closed : ∀ m : Fin 48,
    (∀ i : Fin Tag.F4.rank, ¬(i = f4Index 1 ∨ i = f4Index 2) →
      f4RootVec m i = f4B2Weight 0 i) → ∃ k, f4B2Weight k = f4RootVec m := by
  decide +kernel

theorem f4B2_single_eq_sub :
    (Pi.single (f4Index 1) 1 : Fin Tag.F4.rank → ℤ) = f4B2Weight 1 - f4B2Weight 2 ∧
    (Pi.single (f4Index 2) 1 : Fin Tag.F4.rank → ℤ) = f4B2Weight 0 - f4B2Weight 1 := by
  decide +kernel

theorem f4B2_pairing : ∀ k : Fin 4,
    (∑ j, Tag.F4.cartan (f4Index 1) j * f4B2Weight k j) = (![0, 1, -1, 0] : Fin 4 → ℤ) k ∧
    (∑ j, Tag.F4.cartan (f4Index 2) j * f4B2Weight k j) = (![1, -1, 1, -1] : Fin 4 → ℤ) k := by
  decide +kernel

theorem f4B2_steps :
    (∀ i j : Fin 4, f4B2Weight j + Pi.single (f4Index 1) 1 = f4B2Weight i ↔ (i = 1 ∧ j = 2)) ∧
    (∀ i j : Fin 4, f4B2Weight j - Pi.single (f4Index 1) 1 = f4B2Weight i ↔ (i = 2 ∧ j = 1)) ∧
    (∀ i j : Fin 4, f4B2Weight j + Pi.single (f4Index 2) 1 = f4B2Weight i ↔
      ((i = 0 ∧ j = 1) ∨ (i = 2 ∧ j = 3))) ∧
    (∀ i j : Fin 4, f4B2Weight j - Pi.single (f4Index 2) 1 = f4B2Weight i ↔
      ((i = 1 ∧ j = 0) ∨ (i = 3 ∧ j = 2))) := by
  decide +kernel


theorem f4B2_data : MinNativeData Tag.F4 4 f4B2Support f4B2Weight where
  isRoot k := isRoot_iff_f4IsRootB.2 (b2_roots_dec k)
  injective := b2_inj
  ne_single k i hi := (b2_data_dec k i ((mem_f4B2Support i).1 hi)).1
  not_both k i hi := by
    have h := (b2_data_dec k i ((mem_f4B2Support i).1 hi)).2.1
    rwa [isRoot_iff_f4IsRootB, isRoot_iff_f4IsRootB]
  no_two_up k i hi := by
    have h := (b2_data_dec k i ((mem_f4B2Support i).1 hi)).2.2.1
    rw [isRoot_iff_f4IsRootB, h]
    exact Bool.false_ne_true
  no_two_down k i hi := by
    have h := (b2_data_dec k i ((mem_f4B2Support i).1 hi)).2.2.2.1
    rw [isRoot_iff_f4IsRootB, h]
    exact Bool.false_ne_true
  up_mem k i hi hr := (b2_data_dec k i ((mem_f4B2Support i).1 hi)).2.2.2.2.1
    (isRoot_iff_f4IsRootB.1 hr)
  down_mem k i hi hr := (b2_data_dec k i ((mem_f4B2Support i).1 hi)).2.2.2.2.2
    (isRoot_iff_f4IsRootB.1 hr)

theorem f4B2_bruhat : MinNativeBruhat f4B2_data 0 where
  precedes i j := by
    simp only [Label.Precedes, Label.weight]
    constructor
    · rintro (h | ⟨h, h'⟩)
      · exact ((f4B2_height i j).1).1 h
      · obtain rfl := ((f4B2_height i j).2).1 h
        exact absurd h' (lt_irrefl _)
    · intro h
      exact Or.inl (((f4B2_height i j).1).2 h)
  outside k i hi := f4B2_outside k i (by rwa [← mem_f4B2Support])
  perm_closed β hβ hout := by
    obtain ⟨m, rfl⟩ := isRoot_iff_exists_f4RootVec.1 hβ
    exact f4B2_perm_closed m fun i hi => hout i (fun h => hi ((mem_f4B2Support i).1 h))
  single_eq_sub i hi := by
    rcases (mem_f4B2Support i).1 hi with rfl | rfl
    · exact ⟨1, 2, f4B2_single_eq_sub.1⟩
    · exact ⟨0, 1, f4B2_single_eq_sub.2⟩

end Data

end CFSG.RankThree.PartOne.KF4
