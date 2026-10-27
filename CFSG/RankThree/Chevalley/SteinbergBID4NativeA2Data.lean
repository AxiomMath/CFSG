module

public import CFSG.RankThree.Chevalley.SteinbergBID4RootOps
public import CFSG.RankThree.E6.RootLatticeTools
public import CFSG.RankThree.Lattice.SteinbergBIListMatrix

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6

@[expose] def d4SuppA2 : Set (Fin Tag.D4.rank) := {0, 2}

theorem mem_d4SuppA2 (i : Fin Tag.D4.rank) : i ∈ d4SuppA2 ↔ i = 0 ∨ i = 2 :=
  Iff.rfl

theorem zero_mem_d4SuppA2 : (0 : Fin Tag.D4.rank) ∈ d4SuppA2 := (mem_d4SuppA2 _).2 (Or.inl rfl)
theorem two_mem_d4SuppA2 : (2 : Fin Tag.D4.rank) ∈ d4SuppA2 := (mem_d4SuppA2 _).2 (Or.inr rfl)

@[expose] def d4ChainA2 : Fin 2 → Fin Tag.D4.rank := ![0, 2]

@[expose] def d4A2Weight : Fin 3 → Fin Tag.D4.rank → ℤ :=
  (![![1, 0, 1, 1], ![0, 0, 1, 1], ![0, 0, 0, 1]] : Fin 3 → Fin 4 → ℤ)

theorem exists_d4RootVec_d4A2Weight : ∀ k : Fin 3, ∃ m : Fin 24, d4RootVec m = d4A2Weight k := by
  decide +kernel

theorem isRoot_d4A2Weight (k : Fin 3) : IsRoot Tag.D4 (d4A2Weight k) := by
  obtain ⟨m, hm⟩ := exists_d4RootVec_d4A2Weight k
  rw [← hm]
  exact isRoot_d4RootVec m

theorem d4A2Weight_injective : Function.Injective d4A2Weight := by
  intro k k' h
  revert k k'
  decide

abbrev d4A2Label (k : Fin 3) : Label Tag.D4 := Sum.inr ⟨d4A2Weight k, isRoot_d4A2Weight k⟩

theorem d4A2Label_injective : Function.Injective d4A2Label := by
  intro k k' h
  exact d4A2Weight_injective (congrArg Subtype.val (Sum.inr_injective h))

theorem d4A2Weight_ne_single : ∀ k : Fin 3, ∀ i : Fin Tag.D4.rank, (i = 0 ∨ i = 2) →
    d4A2Weight k ≠ Pi.single i 1 ∧ d4A2Weight k ≠ -Pi.single i 1 := by
  decide +kernel

theorem d4A2Weight_add_single : ∀ k : Fin 3, ∀ i : Fin Tag.D4.rank, (i = 0 ∨ i = 2) →
    (∀ m : Fin 24, d4RootVec m ≠ d4A2Weight k + Pi.single i 1) ∨
      ∃ k', d4A2Weight k' = d4A2Weight k + Pi.single i 1 := by
  decide +kernel

theorem d4A2Weight_sub_single : ∀ k : Fin 3, ∀ i : Fin Tag.D4.rank, (i = 0 ∨ i = 2) →
    (∀ m : Fin 24, d4RootVec m ≠ d4A2Weight k - Pi.single i 1) ∨
      ∃ k', d4A2Weight k' = d4A2Weight k - Pi.single i 1 := by
  decide +kernel

theorem d4A2Weight_add_e0 : ∀ a b : Fin 3,
    d4A2Weight b + Pi.single (0 : Fin Tag.D4.rank) 1 = d4A2Weight a ↔ (a = 0 ∧ b = 1) := by
  decide +kernel

theorem d4A2Weight_sub_e0 : ∀ a b : Fin 3,
    d4A2Weight b - Pi.single (0 : Fin Tag.D4.rank) 1 = d4A2Weight a ↔ (a = 1 ∧ b = 0) := by
  decide +kernel

theorem d4A2Weight_add_e2 : ∀ a b : Fin 3,
    d4A2Weight b + Pi.single (2 : Fin Tag.D4.rank) 1 = d4A2Weight a ↔ (a = 1 ∧ b = 2) := by
  decide +kernel

theorem d4A2Weight_sub_e2 : ∀ a b : Fin 3,
    d4A2Weight b - Pi.single (2 : Fin Tag.D4.rank) 1 = d4A2Weight a ↔ (a = 2 ∧ b = 1) := by
  decide +kernel

theorem d4A2Weight_pairing : ∀ k : Fin 3,
    (∑ j, Tag.D4.cartan 0 j * d4A2Weight k j) = (![1, -1, 0] : Fin 3 → ℤ) k ∧
    (∑ j, Tag.D4.cartan 2 j * d4A2Weight k j) = (![0, 1, -1] : Fin 3 → ℤ) k := by
  decide +kernel

theorem chainRootA2_mem : ∀ k l : Fin 3, k ≠ l → ∃ m : Fin 24,
    d4RootVec m = chainRoot d4ChainA2 k l ∧ ∀ i : Fin Tag.D4.rank, i ≠ 0 → i ≠ 2 →
      chainRoot d4ChainA2 k l i = 0 := by
  decide +kernel

theorem chainRootA2_mem_parabolicRoots {k l : Fin 3} (hkl : k ≠ l) :
    chainRoot d4ChainA2 k l ∈ parabolicRoots Tag.D4 d4SuppA2 := by
  obtain ⟨m, hm, hs⟩ := chainRootA2_mem k l hkl
  rw [← hm]
  refine ⟨isRoot_d4RootVec m, fun i hi => ?_⟩
  rw [hm]
  exact hs i (fun h => hi (Or.inl h)) (fun h => hi (Or.inr h))

theorem exists_chainRootA2_of_d4RootVec : ∀ m : Fin 24, (∀ i : Fin Tag.D4.rank, i ≠ 0 → i ≠ 2 →
    d4RootVec m i = 0) → ∃ k l : Fin 3, k ≠ l ∧ chainRoot d4ChainA2 k l = d4RootVec m := by
  decide +kernel

theorem exists_chainRootA2_of_mem {α : Fin Tag.D4.rank → ℤ}
    (hα : α ∈ parabolicRoots Tag.D4 d4SuppA2) :
    ∃ k l : Fin 3, k ≠ l ∧ chainRoot d4ChainA2 k l = α := by
  obtain ⟨m, rfl⟩ := isRoot_iff_exists_d4RootVec.1 hα.1
  exact exists_chainRootA2_of_d4RootVec m fun i h0 h2 => hα.2 i (by
    rintro (h | h)
    · exact h0 h
    · exact h2 h)

theorem chainRootA2_values :
    chainRoot d4ChainA2 0 1 = Pi.single (0 : Fin Tag.D4.rank) 1 ∧
    chainRoot d4ChainA2 1 2 = Pi.single (2 : Fin Tag.D4.rank) 1 ∧
    chainRoot d4ChainA2 1 0 = -Pi.single (0 : Fin Tag.D4.rank) 1 ∧
    chainRoot d4ChainA2 2 1 = -Pi.single (2 : Fin Tag.D4.rank) 1 := by
  decide +kernel

theorem chainRootA2_sums :
    (chainRoot d4ChainA2 0 1 + chainRoot d4ChainA2 1 2 = chainRoot d4ChainA2 0 2 ∧
      chainRoot d4ChainA2 0 1 ≠ chainRoot d4ChainA2 1 2 ∧
      chainRoot d4ChainA2 0 1 ≠ -chainRoot d4ChainA2 1 2) ∧
    (chainRoot d4ChainA2 2 1 + chainRoot d4ChainA2 1 0 = chainRoot d4ChainA2 2 0 ∧
      chainRoot d4ChainA2 2 1 ≠ chainRoot d4ChainA2 1 0 ∧
      chainRoot d4ChainA2 2 1 ≠ -chainRoot d4ChainA2 1 0) := by
  decide +kernel

theorem d4A2Weight_height : ∀ i j : Fin 3,
    (height (d4A2Weight j) < height (d4A2Weight i) ↔ i < j) ∧
      (height (d4A2Weight i) = height (d4A2Weight j) ↔ i = j) := by
  decide

theorem d4A2Label_precedes_iff (i j : Fin 3) :
    (d4A2Label i).Precedes (d4A2Label j) ↔ i < j := by
  simp only [Label.Precedes, Label.weight]
  constructor
  · rintro (h | ⟨h, h'⟩)
    · exact ((d4A2Weight_height i j).1).1 h
    · obtain rfl := ((d4A2Weight_height i j).2).1 h
      exact absurd h' (lt_irrefl _)
  · intro h
    exact Or.inl (((d4A2Weight_height i j).1).2 h)

theorem d4A2Weight_outside : ∀ k : Fin 3, d4A2Weight k 1 = 0 ∧ d4A2Weight k 3 = 1 := by
  decide

theorem exists_d4A2Weight_of_d4RootVec : ∀ m : Fin 24, d4RootVec m 1 = 0 →
    d4RootVec m 3 = 1 → ∃ k, d4A2Weight k = d4RootVec m := by
  decide +kernel

theorem one_not_mem_d4SuppA2 : (1 : Fin Tag.D4.rank) ∉ d4SuppA2 := by
  rintro (h | h) <;> exact absurd h (by decide)

theorem three_not_mem_d4SuppA2 : (3 : Fin Tag.D4.rank) ∉ d4SuppA2 := by
  rintro (h | h) <;> exact absurd h (by decide)

theorem exists_d4A2Weight_smul {w : WeylGroup Tag.D4}
    (hw : w ∈ parabolicWeylGroup Tag.D4 d4SuppA2) (k : Fin 3) :
    ∃ k', d4A2Weight k' = w • d4A2Weight k := by
  obtain ⟨a1, a3⟩ := d4A2Weight_outside k
  obtain ⟨m, hm⟩ := isRoot_iff_exists_d4RootVec.1 (IsRoot.smul (isRoot_d4A2Weight k) w)
  obtain ⟨k', hk'⟩ := exists_d4A2Weight_of_d4RootVec m
    (by rw [hm, smul_apply_of_mem_parabolicWeylGroup hw _ one_not_mem_d4SuppA2, a1])
    (by rw [hm, smul_apply_of_mem_parabolicWeylGroup hw _ three_not_mem_d4SuppA2, a3])
  exact ⟨k', hk'.trans hm⟩

theorem smul_d4A2Weight_eq_of_not_lt {w : WeylGroup Tag.D4}
    (hw : w ∈ parabolicWeylGroup Tag.D4 d4SuppA2)
    (hprec : ∀ j j', d4A2Weight j' = w • d4A2Weight j → ¬j < j') (j : Fin 3) :
    w • d4A2Weight j = d4A2Weight j := by
  by_contra hj
  classical
  set M : Finset (Fin 3) := Finset.univ.filter fun k => w • d4A2Weight k ≠ d4A2Weight k
  have hM : M.Nonempty := ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
  obtain ⟨k, hkM, hmin⟩ := M.exists_min_image id hM
  have hk : w • d4A2Weight k ≠ d4A2Weight k := (Finset.mem_filter.mp hkM).2
  obtain ⟨k', hk'⟩ := exists_d4A2Weight_smul hw k
  have hne : k' ≠ k := fun h => hk (by rw [← hk', h])
  have hlt : k' < k := lt_of_le_of_ne (not_lt.1 (hprec k k' hk')) hne
  have hk'M : k' ∈ M := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun h => hne ?_⟩
    apply d4A2Weight_injective
    apply smul_left_cancel w
    rw [h]
    exact hk'
  exact absurd (hmin k' hk'M) (not_le.mpr hlt)

theorem single_eq_d4A2Weight_sub :
    (Pi.single (0 : Fin Tag.D4.rank) 1 : Fin Tag.D4.rank → ℤ) = d4A2Weight 0 - d4A2Weight 1 ∧
    (Pi.single (2 : Fin Tag.D4.rank) 1 : Fin Tag.D4.rank → ℤ) = d4A2Weight 1 - d4A2Weight 2 := by
  decide

theorem eq_one_of_smul_d4A2Weight {w : WeylGroup Tag.D4}
    (hw : w ∈ parabolicWeylGroup Tag.D4 d4SuppA2) (h : ∀ k, w • d4A2Weight k = d4A2Weight k) :
    w = 1 := by
  obtain ⟨e0, e2⟩ := single_eq_d4A2Weight_sub
  refine eq_one_of_forall_height_pos fun i => ?_
  by_cases hi : i ∈ d4SuppA2
  · have hfix : w • (Pi.single i 1 : Fin Tag.D4.rank → ℤ) = Pi.single i 1 := by
      rcases (mem_d4SuppA2 i).1 hi with rfl | rfl
      · rw [e0, smul_sub, h, h]
      · rw [e2, smul_sub, h, h]
    rw [hfix, height_single]
    exact one_pos
  · have hroot := IsRoot.smul (isRoot_single Tag.D4 i) w
    have hcoord : (w • (Pi.single i 1 : Fin Tag.D4.rank → ℤ)) i = 1 := by
      rw [smul_apply_of_mem_parabolicWeylGroup hw _ hi, Pi.single_eq_same]
    refine (IsRoot.height_pos_iff hroot).2 ?_
    rcases hroot.nonneg_or_nonpos with hs | hs
    · exact hs
    · have := hs i
      omega

@[expose] def d4A2PosRoot : Fin 3 → Fin Tag.D4.rank → ℤ :=
  ![chainRoot d4ChainA2 1 2, chainRoot d4ChainA2 0 1, chainRoot d4ChainA2 0 2]

theorem d4A2PosRoot_injective : Function.Injective d4A2PosRoot := by
  intro k k' h
  revert k k'
  decide +kernel

theorem chainRootA2_height_pos : ∀ k l : Fin 3, k ≠ l →
    (0 < height (chainRoot d4ChainA2 k l) ↔ k < l) := by
  decide +kernel

theorem exists_d4A2PosRoot : ∀ k l : Fin 3, k < l →
    ∃ m, d4A2PosRoot m = chainRoot d4ChainA2 k l := by
  decide +kernel

@[expose] def d4A2PosRow : Fin 3 → Fin 3 := ![1, 0, 0]

@[expose] def d4A2PosCol : Fin 3 → Fin 3 := ![2, 1, 2]

theorem d4A2PosRoot_eq (m : Fin 3) :
    d4A2PosRoot m = chainRoot d4ChainA2 (d4A2PosRow m) (d4A2PosCol m) := by
  fin_cases m <;> rfl

theorem d4A2PosRow_lt_col : ∀ m : Fin 3, d4A2PosRow m < d4A2PosCol m := by decide

theorem range_d4A2PosRoot : Set.range d4A2PosRoot = parabolicPosRoots Tag.D4 d4SuppA2 := by
  ext β
  constructor
  · rintro ⟨m, rfl⟩
    rw [d4A2PosRoot_eq]
    have hmem := chainRootA2_mem_parabolicRoots (d4A2PosRow_lt_col m).ne
    exact ⟨hmem, hmem.1, (chainRootA2_height_pos _ _ (d4A2PosRow_lt_col m).ne).2
      (d4A2PosRow_lt_col m)⟩
  · rintro ⟨hβ, -, hpos⟩
    obtain ⟨k, l, hkl, rfl⟩ := exists_chainRootA2_of_mem hβ
    exact exists_d4A2PosRoot k l ((chainRootA2_height_pos k l hkl).1 hpos)

theorem d4A2PosRoot_mem (m : Fin 3) : d4A2PosRoot m ∈ parabolicRoots Tag.D4 d4SuppA2 :=
  (show d4A2PosRoot m ∈ parabolicPosRoots Tag.D4 d4SuppA2 from range_d4A2PosRoot ▸ ⟨m, rfl⟩).1

@[expose] def d4A2Sigma : Set (Fin Tag.D4.rank → ℤ) :=
  {Pi.single 0 1, -Pi.single 0 1, Pi.single 2 1, -Pi.single 2 1,
    Pi.single 0 1 + Pi.single 2 1, -(Pi.single 0 1 + Pi.single 2 1)}

theorem chainRootA2_cases : ∀ k l : Fin 3, k ≠ l →
    chainRoot d4ChainA2 k l = Pi.single 0 1 ∨ chainRoot d4ChainA2 k l = -Pi.single 0 1 ∨
      chainRoot d4ChainA2 k l = Pi.single 2 1 ∨ chainRoot d4ChainA2 k l = -Pi.single 2 1 ∨
      chainRoot d4ChainA2 k l = Pi.single 0 1 + Pi.single 2 1 ∨
      chainRoot d4ChainA2 k l = -(Pi.single 0 1 + Pi.single 2 1) := by
  decide +kernel

theorem chainRootA2_values' :
    chainRoot d4ChainA2 0 2 = Pi.single (0 : Fin Tag.D4.rank) 1 + Pi.single 2 1 ∧
    chainRoot d4ChainA2 2 0 = -(Pi.single (0 : Fin Tag.D4.rank) 1 + Pi.single 2 1) := by
  decide +kernel

theorem parabolicRoots_d4SuppA2 : parabolicRoots Tag.D4 d4SuppA2 = d4A2Sigma := by
  ext α
  constructor
  · intro hα
    obtain ⟨k, l, hkl, rfl⟩ := exists_chainRootA2_of_mem hα
    simp only [d4A2Sigma, Set.mem_insert_iff, Set.mem_singleton_iff]
    exact chainRootA2_cases k l hkl
  · intro hα
    obtain ⟨c01, c12, c10, c21⟩ := chainRootA2_values
    obtain ⟨c02, c20⟩ := chainRootA2_values'
    simp only [d4A2Sigma, Set.mem_insert_iff, Set.mem_singleton_iff] at hα
    rcases hα with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [← c01]; exact chainRootA2_mem_parabolicRoots (by decide)
    · rw [← c10]; exact chainRootA2_mem_parabolicRoots (by decide)
    · rw [← c12]; exact chainRootA2_mem_parabolicRoots (by decide)
    · rw [← c21]; exact chainRootA2_mem_parabolicRoots (by decide)
    · rw [← c02]; exact chainRootA2_mem_parabolicRoots (by decide)
    · rw [← c20]; exact chainRootA2_mem_parabolicRoots (by decide)

end CFSG.RankThree.Chevalley
