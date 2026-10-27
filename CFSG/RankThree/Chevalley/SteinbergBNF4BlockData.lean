module

public import CFSG.RankThree.Chevalley.SteinbergBNF4Block

public noncomputable section

namespace CFSG.RankThree.Chevalley.SteinbergBN

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix

theorem isRoot_F4_iff {v : Fin Tag.F4.rank → ℤ} :
    IsRoot Tag.F4 v ↔ ∃ k : Fin 48, Tag.F4.rootCertificate.root k = v := by
  rw [RootCertificate.isRoot_iff (Tag.rootCertificate_check .F4),
    show Tag.F4.rootCertificate.roots.length = 48 from rfl]
  exact ⟨fun ⟨k, hk, h⟩ => ⟨⟨k, hk⟩, h⟩, fun ⟨k, h⟩ => ⟨k, k.2, h⟩⟩

theorem isRoot_of_idx {k : ℕ} (hk : k < Tag.F4.rootCertificate.roots.length)
    {v : Fin Tag.F4.rank → ℤ} (h : Tag.F4.rootCertificate.root k = v) : IsRoot Tag.F4 v :=
  h ▸ RootCertificate.isRoot_root (Tag.rootCertificate_check .F4) k hk

theorem precedes_of_height_lt {α γ : Fin Tag.F4.rank → ℤ} (hα : IsRoot Tag.F4 α)
    (hγ : IsRoot Tag.F4 γ) (h : height γ < height α) :
    Label.Precedes (Sum.inr ⟨α, hα⟩ : Label Tag.F4) (Sum.inr ⟨γ, hγ⟩) :=
  Or.inl h

abbrev f4LongJ : Set (Fin Tag.F4.rank) := {0, 1}

theorem mem_f4LongJ (s : Fin Tag.F4.rank) : s ∈ f4LongJ ↔ s = 0 ∨ s = 1 :=
  Iff.rfl

theorem zero_mem_f4LongJ : (0 : Fin Tag.F4.rank) ∈ f4LongJ := Or.inl rfl
theorem one_mem_f4LongJ : (1 : Fin Tag.F4.rank) ∈ f4LongJ := Or.inr rfl

@[expose] def f4LongWeight : Fin 3 → Fin Tag.F4.rank → ℤ :=
  (![![1, 1, 1, 0], ![0, 1, 1, 0], ![0, 0, 1, 0]] : Fin 3 → Fin 4 → ℤ)

@[expose] def f4LongIdx : Fin 3 → ℕ := ![16, 8, 2]

theorem f4LongIdx_spec : ∀ b, f4LongIdx b < Tag.F4.rootCertificate.roots.length ∧
    Tag.F4.rootCertificate.root (f4LongIdx b) = f4LongWeight b := by
  decide +kernel

theorem f4Long_slice : ∀ k : Fin 48, Tag.F4.rootCertificate.root k 2 = 1 →
    Tag.F4.rootCertificate.root k 3 = 0 → ∃ b, f4LongWeight b = Tag.F4.rootCertificate.root k := by
  decide +kernel

theorem f4Long_checks :
    (∀ b, f4LongWeight b 2 = 1 ∧ f4LongWeight b 3 = 0) ∧
    (∀ b, ∀ i : Fin Tag.F4.rank, (i = 0 ∨ i = 1) →
      f4LongWeight b ≠ Pi.single i 1 ∧ f4LongWeight b ≠ -Pi.single i 1) ∧
    (∀ j j' : Fin 3, j < j' → height (f4LongWeight j') < height (f4LongWeight j)) ∧
    (Pi.single (0 : Fin Tag.F4.rank) 1 : Fin Tag.F4.rank → ℤ) = f4LongWeight 0 - f4LongWeight 1 ∧
    (Pi.single (1 : Fin Tag.F4.rank) 1 : Fin Tag.F4.rank → ℤ) =
      f4LongWeight 1 - f4LongWeight 2 := by
  decide +kernel

theorem isSliceBlock_f4LongWeight
    : IsSliceBlock f4LongJ f4LongWeight where
  isRoot b := isRoot_of_idx (f4LongIdx_spec b).1 (f4LongIdx_spec b).2
  injective := by
    intro a b h
    revert a b
    decide
  slice := by
    refine ⟨![0, 0, 1, 0], fun b s hs => ?_, fun γ hγ hs => ?_⟩
    · have h2 : s = 2 ∨ s = 3 := by
        rw [mem_f4LongJ] at hs
        revert s
        decide
      obtain ⟨e2, e3⟩ := f4Long_checks.1 b
      rcases h2 with rfl | rfl
      · exact e2
      · exact e3
    · obtain ⟨k, rfl⟩ := isRoot_F4_iff.1 hγ
      exact f4Long_slice k (hs 2 (by rw [mem_f4LongJ]; decide))
        (hs 3 (by rw [mem_f4LongJ]; decide))
  ne_single b i hi := f4Long_checks.2.1 b i hi
  precedes j j' h := precedes_of_height_lt _ _ (f4Long_checks.2.2.1 j j' h)
  simple i hi := by
    rcases hi with rfl | rfl
    · exact ⟨0, 1, f4Long_checks.2.2.2.1⟩
    · exact ⟨1, 2, f4Long_checks.2.2.2.2⟩

theorem f4Long_coeff_x0 : ∀ k : Fin 4, xCoeff f4LongWeight
    (fun b => Tag.F4.stringData.up (f4LongIdx b) 0)
    (fun b => Tag.F4.stringData.down (f4LongIdx b) 0) 0 k =
      ![1, !![0, 1, 0; 0, 0, 0; 0, 0, 0],
        !![0, 0, 0; 0, 0, 0; 0, 0, 0], 0] k := by
  decide +kernel

theorem f4Long_coeff_y0 : ∀ k : Fin 4, yCoeff f4LongWeight
    (fun b => Tag.F4.stringData.up (f4LongIdx b) 0)
    (fun b => Tag.F4.stringData.down (f4LongIdx b) 0) 0 k =
      ![1, !![0, 0, 0; 1, 0, 0; 0, 0, 0],
        !![0, 0, 0; 0, 0, 0; 0, 0, 0], 0] k := by
  decide +kernel

theorem f4Long_coeff_x1 : ∀ k : Fin 4, xCoeff f4LongWeight
    (fun b => Tag.F4.stringData.up (f4LongIdx b) 1)
    (fun b => Tag.F4.stringData.down (f4LongIdx b) 1) 1 k =
      ![1, !![0, 0, 0; 0, 0, 1; 0, 0, 0],
        !![0, 0, 0; 0, 0, 0; 0, 0, 0], 0] k := by
  decide +kernel

theorem f4Long_coeff_y1 : ∀ k : Fin 4, yCoeff f4LongWeight
    (fun b => Tag.F4.stringData.up (f4LongIdx b) 1)
    (fun b => Tag.F4.stringData.down (f4LongIdx b) 1) 1 k =
      ![1, !![0, 0, 0; 0, 0, 0; 0, 1, 0],
        !![0, 0, 0; 0, 0, 0; 0, 0, 0], 0] k := by
  decide +kernel

@[expose] def f4LongPos : Fin 3 → Fin Tag.F4.rank → ℤ :=
  (![![1, 0, 0, 0], ![0, 1, 0, 0], ![1, 1, 0, 0]] : Fin 3 → Fin 4 → ℤ)

theorem f4LongPos_checks :
    (∀ a, ∃ k : Fin 48, Tag.F4.rootCertificate.root k = f4LongPos a) ∧
    (∀ a, f4LongPos a 2 = 0 ∧ f4LongPos a 3 = 0 ∧ 0 < height (f4LongPos a)) ∧
    (∀ k : Fin 48, Tag.F4.rootCertificate.root k 2 = 0 → Tag.F4.rootCertificate.root k 3 = 0 →
      0 < height (Tag.F4.rootCertificate.root k) →
        ∃ a, f4LongPos a = Tag.F4.rootCertificate.root k) ∧
    Function.Injective f4LongPos ∧
    f4LongPos 0 = Pi.single 0 1 ∧ f4LongPos 1 = Pi.single 1 1 ∧
    f4LongPos 2 = reflect Tag.F4 0 (Pi.single 1 1) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ?_, by decide +kernel,
    by decide +kernel, by decide +kernel⟩
  intro a b h
  revert a b
  decide

abbrev f4ShortJ : Set (Fin Tag.F4.rank) := {2, 3}

theorem mem_f4ShortJ (s : Fin Tag.F4.rank) : s ∈ f4ShortJ ↔ s = 2 ∨ s = 3 :=
  Iff.rfl

theorem two_mem_f4ShortJ : (2 : Fin Tag.F4.rank) ∈ f4ShortJ := Or.inl rfl
theorem three_mem_f4ShortJ : (3 : Fin Tag.F4.rank) ∈ f4ShortJ := Or.inr rfl

@[expose] def f4ShortWeight : Fin 6 → Fin Tag.F4.rank → ℤ :=
  (![![0, 1, 2, 2], ![0, 1, 2, 1], ![0, 1, 1, 1], ![0, 1, 2, 0], ![0, 1, 1, 0], ![0, 1, 0, 0]] :
    Fin 6 → Fin 4 → ℤ)

@[expose] def f4ShortIdx : Fin 6 → ℕ := ![15, 25, 17, 7, 8, 1]

theorem f4ShortIdx_spec : ∀ b, f4ShortIdx b < Tag.F4.rootCertificate.roots.length ∧
    Tag.F4.rootCertificate.root (f4ShortIdx b) = f4ShortWeight b := by
  decide +kernel

theorem f4Short_slice : ∀ k : Fin 48, Tag.F4.rootCertificate.root k 0 = 0 →
    Tag.F4.rootCertificate.root k 1 = 1 →
      ∃ b, f4ShortWeight b = Tag.F4.rootCertificate.root k := by
  decide +kernel

theorem f4Short_checks :
    (∀ b, f4ShortWeight b 0 = 0 ∧ f4ShortWeight b 1 = 1) ∧
    (∀ b, ∀ i : Fin Tag.F4.rank, (i = 2 ∨ i = 3) →
      f4ShortWeight b ≠ Pi.single i 1 ∧ f4ShortWeight b ≠ -Pi.single i 1) ∧
    (∀ j j' : Fin 6, j < j' → ¬(j = 2 ∧ j' = 3) →
      height (f4ShortWeight j') < height (f4ShortWeight j)) ∧
    height (f4ShortWeight 2) = height (f4ShortWeight 3) ∧
    (Pi.single (2 : Fin Tag.F4.rank) 1 : Fin Tag.F4.rank → ℤ) =
      f4ShortWeight 1 - f4ShortWeight 2 ∧
    (Pi.single (3 : Fin Tag.F4.rank) 1 : Fin Tag.F4.rank → ℤ) =
      f4ShortWeight 2 - f4ShortWeight 4 := by
  decide +kernel

theorem f4ShortWeight_lex : toLex (f4ShortWeight 2) < toLex (f4ShortWeight 3) :=
  show Pi.Lex (· < ·) (· < ·) (f4ShortWeight 2) (f4ShortWeight 3) from
    ⟨2, by decide, by decide⟩

theorem isSliceBlock_f4ShortWeight
    : IsSliceBlock f4ShortJ f4ShortWeight where
  isRoot b := isRoot_of_idx (f4ShortIdx_spec b).1 (f4ShortIdx_spec b).2
  injective := by
    intro a b h
    revert a b
    decide
  slice := by
    refine ⟨![0, 1, 0, 0], fun b s hs => ?_, fun γ hγ hs => ?_⟩
    · have h2 : s = 0 ∨ s = 1 := by
        rw [mem_f4ShortJ] at hs
        revert s
        decide
      obtain ⟨e0, e1⟩ := f4Short_checks.1 b
      rcases h2 with rfl | rfl
      · exact e0
      · exact e1
    · obtain ⟨k, rfl⟩ := isRoot_F4_iff.1 hγ
      exact f4Short_slice k (hs 0 (by rw [mem_f4ShortJ]; decide))
        (hs 1 (by rw [mem_f4ShortJ]; decide))
  ne_single b i hi := f4Short_checks.2.1 b i hi
  precedes j j' h := by
    by_cases h23 : j = 2 ∧ j' = 3
    · obtain ⟨rfl, rfl⟩ := h23
      exact Or.inr ⟨f4Short_checks.2.2.2.1, f4ShortWeight_lex⟩
    · exact precedes_of_height_lt _ _ (f4Short_checks.2.2.1 j j' h h23)
  simple i hi := by
    rcases hi with rfl | rfl
    · exact ⟨1, 2, f4Short_checks.2.2.2.2.1⟩
    · exact ⟨2, 4, f4Short_checks.2.2.2.2.2⟩

theorem f4Short_coeff_x2 : ∀ k : Fin 4, xCoeff f4ShortWeight
    (fun b => Tag.F4.stringData.up (f4ShortIdx b) 2)
    (fun b => Tag.F4.stringData.down (f4ShortIdx b) 2) 2 k =
      ![1, !![0, 0, 0, 0, 0, 0;
          0, 0, 1, 0, 0, 0;
          0, 0, 0, 0, 0, 0;
          0, 0, 0, 0, 2, 0;
          0, 0, 0, 0, 0, 1;
          0, 0, 0, 0, 0, 0],
        !![0, 0, 0, 0, 0, 0;
          0, 0, 0, 0, 0, 0;
          0, 0, 0, 0, 0, 0;
          0, 0, 0, 0, 0, 1;
          0, 0, 0, 0, 0, 0;
          0, 0, 0, 0, 0, 0], 0] k := by
  decide +kernel

theorem f4Short_coeff_y2 : ∀ k : Fin 4, yCoeff f4ShortWeight
    (fun b => Tag.F4.stringData.up (f4ShortIdx b) 2)
    (fun b => Tag.F4.stringData.down (f4ShortIdx b) 2) 2 k =
      ![1, !![0, 0, 0, 0, 0, 0;
          0, 0, 0, 0, 0, 0;
          0, 1, 0, 0, 0, 0;
          0, 0, 0, 0, 0, 0;
          0, 0, 0, 1, 0, 0;
          0, 0, 0, 0, 2, 0],
        !![0, 0, 0, 0, 0, 0;
          0, 0, 0, 0, 0, 0;
          0, 0, 0, 0, 0, 0;
          0, 0, 0, 0, 0, 0;
          0, 0, 0, 0, 0, 0;
          0, 0, 0, 1, 0, 0], 0] k := by
  decide +kernel

theorem f4Short_coeff_x3 : ∀ k : Fin 4, xCoeff f4ShortWeight
    (fun b => Tag.F4.stringData.up (f4ShortIdx b) 3)
    (fun b => Tag.F4.stringData.down (f4ShortIdx b) 3) 3 k =
      ![1, !![0, 2, 0, 0, 0, 0;
          0, 0, 0, 1, 0, 0;
          0, 0, 0, 0, 1, 0;
          0, 0, 0, 0, 0, 0;
          0, 0, 0, 0, 0, 0;
          0, 0, 0, 0, 0, 0],
        !![0, 0, 0, 1, 0, 0;
          0, 0, 0, 0, 0, 0;
          0, 0, 0, 0, 0, 0;
          0, 0, 0, 0, 0, 0;
          0, 0, 0, 0, 0, 0;
          0, 0, 0, 0, 0, 0], 0] k := by
  decide +kernel

theorem f4Short_coeff_y3 : ∀ k : Fin 4, yCoeff f4ShortWeight
    (fun b => Tag.F4.stringData.up (f4ShortIdx b) 3)
    (fun b => Tag.F4.stringData.down (f4ShortIdx b) 3) 3 k =
      ![1, !![0, 0, 0, 0, 0, 0;
          1, 0, 0, 0, 0, 0;
          0, 0, 0, 0, 0, 0;
          0, 2, 0, 0, 0, 0;
          0, 0, 1, 0, 0, 0;
          0, 0, 0, 0, 0, 0],
        !![0, 0, 0, 0, 0, 0;
          0, 0, 0, 0, 0, 0;
          0, 0, 0, 0, 0, 0;
          1, 0, 0, 0, 0, 0;
          0, 0, 0, 0, 0, 0;
          0, 0, 0, 0, 0, 0], 0] k := by
  decide +kernel

@[expose] def f4ShortPos : Fin 3 → Fin Tag.F4.rank → ℤ :=
  (![![0, 0, 1, 0], ![0, 0, 0, 1], ![0, 0, 1, 1]] : Fin 3 → Fin 4 → ℤ)

theorem f4ShortPos_checks :
    (∀ a, ∃ k : Fin 48, Tag.F4.rootCertificate.root k = f4ShortPos a) ∧
    (∀ a, f4ShortPos a 0 = 0 ∧ f4ShortPos a 1 = 0 ∧ 0 < height (f4ShortPos a)) ∧
    (∀ k : Fin 48, Tag.F4.rootCertificate.root k 0 = 0 → Tag.F4.rootCertificate.root k 1 = 0 →
      0 < height (Tag.F4.rootCertificate.root k) →
        ∃ a, f4ShortPos a = Tag.F4.rootCertificate.root k) ∧
    Function.Injective f4ShortPos ∧
    f4ShortPos 0 = Pi.single 2 1 ∧ f4ShortPos 1 = Pi.single 3 1 ∧
    f4ShortPos 2 = reflect Tag.F4 2 (Pi.single 3 1) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ?_, by decide +kernel,
    by decide +kernel, by decide +kernel⟩
  intro a b h
  revert a b
  decide

abbrev f4B2J : Set (Fin Tag.F4.rank) := {1, 2}

theorem mem_f4B2J (s : Fin Tag.F4.rank) : s ∈ f4B2J ↔ s = 1 ∨ s = 2 :=
  Iff.rfl

theorem one_mem_f4B2J : (1 : Fin Tag.F4.rank) ∈ f4B2J := Or.inl rfl
theorem two_mem_f4B2J : (2 : Fin Tag.F4.rank) ∈ f4B2J := Or.inr rfl

@[expose] def f4B2Weight : Fin 4 → Fin Tag.F4.rank → ℤ :=
  (![![0, 1, 2, 1], ![0, 1, 1, 1], ![0, 0, 1, 1], ![0, 0, 0, 1]] : Fin 4 → Fin 4 → ℤ)

@[expose] def f4B2Idx : Fin 4 → ℕ := ![25, 17, 10, 3]

theorem f4B2Idx_spec : ∀ b, f4B2Idx b < Tag.F4.rootCertificate.roots.length ∧
    Tag.F4.rootCertificate.root (f4B2Idx b) = f4B2Weight b := by
  decide +kernel

theorem f4B2_slice : ∀ k : Fin 48, Tag.F4.rootCertificate.root k 0 = 0 →
    Tag.F4.rootCertificate.root k 3 = 1 →
      ∃ b, f4B2Weight b = Tag.F4.rootCertificate.root k := by
  decide +kernel

theorem f4B2_checks :
    (∀ b, f4B2Weight b 0 = 0 ∧ f4B2Weight b 3 = 1) ∧
    (∀ b, ∀ i : Fin Tag.F4.rank, (i = 1 ∨ i = 2) →
      f4B2Weight b ≠ Pi.single i 1 ∧ f4B2Weight b ≠ -Pi.single i 1) ∧
    (∀ j j' : Fin 4, j < j' → height (f4B2Weight j') < height (f4B2Weight j)) ∧
    (Pi.single (1 : Fin Tag.F4.rank) 1 : Fin Tag.F4.rank → ℤ) = f4B2Weight 1 - f4B2Weight 2 ∧
    (Pi.single (2 : Fin Tag.F4.rank) 1 : Fin Tag.F4.rank → ℤ) = f4B2Weight 0 - f4B2Weight 1 := by
  decide +kernel

theorem isSliceBlock_f4B2Weight : IsSliceBlock f4B2J f4B2Weight where
  isRoot b := isRoot_of_idx (f4B2Idx_spec b).1 (f4B2Idx_spec b).2
  injective := by
    intro a b h
    revert a b
    decide
  slice := by
    refine ⟨![0, 0, 0, 1], fun b s hs => ?_, fun γ hγ hs => ?_⟩
    · have h2 : s = 0 ∨ s = 3 := by
        rw [mem_f4B2J] at hs
        revert s
        decide
      obtain ⟨e0, e3⟩ := f4B2_checks.1 b
      rcases h2 with rfl | rfl
      · exact e0
      · exact e3
    · obtain ⟨k, rfl⟩ := isRoot_F4_iff.1 hγ
      exact f4B2_slice k (hs 0 (by rw [mem_f4B2J]; decide)) (hs 3 (by rw [mem_f4B2J]; decide))
  ne_single b i hi := f4B2_checks.2.1 b i hi
  precedes j j' h := precedes_of_height_lt _ _ (f4B2_checks.2.2.1 j j' h)
  simple i hi := by
    rcases hi with rfl | rfl
    · exact ⟨1, 2, f4B2_checks.2.2.2.1⟩
    · exact ⟨0, 1, f4B2_checks.2.2.2.2⟩

theorem f4B2_coeff_x1 : ∀ k : Fin 4, xCoeff f4B2Weight
    (fun b => Tag.F4.stringData.up (f4B2Idx b) 1)
    (fun b => Tag.F4.stringData.down (f4B2Idx b) 1) 1 k =
      ![1, !![0, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 0; 0, 0, 0, 0],
        !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0], 0] k := by
  decide +kernel

theorem f4B2_coeff_y1 : ∀ k : Fin 4, yCoeff f4B2Weight
    (fun b => Tag.F4.stringData.up (f4B2Idx b) 1)
    (fun b => Tag.F4.stringData.down (f4B2Idx b) 1) 1 k =
      ![1, !![0, 0, 0, 0; 0, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 0],
        !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0], 0] k := by
  decide +kernel

theorem f4B2_coeff_x2 : ∀ k : Fin 4, xCoeff f4B2Weight
    (fun b => Tag.F4.stringData.up (f4B2Idx b) 2)
    (fun b => Tag.F4.stringData.down (f4B2Idx b) 2) 2 k =
      ![1, !![0, 1, 0, 0; 0, 0, 0, 0; 0, 0, 0, 1; 0, 0, 0, 0],
        !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0], 0] k := by
  decide +kernel

theorem f4B2_coeff_y2 : ∀ k : Fin 4, yCoeff f4B2Weight
    (fun b => Tag.F4.stringData.up (f4B2Idx b) 2)
    (fun b => Tag.F4.stringData.down (f4B2Idx b) 2) 2 k =
      ![1, !![0, 0, 0, 0; 1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 1, 0],
        !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0], 0] k := by
  decide +kernel

@[expose] def f4B2Pos : Fin 4 → Fin Tag.F4.rank → ℤ :=
  (![![0, 0, 1, 0], ![0, 1, 0, 0], ![0, 1, 1, 0], ![0, 1, 2, 0]] : Fin 4 → Fin 4 → ℤ)

theorem f4B2Pos_checks :
    (∀ a, ∃ k : Fin 48, Tag.F4.rootCertificate.root k = f4B2Pos a) ∧
    (∀ a, f4B2Pos a 0 = 0 ∧ f4B2Pos a 3 = 0 ∧ 0 < height (f4B2Pos a)) ∧
    (∀ k : Fin 48, Tag.F4.rootCertificate.root k 0 = 0 → Tag.F4.rootCertificate.root k 3 = 0 →
      0 < height (Tag.F4.rootCertificate.root k) →
        ∃ a, f4B2Pos a = Tag.F4.rootCertificate.root k) ∧
    Function.Injective f4B2Pos ∧
    f4B2Pos 0 = Pi.single 2 1 ∧ f4B2Pos 1 = Pi.single 1 1 ∧
    f4B2Pos 2 = reflect Tag.F4 1 (Pi.single 2 1) ∧
    f4B2Pos 3 = reflect Tag.F4 2 (Pi.single 1 1) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ?_, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel⟩
  intro a b h
  revert a b
  decide

end CFSG.RankThree.Chevalley.SteinbergBN
