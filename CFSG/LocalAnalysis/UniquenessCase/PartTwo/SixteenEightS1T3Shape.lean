module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3Set
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSmallShapes

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def T3EngineBranch {W : Type} [CommGroup W] (L : Subgroup (MulAut W)) (U Z : Subgroup W)
    (k : ℕ) : Prop :=
  ∃ n : ℕ,
    (IsSLn ↥L n 1 ∧ 5 ≤ n ∧ SumOfNat (fun H U Z => BinaryNaturalSL H U Z n 1) L U Z k) ∨
    (IsSpn ↥L n 1 ∧ 6 ≤ n ∧ SumOfNat (fun H U Z => NatSpn H U Z n 1) L U Z k) ∨
    (IsOmegaPlus ↥L n 1 ∧ 6 ≤ n ∧ SumOfNat (fun H U Z => NatOmegaPlus H U Z n 1) L U Z k) ∨
    (IsOmegaMinus ↥L n 1 ∧ 8 ≤ n ∧ SumOfNat (fun H U Z => NatOmegaMinus H U Z n 1) L U Z k) ∨
    (UC22.IsAlt ↥L n ∧ 8 ≤ n ∧ SumOfNat (fun H U Z => AlternatingNatural H U Z n) L U Z k)

@[expose] def T3SpecialShape {W : Type} [CommGroup W] (L : Subgroup (MulAut W)) : Prop :=
  IsSLn ↥L 3 1 ∨ IsSLn ↥L 4 1 ∨ IsOmegaMinus ↥L 4 1 ∨ IsOmegaMinus ↥L 6 1 ∨
    UC22.IsAlt ↥L 5 ∨ UC22.IsAlt ↥L 6 ∨ UC22.IsAlt ↥L 7

theorem ThreeNat.shape_cases {W : Type} [CommGroup W] [Finite W] {A L T : Subgroup (MulAut W)}
    (h : ThreeNat A L T) : T3EngineBranch L ⊤ (fixV L) 3 ∨ T3SpecialShape L := by
  obtain ⟨n, hSL | hSp | hOP | hOM | hAlt⟩ := h.sum
  ·
    obtain ⟨hSLn, hsum⟩ := hSL
    by_cases h5 : 5 ≤ n
    · exact Or.inl ⟨n, Or.inl ⟨hSLn, h5, hsum⟩⟩
    · have hn5 : n < 5 := not_le.1 h5
      have h3 : 3 ≤ n := s16k_three_le_of_isSLn h.quasi hSLn
      rcases (by omega : n = 3 ∨ n = 4) with rfl | rfl
      · exact Or.inr (Or.inl hSLn)
      · exact Or.inr (Or.inr (Or.inl hSLn))
  ·
    obtain ⟨hSpn, hsum⟩ := hSp
    have h6 : 6 ≤ n := s16k_six_le_of_isSpn h.quasi hSpn
    exact Or.inl ⟨n, Or.inr (Or.inl ⟨hSpn, h6, hsum⟩)⟩
  ·
    obtain ⟨hOPn, hsum⟩ := hOP
    have h6 : 6 ≤ n := s16k_six_le_of_isOmegaPlus h.quasi hOPn
    exact Or.inl ⟨n, Or.inr (Or.inr (Or.inl ⟨hOPn, h6, hsum⟩))⟩
  ·
    obtain ⟨hOMn, hsum⟩ := hOM
    by_cases h8 : 8 ≤ n
    · exact Or.inl ⟨n, Or.inr (Or.inr (Or.inr (Or.inl ⟨hOMn, h8, hsum⟩)))⟩
    · have hn8 : n < 8 := not_le.1 h8
      have h4 : 4 ≤ n := s16k_four_le_of_isOmegaMinus h.quasi hOMn
      obtain ⟨r, hr⟩ := hOMn.1
      rcases (by omega : n = 4 ∨ n = 6) with rfl | rfl
      · simp only [T3SpecialShape]
        tauto
      · simp only [T3SpecialShape]
        tauto
  ·
    obtain ⟨hAltn, hsum⟩ := hAlt
    by_cases h8 : 8 ≤ n
    · exact Or.inl ⟨n, Or.inr (Or.inr (Or.inr (Or.inr ⟨hAltn, h8, hsum⟩)))⟩
    · have hn8 : n < 8 := not_le.1 h8
      have h5 : 5 ≤ n := s16k_five_le_of_isAlt h.quasi hAltn
      rcases (by omega : n = 5 ∨ n = 6 ∨ n = 7) with rfl | rfl | rfl
      · simp only [T3SpecialShape]
        tauto
      · simp only [T3SpecialShape]
        tauto
      · simp only [T3SpecialShape]
        tauto

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
