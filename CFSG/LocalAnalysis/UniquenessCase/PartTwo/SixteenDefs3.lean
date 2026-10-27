module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

section Shapes168

variable (D : Data G) (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) (L : Subgroup G)

@[expose] noncomputable def Shape168_2Alt (n : ℕ) (L₀ : Subgroup (MulAut (Vtil V₀ V hV))) :
    Prop :=
  IsSym ↥L₀ n ∧ UC22.IsAlt ↥(lBar V₀ V hV L) n ∧
    SumOfNat (fun H U Z => AlternatingNatural H U Z n)
      (lBar V₀ V hV L) (⊤ : Subgroup (Vtil V₀ V hV)) ⊥ 2

@[expose] noncomputable def Shape168_2Ln (m : ℕ) (L₀ : Subgroup (MulAut (Vtil V₀ V hV))) :
    Prop :=
  IsLn ↥L₀ m 1 ∧ IsLn ↥(lBar V₀ V hV L) m 1 ∧
    SumOfNat (fun H U Z => BinaryNaturalSL H U Z m 1)
      (lBar V₀ V hV L) (⊤ : Subgroup (Vtil V₀ V hV)) ⊥ 2

@[expose] noncomputable def Shape168_2Sp (L₀ : Subgroup (MulAut (Vtil V₀ V hV))) : Prop :=
  IsSpn ↥L₀ 6 1 ∧ IsSpn ↥(lBar V₀ V hV L) 6 1 ∧
    SumOfNat (fun H U Z => NatSpn H U Z 6 1)
      (lBar V₀ V hV L) (⊤ : Subgroup (Vtil V₀ V hV)) ⊥ 2

@[expose] noncomputable def Shape168_2OMinus (n : ℕ) (L₀ : Subgroup (MulAut (Vtil V₀ V hV))) :
    Prop :=
  IsOMinus ↥L₀ n 1 ∧ IsOmegaMinus ↥(lBar V₀ V hV L) n 1 ∧
    SumOfNat (fun H U Z => NatOmegaMinus H U Z n 1)
      (lBar V₀ V hV L) (⊤ : Subgroup (Vtil V₀ V hV)) ⊥ 2

@[expose] noncomputable def Case168_2Shape
    (S : Subgroup (MulAut (Vtil V₀ V hV)) → Prop) : Prop :=
  IsSym ↥(kBar D.M V₀ V hV L) 3 ∧
    (∃ L₀ : Subgroup (MulAut (Vtil V₀ V hV)),
      IsInternalDirect (kBar D.M V₀ V hV L) L₀ (Mbar D.M V₀ V hV) ∧ S L₀) ∧
    D.sig = {3}

theorem case168_2_iff_shape :
    Case168_2 D V₀ V hV L ↔ Case168_2Shape D V₀ V hV L (fun L₀ =>
      (∃ n : ℕ, 5 ≤ n ∧ n ≤ 11 ∧ Shape168_2Alt V₀ V hV L n L₀) ∨
        (∃ m : ℕ, 3 ≤ m ∧ m ≤ 5 ∧ Shape168_2Ln V₀ V hV L m L₀) ∨ Shape168_2Sp V₀ V hV L L₀ ∨
        Shape168_2OMinus V₀ V hV L 6 L₀ ∨ Shape168_2OMinus V₀ V hV L 8 L₀) :=
  Iff.rfl

@[expose] noncomputable def Case168_2Small : Prop :=
  Case168_2Shape D V₀ V hV L (fun L₀ =>
    Shape168_2Alt V₀ V hV L 6 L₀ ∨ Shape168_2Alt V₀ V hV L 7 L₀ ∨ Shape168_2Ln V₀ V hV L 4 L₀ ∨
      Shape168_2OMinus V₀ V hV L 6 L₀)

theorem Case168_2Small.case168_2 (h : Case168_2Small D V₀ V hV L) : Case168_2 D V₀ V hV L := by
  rw [case168_2_iff_shape]
  obtain ⟨h1, ⟨L₀, hI, hS⟩, h3⟩ := h
  refine ⟨h1, ⟨L₀, hI, ?_⟩, h3⟩
  rcases hS with h | h | h | h
  · exact Or.inl ⟨6, by norm_num, by norm_num, h⟩
  · exact Or.inl ⟨7, by norm_num, by norm_num, h⟩
  · exact Or.inr (Or.inl ⟨4, by norm_num, by norm_num, h⟩)
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))

@[expose] noncomputable def Case168_4With (r : ℕ) : Prop :=
  ∃ p : ℕ, (p = 3 ∨ p = 7) ∧ Case168_4At D V₀ V hV L p r

theorem case168_4_iff_with :
    Case168_4 D V₀ V hV L ↔ ∃ r : ℕ, 1 < r ∧ Case168_4With D V₀ V hV L r := by
  constructor
  · rintro ⟨p, r, hp, hr, h⟩
    exact ⟨r, hr, p, hp, h⟩
  · rintro ⟨r, hr, p, hp, h⟩
    exact ⟨p, r, hp, hr, h⟩

@[expose] noncomputable def Choice1613 (A : Subgroup G) : Prop :=
  A ∈ E3.gammaSet V D.k D.T ∧
    (⁅oddBar D.M V₀ V hV, barSub V₀ V hV A⁆ ≠ ⊥ ∨
      (Case168_9 D V₀ V hV L ∧ ¬ barSub V₀ V hV A ≤ stabSub (wTil V₀ V hV L)))

end Shapes168

@[expose] def deltaConj (Δ : Set (Subgroup G)) (g : G) : Set (Subgroup G) :=
  (fun I => conjSubgroup I g) '' Δ

section Notation1617

variable (D : Data G) (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) (L : Subgroup G)

@[expose] noncomputable def Concl1617 (A : Subgroup G) (g : G) (Δ : Set (Subgroup G)) : Prop :=
  Δ.ncard = 2 ∧ (∀ I ∈ Δ, I ≤ V) ∧ sSupIndep Δ ∧ sSup Δ = V ∧
    (Case168_2 D V₀ V hV L → ∀ I ∈ Δ, imgTil V₀ V hV I ∈ irrBar L V₀ V hV) ∧
    (Case168_4At D V₀ V hV L 3 3 →
      (∀ I ∈ Δ, rk ↥I = 4) ∧
        (∀ u ∈ V ⊓ conjSubgroup D.M g, ∀ J ∈ deltaConj Δ g, conjSubgroup J u ∈ deltaConj Δ g) ∧
        PairsOfConj (Mbar D.M V₀ V hV) (dParam 3) (imgTil V₀ V hV '' Δ)) ∧
    ((Case168_9 D V₀ V hV L ∨ Case168_10 D V₀ V hV L) → Δ = wConj D.M V₀ V hV L)

end Notation1617

@[expose] def Hyperplane1618 (V A B U : Subgroup G) : Prop :=
  B ≤ A ∧ E3.mQuot A B = 1 ∧ U = V ⊓ centralizer (B : Set G) ∧
    U ≠ V ⊓ centralizer (A : Set G)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
