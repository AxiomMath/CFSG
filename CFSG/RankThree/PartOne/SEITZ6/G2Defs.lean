module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Blueprint.Chevalley
public import CFSG.LieType.Chevalley.LangFiniteSubfieldCongruence
public import CFSG.RankThree.PartOne.SEITZ3.Conj

public section

namespace CFSG.RankThree.PartOne.SEITZ6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.SEITZ3

variable {K : Type} [Field K]

@[expose] noncomputable def coordAt (γ : Fin (Tag.rank .G2) → ℤ) (x : RootModule .G2 K) : K :=
  open _root_.Classical in if h : IsRoot .G2 γ then x (Sum.inr ⟨γ, h⟩) else 0

theorem coordAt_eq {γ : Fin (Tag.rank .G2) → ℤ} (hγ : IsRoot .G2 γ) (x : RootModule .G2 K) :
    coordAt γ x = x (Sum.inr ⟨γ, hγ⟩) := by
  unfold coordAt
  simp [hγ]

theorem coordAt_add (γ : Fin (Tag.rank .G2) → ℤ) (x y : RootModule .G2 K) :
    coordAt γ (x + y) = coordAt γ x + coordAt γ y := by
  unfold coordAt
  split_ifs <;> simp

theorem coordAt_smul (γ : Fin (Tag.rank .G2) → ℤ) (c : K) (x : RootModule .G2 K) :
    coordAt γ (c • x) = c * coordAt γ x := by
  unfold coordAt
  split_ifs <;> simp

theorem coordAt_rootVec_self {γ : Fin (Tag.rank .G2) → ℤ} (hγ : IsRoot .G2 γ) :
    coordAt γ (rootVec .G2 K γ) = 1 := by
  unfold coordAt rootVec
  simp [hγ]

theorem coordAt_rootVec_ne {γ δ : Fin (Tag.rank .G2) → ℤ} (h : γ ≠ δ) :
    coordAt γ (rootVec .G2 K δ) = 0 := by
  classical
  unfold coordAt rootVec
  by_cases hγ : IsRoot .G2 γ <;> by_cases hδ : IsRoot .G2 δ
  · have : (⟨γ, hγ⟩ : {v // IsRoot .G2 v}) ≠ ⟨δ, hδ⟩ := fun e => h (congrArg Subtype.val e)
    simp [hγ, hδ, this]
  · simp [hγ, hδ]
  · simp [hγ]
  · simp [hγ]

theorem coordAt_hVec (γ : Fin (Tag.rank .G2) → ℤ) (i : Fin (Tag.rank .G2)) :
    coordAt γ (hVec .G2 K i) = 0 := by
  unfold coordAt hVec
  split_ifs <;> simp

end CFSG.RankThree.PartOne.SEITZ6
