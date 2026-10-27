module

public import CFSG.LocalAnalysis.WeakClosure81.W183B2Fin
public import CFSG.LocalAnalysis.WeakClosure81.W183Br1Diag
public import CFSG.LocalAnalysis.WeakClosure81.W18Asch5

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL3 IsAlt)

@[expose] def FinG11Cov : Prop :=
  ∀ (X : Type) [Group X], CFSG.Open.IsQuasisimple X → Nat.card ↥(Subgroup.center X) = 3 →
    (IsL3 (X ⧸ Subgroup.center X) 2 ∨ IsAlt (X ⧸ Subgroup.center X) 6) → AbsIrrOverF4 X

@[expose] def CorConfigIn (G₀ : Type*) [Group G₀] (A₀ P : Subgroup G₀) : Prop :=
  ∃ (A' : Subgroup G₀) (S : Set (Subgroup G₀)) (y : G₀),
    (∃ g : G₀, A' = A₀.map (MulAut.conj g).toMonoidHom) ∧
    (∀ X ∈ S, ∃ g : G₀, X = A₀.map (MulAut.conj g).toMonoidHom) ∧
    A₀.map (MulAut.conj y).toMonoidHom ≠ A₀ ∧
    (∀ s ∈ A₀, ∃ z ∈ Subgroup.closure (⋃ X ∈ S, (X : Set G₀)), y * s * y⁻¹ = s * z) ∧
    ¬ A₀ ≤ Subgroup.normalizer (A' : Set G₀) ∧
    (∀ X ∈ S, X = A' ∨ ∀ a ∈ A', ∀ x ∈ X, a * x = x * a) ∧
    A' ≤ P ∧ (∀ X ∈ S, X ≤ P) ∧ y ∈ P

@[expose] def FinG1Syl : Prop :=
  ∀ (G₀ : Type) [Group G₀], LieModel G₀ .PSL 3 2 2 →
    ∀ A₀ : Subgroup G₀, Nat.card A₀ = 4 → IsElemAbelian 2 A₀ → IsTISub G₀ A₀ →
      ∃ P : Subgroup G₀, IsPGroup 2 P ∧ A₀ ≤ P ∧ CorConfigIn G₀ A₀ P

theorem finG1_of_finG1Syl (h : FinG1Syl) : FinG1 := by
  intro G₀ inst hL A₀ hcard hel hTI
  obtain ⟨P, -, -, A', S, y, h1, h2, h3, h4, h5, h6, -, -, -⟩ := h G₀ hL A₀ hcard hel hTI
  exact ⟨A', S, y, h1, h2, h3, h4, h5, h6⟩

structure Br3Rows : Prop where
  a6 : FinA6
  g1 : FinG1
  g1syl : FinG1Syl
  g3 : FinG3
  g4l34 : FinG4L34
  g4a6 : FinG4A6
  h65o : Asch6_5Odd
  h65f : Asch6_5Four
  h210 : Asch2_10
  g11cov : FinG11Cov

end CFSG.LocalAnalysis.WeakClosure81

end
