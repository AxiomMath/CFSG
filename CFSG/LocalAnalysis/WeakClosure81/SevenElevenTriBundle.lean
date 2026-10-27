module

public import CFSG.LocalAnalysis.WeakClosure81.OddTranspListTriality

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

@[expose] def OddTranspositionListInputTri : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (s : X), orderOf s = 2 →
    CFSG.Timmesfeld.Bridge.Asc72.IsOddTransp {x : X | IsConj s x} →
    Subgroup.normalClosure ({s} : Set X) = ⊤ → CFSG.pCore 2 X = ⊥ →
    fusionOddCore X ≤ Subgroup.center X →
    (∃ m n : ℕ,
      (IsSpGp (X ⧸ Subgroup.center X) m n ∧ IsSymplecticTransvection X m n s) ∨
      (IsPSUGp (X ⧸ Subgroup.center X) m n ∧ IsUnitaryTransvection X m n s) ∨
      IsOrthGp (X ⧸ Subgroup.center X) m n ∨ IsL2WrSymGp (X ⧸ Subgroup.center X) n m) ∨
    (∃ n : ℕ, IsSymGp (X ⧸ fusionOddCore X) n) ∨
    IsThreeCoverOrth6Minus X ∨
    (∃ L : Subgroup X, s ∈ L ∧
      IsSevenNineGroup ↥L {x : ↥L | (x : X) ∈ Subgroup.zpowers s ∧ x ≠ 1}) ∨
    (∃ n : ℕ, 1 < n ∧ CFSG.Quasithin.IsSz n (X ⧸ fusionZStar X)) ∨
    IsTrialityOddTransp (X ⧸ Subgroup.center X) (QuotientGroup.mk s)

theorem OddTranspositionListInputClsTri.toInput (h : OddTranspositionListInputClsTri) :
    OddTranspositionListInputTri := by
  intro X _ _ s hord hodd hncl hpc hOZ
  rcases h X s hord hodd hncl hpc hOZ with hAlt | hTri
  · rcases hAlt with ⟨m, n, h1 | h2 | h3 | h4⟩ | ⟨n, h5⟩ | h6 | h7 | h8
    · exact Or.inl ⟨m, n, Or.inl h1⟩
    · exact Or.inl ⟨m, n, Or.inr (Or.inl h2)⟩
    · exact Or.inl ⟨m, n, Or.inr (Or.inr (Or.inl (isOrthGp_of_isOrthReflection h3)))⟩
    · exact Or.inl ⟨m, n, Or.inr (Or.inr (Or.inr (isL2WrSymGp_of_isWreathTransposition h4)))⟩
    · exact Or.inr (Or.inl ⟨n, isSymGp_of_isSymTransposition h5⟩)
    · exact Or.inr (Or.inr (Or.inl (isThreeCoverOrth6Minus_of_isOrth63Reflection h6)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h7)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h8))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hTri))))

@[expose] def OddTranspListBundleCls : Prop :=
  OddTranspositionListInputClsTri ∧ TrialityMarkedInput ∧ TrialityCentralInput

@[expose] def OddTranspListBundle : Prop :=
  OddTranspositionListInputTri ∧ TrialityMarkedInput ∧ TrialityCentralInput

theorem OddTranspListBundleCls.toInput (h : OddTranspListBundleCls) : OddTranspListBundle :=
  ⟨h.1.toInput, h.2.1, h.2.2⟩

end CFSG.LocalAnalysis.WeakClosure81
