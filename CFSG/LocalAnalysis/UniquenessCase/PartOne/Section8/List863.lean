module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.List857

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Bar2 IsAlt IsSpor)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08 (IsA6Z3 IsA7Z3 IsM22Z3)
open CFSG.LocalAnalysis.UniquenessCase.UCK (ThreeCover)

@[expose] def List857Clause1 (X : Type) [Group X] : Prop :=
  (∃ p f : ℕ, p ^ f % 3 = 2 ∧ LieModel X .PSL 4 p f) ∨
    (∃ p f : ℕ, p ^ f % 3 = 1 ∧ LieModel X .PSU 4 p f) ∨
    (∃ p f : ℕ, p ^ f % 3 = 2 ∧
      (LieModel X .PSL 5 p f ∨
        ThreeCover (fun Y _ => LieModel Y .PSL 5 p f) X)) ∨
    (∃ p f : ℕ, p ^ f % 3 = 1 ∧
      (LieModel X .PSU 5 p f ∨
        ThreeCover (fun Y _ => LieModel Y .PSU 5 p f) X)) ∨
    (∃ p f : ℕ, LieModel X .PSp 2 p f) ∨
    IsSpor X .M11 ∨ IsSpor X .M22 ∨ IsSpor X .M23 ∨ IsSpor X .HS ∨
    IsAlt X 7 ∨ IsAlt X 6

@[expose] def List857Clause2 (X : Type) [Group X] : Prop :=
  IsA6Z3 X ∨ IsA7Z3 X ∨ IsM22Z3 X

@[expose] def List857Clause3 (X : Type) [Group X] : Prop :=
  LieModel X .PSL 3 3 1 ∨ (∃ p f : ℕ, LieModel X .G2 0 p f) ∨
    LieModel X .PSU 3 3 1 ∨
    (∃ p f : ℕ, LieModel X .trialityD4 0 p f) ∨
    (∃ f : ℕ, LieModel X .twistedF4 0 2 f) ∨
    LieModel X .Tits 0 2 1 ∨
    IsSpor X .J2 ∨ IsSpor X .He ∨ IsSpor X .Ru ∨ IsSpor X .J4 ∨
    IsSpor X .M12 ∨ IsSpor X .M24

theorem list857_iff_clauses {X : Type} [Group X] :
    List857 X ↔ List857Clause1 X ∨ List857Clause2 X ∨ List857Clause3 X := by
  unfold List857 List857Clause1 List857Clause2 List857Clause3
  exact Iff.rfl

@[expose] def List863 (X : Type) [Group X] : Prop :=
  IsSpor X .Ru ∨ IsSpor X .J4 ∨ LieModel X .G2 0 5 1 ∨ LieModel X .G2 0 7 1 ∨
    LieModel X .G2 0 17 1

@[expose] def List864 {G : Type} [Group G] [Finite G] (L X P : Subgroup G) : Prop :=
  ((IsA6Z3 (Bar2 L) ∨ IsA7Z3 (Bar2 L) ∨ IsM22Z3 (Bar2 L)) ∧
      ⁅L, X⁆ ≤ CFSG.Open.pCoreOf 2 L) ∨
    ((LieModel (Bar2 L) .PSL 3 3 1 ∨ IsSpor (Bar2 L) .M12 ∨
        IsSpor (Bar2 L) .M24 ∨ LieModel (Bar2 L) .PSU 3 3 1) ∧
      ⁅L, X⁆ ≤ CFSG.Open.pCoreOf 2 L) ∨
    (List863 (Bar2 L) ∧ ⁅L, X⁆ ≤ CFSG.Open.pCoreOf 2 L) ∨
    ((LieModel (Bar2 L) .PSU 3 3 1 ∨ IsSpor (Bar2 L) .J2 ∨
        ∃ p f : ℕ, LieModel (Bar2 L) .G2 0 p f) ∧
      ¬ (⁅L, X⁆ ≤ CFSG.Open.pCoreOf 2 L) ∧
      X ≤ (Subgroup.center ↥P).map P.subtype)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
