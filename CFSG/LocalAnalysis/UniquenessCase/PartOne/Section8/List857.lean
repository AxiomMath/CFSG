module

public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs2
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsAlt IsSpor)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08 (IsA6Z3 IsA7Z3 IsM22Z3)
open CFSG.LocalAnalysis.UniquenessCase.UCK (ThreeCover)

@[expose] def IsSL3PiType (X : Type) [Group X] : Prop :=
  (∃ p f : ℕ, p ^ f % 3 = 1 ∧ LieModel X .PSL 3 p f) ∨
    (∃ p f : ℕ, p ^ f % 3 = 2 ∧ LieModel X .PSU 3 p f) ∨
    (∃ p f : ℕ, p ^ f % 3 = 1 ∧
      ThreeCover (fun Y _ => LieModel Y .PSL 3 p f) X) ∨
    (∃ p f : ℕ, p ^ f % 3 = 2 ∧
      ThreeCover (fun Y _ => LieModel Y .PSU 3 p f) X)

@[expose] def List857 (X : Type) [Group X] : Prop :=
  ((∃ p f : ℕ, p ^ f % 3 = 2 ∧ LieModel X .PSL 4 p f) ∨
    (∃ p f : ℕ, p ^ f % 3 = 1 ∧ LieModel X .PSU 4 p f) ∨
    (∃ p f : ℕ, p ^ f % 3 = 2 ∧
      (LieModel X .PSL 5 p f ∨
        ThreeCover (fun Y _ => LieModel Y .PSL 5 p f) X)) ∨
    (∃ p f : ℕ, p ^ f % 3 = 1 ∧
      (LieModel X .PSU 5 p f ∨
        ThreeCover (fun Y _ => LieModel Y .PSU 5 p f) X)) ∨
    (∃ p f : ℕ, LieModel X .PSp 2 p f) ∨
    IsSpor X .M11 ∨ IsSpor X .M22 ∨ IsSpor X .M23 ∨ IsSpor X .HS ∨
    IsAlt X 7 ∨ IsAlt X 6) ∨
    (IsA6Z3 X ∨ IsA7Z3 X ∨ IsM22Z3 X) ∨
    (LieModel X .PSL 3 3 1 ∨ (∃ p f : ℕ, LieModel X .G2 0 p f) ∨
      LieModel X .PSU 3 3 1 ∨
      (∃ p f : ℕ, LieModel X .trialityD4 0 p f) ∨
      (∃ f : ℕ, LieModel X .twistedF4 0 2 f) ∨
      LieModel X .Tits 0 2 1 ∨
      IsSpor X .J2 ∨ IsSpor X .He ∨ IsSpor X .Ru ∨ IsSpor X .J4 ∨
      IsSpor X .M12 ∨ IsSpor X .M24)

theorem list857_of_K33
    (h33 : CFSG.LocalAnalysis.UniquenessCase.UCK.K33)
    {X : Type} [Group X] [Finite X]
    (hQ : CFSG.Open.IsQuasisimple X) (hcat : CFSG.Open.IsCatalogGroup (X ⧸ Subgroup.center X))
    (hZ : IsPGroup 3 (Subgroup.center X)) (hr : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 2)
    (hnotSL3 : ¬ IsSL3PiType X) :
    List857 X := by
  have h := h33 X hQ hcat hZ hr
  rcases h with h1 | h2 | h3 | h4 | h5
  ·
    rcases h1 with hA6 | hA7 | hM22 | ⟨p, f, hmod, hcov⟩ | ⟨p, f, hmod, hcov⟩
    · have h' : IsA6Z3 X :=
        ⟨CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hA6.1, hA6.2.1, hA6.2.2⟩
      unfold List857
      simp [h']
    · have h' : IsA7Z3 X :=
        ⟨CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hA7.1, hA7.2.1, hA7.2.2⟩
      unfold List857
      simp [h']
    · have h' : IsM22Z3 X :=
        ⟨CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hM22.1, hM22.2.1, hM22.2.2⟩
      unfold List857
      simp [h']
    · exact absurd (by
        unfold IsSL3PiType
        exact Or.inr (Or.inr (Or.inl ⟨p, f, hmod, hcov⟩))) hnotSL3
    · exact absurd (by
        unfold IsSL3PiType
        exact Or.inr (Or.inr (Or.inr ⟨p, f, hmod, hcov⟩))) hnotSL3
  ·
    rcases h2 with hA7 | hA6
    · unfold List857
      simp [hA7]
    · unfold List857
      simp [hA6]
  ·
    rcases h3 with hL3 | hU3
    · unfold List857
      simp [hL3]
    · unfold List857
      simp [hU3]
  ·
    rcases h4 with ⟨p, f, hmod, hm⟩ | ⟨p, f, hmod, hm⟩ | ⟨p, f, hm⟩ | ⟨p, f, hm⟩ |
      ⟨p, f, hm⟩ | ⟨f, hm⟩ | hm | ⟨p, f, hmod, hm⟩ | ⟨p, f, hmod, hm⟩ |
      ⟨p, f, hmod, hm⟩ | ⟨p, f, hmod, hm⟩
    · exact absurd (by
        unfold IsSL3PiType
        exact Or.inl ⟨p, f, hmod, hm⟩) hnotSL3
    · exact absurd (by
        unfold IsSL3PiType
        exact Or.inr (Or.inl ⟨p, f, hmod, hm⟩)) hnotSL3
    · have h' : ∃ p f : ℕ, LieModel X .PSp 2 p f := ⟨p, f, hm⟩
      unfold List857
      simp [h']
    · have h' : ∃ p f : ℕ, LieModel X .G2 0 p f := ⟨p, f, hm⟩
      unfold List857
      simp [h']
    · have h' : ∃ p f : ℕ, LieModel X .trialityD4 0 p f := ⟨p, f, hm⟩
      unfold List857
      simp [h']
    · have h' : ∃ f : ℕ, LieModel X .twistedF4 0 2 f := ⟨f, hm⟩
      unfold List857
      simp [h']
    · unfold List857
      simp [hm]
    · have h' : ∃ p f : ℕ, p ^ f % 3 = 2 ∧ LieModel X .PSL 4 p f := ⟨p, f, hmod, hm⟩
      unfold List857
      simp [h']
    · have h' : ∃ p f : ℕ, p ^ f % 3 = 1 ∧ LieModel X .PSU 4 p f := ⟨p, f, hmod, hm⟩
      unfold List857
      simp [h']
    · have h' : ∃ p f : ℕ, p ^ f % 3 = 2 ∧
          (LieModel X .PSL 5 p f ∨
            ThreeCover (fun Y _ => LieModel Y .PSL 5 p f) X) :=
        ⟨p, f, hmod, Or.inl hm⟩
      unfold List857
      simp [h']
    · have h' : ∃ p f : ℕ, p ^ f % 3 = 1 ∧
          (LieModel X .PSU 5 p f ∨
            ThreeCover (fun Y _ => LieModel Y .PSU 5 p f) X) :=
        ⟨p, f, hmod, Or.inl hm⟩
      unfold List857
      simp [h']
  ·
    obtain ⟨s, hs, hsp⟩ := h5
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      unfold List857
      simp [hsp]

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
