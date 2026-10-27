module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12c4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.TypeSplit
public import CFSG.LieType.Multipliers.ThreeThreeCenter
public import CFSG.Blueprint.LieModelAPI

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.McClurg

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

private theorem classicalEvenAltG2_of_classicalModel {X : Type} [Group X]
    (hX : CFSG.IsQuasisimple X)
    {t : StatedLieTag} {m f : ℕ}
    (ht : t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaPlus ∨ t = .POmegaMinus)
    (h : StatedClassicalModel (X ⧸ Subgroup.center X) t m 2 f) :
    F12.ClassicalEvenAltG2 X := by
  have hmem : t ∈ CFSG.Blueprint.classicalTags := by
    rcases ht with rfl | rfl | rfl | rfl | rfl <;> decide
  exact Or.inl ⟨hX, t, m, f, ht, (CFSG.Blueprint.LieModel.classical_iff hmem).2 h⟩

private theorem isG2Der_of_isG2Cover
    {X : Type} [Group X] [Finite X] (hX : CFSG.Open.IsQuasisimple X)
    (hodd : Odd (Nat.card (Subgroup.center X))) {f : ℕ} (hf : 2 ≤ f)
    (h : CFSG.Quasithin.IsG2 2 f (X ⧸ Subgroup.center X)) :
    ∃ n : ℕ, F08.IsG2Der X n := by
  haveI : Group.IsPerfect X := Group.isPerfect_def.mpr hX.1
  have hZ : Subgroup.center X = ⊥ := by
    have h0 := CFSG.SectionRank.g2_even_perfect_odd_cover_trivial (f := f) h
      (QuotientGroup.mk' (Subgroup.center X)) (QuotientGroup.mk'_surjective _)
      (QuotientGroup.ker_mk' _).le (by rw [QuotientGroup.ker_mk']; exact hodd)
    rwa [QuotientGroup.ker_mk'] at h0
  have hLieK : CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X) .G2 0 2 f :=
    (CFSG.Blueprint.LieModel.chevalleyExceptional_iff (by decide)).2 ⟨rfl, h⟩
  have hLieX : CFSG.Blueprint.LieModel X .G2 0 2 f :=
    CFSG.Blueprint.LieModel.of_quotient_center hZ hLieK
  exact ⟨f, Or.inr ⟨hf, hLieX⟩⟩

private theorem isG2Der_one_of_isPSU331
    {X : Type} [Group X] [Finite X] (hX : CFSG.Open.IsQuasisimple X)
    (h : CFSG.Quasithin.IsPSU 3 3 1 (X ⧸ Subgroup.center X)) :
    ∃ n : ℕ, F08.IsG2Der X n := by
  have hLieK : CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X) .PSU 3 3 1 :=
    (CFSG.Blueprint.LieModel.classical_iff (by decide)).2 h
  have hZ := CFSG.LieType.Multipliers.center_eq_bot_of_lieModel_psu_three_three hX hLieK
  have hLieX := CFSG.Blueprint.LieModel.of_quotient_center hZ hLieK
  exact ⟨1, Or.inl ⟨rfl, hLieX⟩⟩

theorem classicalEvenAltG2Der_of_ffConclusion
    {X : Type} [Group X] [Finite X] (hX : CFSG.Open.IsQuasisimple X)
    (hodd : Odd (Nat.card (Subgroup.center X)))
    (h : CFSG.HardMathSupport.Cooperstein.Coordinator.FFConclusion (X ⧸ Subgroup.center X)) :
    ClassicalEvenAltG2Der X := by
  have hXq : CFSG.IsQuasisimple X :=
    CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hX
  obtain hS | hH | hE | hAlt :=
    CFSG.Quasithin.B69K.typeSplit_cert (K := X ⧸ Subgroup.center X) h
  ·
    rcases hS with ⟨f, h⟩ | ⟨f, h⟩ | ⟨f, h⟩ | ⟨f, h⟩ | h | h
    · exact Or.inl (classicalEvenAltG2_of_classicalModel hXq (Or.inl rfl) h)
    · exact Or.inl (classicalEvenAltG2_of_classicalModel hXq (Or.inl rfl) h)
    · exact Or.inl
        (classicalEvenAltG2_of_classicalModel hXq (Or.inr (Or.inl rfl)) h)
    · exact Or.inl
        (classicalEvenAltG2_of_classicalModel hXq (Or.inr (Or.inr (Or.inl rfl))) h)
    · exact Or.inl (Or.inr (Or.inl ⟨hXq, 5, h⟩))
    · exact Or.inl (Or.inr (Or.inl ⟨hXq, 6, h⟩))
  ·
    rcases hH with ⟨n, f, -, h⟩ | ⟨n, f, -, h⟩ | ⟨r, f, -, h⟩ | ⟨n, f, -, h⟩ |
      ⟨n, f, -, h⟩
    · exact Or.inl (classicalEvenAltG2_of_classicalModel hXq (Or.inl rfl) h)
    · exact Or.inl
        (classicalEvenAltG2_of_classicalModel hXq (Or.inr (Or.inl rfl)) h)
    · exact Or.inl
        (classicalEvenAltG2_of_classicalModel hXq (Or.inr (Or.inr (Or.inl rfl))) h)
    · exact Or.inl
        (classicalEvenAltG2_of_classicalModel hXq (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) h)
    · exact Or.inl
        (classicalEvenAltG2_of_classicalModel hXq (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) h)
  ·
    rcases hE with ⟨f, hf, h⟩ | h | h | h
    · exact Or.inr (isG2Der_of_isG2Cover hX hodd hf h)
    · exact Or.inl (Or.inr (Or.inl ⟨hXq, 7, h⟩))
    · exact Or.inl (Or.inr (Or.inl ⟨hXq, 8, h⟩))
    · exact Or.inr (isG2Der_one_of_isPSU331 hX h)
  ·
    obtain ⟨m, -, h⟩ := hAlt
    exact Or.inl (Or.inr (Or.inl ⟨hXq, m, h⟩))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.McClurg
