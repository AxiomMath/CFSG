module

public import CFSG.LocalAnalysis.StandardType.GGSixPositionDefs

public section

namespace CFSG.StandardType

open CFSG.StandardType.S2MathFi1035Pos CFSG.Open CFSG.LieType.Universal

@[expose] def StandardReturnAt (M : LieUniversal) (g : ℕ) : Prop :=
  (∃ (t : StatedLieTag) (n : ℕ), GGPosTag t ∧ StatedLieAdmissible t n 2 g ∧ M = ggU t n g) ∨
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (σ : F →+* F),
      TriField F σ g ∧ M = triD4Universal F σ

structure PinnedReturnAt {X Y : Type} [Group X] [Group Y]
    (M : LieUniversal) (g : ℕ) (K B : Subgroup X) (η : K →* Y) (P0 Pm0 : Subgroup Y) where
  model_at : StandardReturnAt M g
  beta : Fin M.D.rank → ℤ
  root_mem : beta ∈ M.D.roots
  long : GGLongRoot M.D beta
  cover : M.K →* K
  surj : Function.Surjective cover
  central : cover.ker ≤ Subgroup.center M.K
  positive : (M.D.rootGroup beta).map (η.comp cover) = P0
  negative : (M.D.rootGroup (-beta)).map (η.comp cover) = Pm0

@[expose] def PinnedReturnAt.ClassicalAction
    {X Y : Type} [Group X] [Group Y]
    {M : LieUniversal} {g : ℕ} {K B : Subgroup X} {η : K →* Y} {P0 Pm0 : Subgroup Y}
    (D : PinnedReturnAt M g K B η P0 Pm0) : Prop :=
  ∀ b ∈ B, GGPsiInnerDiag M.D (K.subtype.comp D.cover) b

@[expose] def PinnedReturnAt.PairConclusion
    {X Y : Type} [Group X] [Group Y]
    {M : LieUniversal} {g : ℕ} {K B : Subgroup X} {η : K →* Y} {P0 Pm0 : Subgroup Y}
    (D : PinnedReturnAt M g K B η P0 Pm0) (R Rm : Subgroup X) : Prop :=
  ∃ u : M.K, R = ggRootSub M.D (K.subtype.comp D.cover) D.beta u ∧
    Rm = ggRootSub M.D (K.subtype.comp D.cover) (-D.beta) u

theorem rootPairVia_of_pairConclusion
    {X Y : Type} [Group X] [Group Y]
    {M : LieUniversal} {g : ℕ} {K B : Subgroup X} {η : K →* Y} {P0 Pm0 : Subgroup Y}
    (D : PinnedReturnAt M g K B η P0 Pm0) (R Rm : Subgroup X)
    (h : D.PairConclusion R Rm) : GGRootPairVia M K R Rm D.beta := by
  obtain ⟨u, hR, hRm⟩ := h
  refine ⟨K.subtype.comp D.cover, ?_, ?_, u, hR, hRm⟩
  · ext x
    constructor
    · rintro ⟨w, rfl⟩
      exact (D.cover w).2
    · intro hx
      obtain ⟨w, hw⟩ := D.surj ⟨x, hx⟩
      exact ⟨w, by rw [MonoidHom.comp_apply, hw]; rfl⟩
  · intro w hw
    apply D.central
    exact Subtype.ext (by simpa using hw)

theorem rootVia_of_pairConclusion
    {X Y : Type} [Group X] [Group Y]
    {M : LieUniversal} {g : ℕ} {K B : Subgroup X} {η : K →* Y} {P0 Pm0 : Subgroup Y}
    (D : PinnedReturnAt M g K B η P0 Pm0) (R Rm : Subgroup X)
    (h : D.PairConclusion R Rm) : GGRootVia M K R D.beta := by
  obtain ⟨φ, hrange, hker, u, hR, -⟩ := rootPairVia_of_pairConclusion D R Rm h
  exact ⟨φ, hrange, hker, u, hR⟩

end CFSG.StandardType
