module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IModel

public section

namespace CFSG.StandardType.RCKK1IIISU

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.RCKRP
  CFSG.StandardType.LieOddCover
open CFSG.Open (StatedLieTag StatedLieAdmissible)

private theorem rckSUm_not_two_le_n {lab : LargeEvenLabel}
    (hrow : ggSixRCKLabelRow lab = .III) (htag : lab.tag = .twA ∨ lab.tag = .twD) :
    ¬ 2 ≤ lab.n := by
  obtain ⟨t, l, n⟩ := lab
  rcases htag with ht | ht
  · have ht : t = .twA := ht
    subst ht
    simp only [ggSixRCKLabelRow] at hrow
    intro h2
    rw [if_pos h2] at hrow
    exact absurd hrow (by decide)
  · have ht : t = .twD := ht
    subst ht
    simp only [ggSixRCKLabelRow] at hrow
    intro h2
    rw [if_pos h2] at hrow
    exact absurd hrow (by decide)

private theorem rckSUm_twD_rank_eq_three {l n : ℕ}
    (hrow : ggSixRCKLabelRow (⟨.twD, l, n⟩ : LargeEvenLabel) = .III) : l = 3 := by
  simp only [ggSixRCKLabelRow] at hrow
  by_cases h2 : 2 ≤ n
  · rw [if_pos h2] at hrow
    exact absurd hrow (by decide)
  · rw [if_neg h2] at hrow
    by_cases hl2 : l = 2
    · rw [if_pos hl2] at hrow
      exact absurd hrow (by decide)
    · by_cases hl3 : l = 3
      · exact hl3
      · rw [if_neg hl2, if_neg hl3] at hrow
        exact absurd hrow (by decide)

private theorem rckSUm_markChar_two {lab : LargeEvenLabel}
    (htag : lab.tag = .twA ∨ lab.tag = .twD) : markChar lab = 2 := by
  obtain ⟨t, l, n⟩ := lab
  rcases htag with ht | ht
  · have ht : t = .twA := ht
    subst ht
    rfl
  · have ht : t = .twD := ht
    subst ht
    rfl

private theorem rckSUm_markTag_PSU {lab : LargeEvenLabel}
    (hrow : ggSixRCKLabelRow lab = .III) (htag : lab.tag = .twA ∨ lab.tag = .twD) :
    markTag lab = .PSU := by
  obtain ⟨t, l, n⟩ := lab
  rcases htag with ht | ht
  · have ht : t = .twA := ht
    subst ht
    rfl
  · have ht : t = .twD := ht
    subst ht
    have hl3 : l = 3 := rckSUm_twD_rank_eq_three hrow
    subst hl3
    simp [markTag]

private theorem rckSUm_markDeg_one {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hrow : ggSixRCKLabelRow lab = .III) (htag : lab.tag = .twA ∨ lab.tag = .twD) :
    markDeg lab = 1 := by
  obtain ⟨t, l, n⟩ := lab
  have hn1 : 1 ≤ n := by simpa using hlab.1
  have hn2 : ¬ 2 ≤ n := by simpa using rckSUm_not_two_le_n hrow htag
  have hneq : n = 1 := le_antisymm (Nat.le_of_lt_succ (Nat.lt_of_not_le hn2)) hn1
  rcases htag with ht | ht
  · have ht : t = .twA := ht
    subst ht
    subst hneq
    rfl
  · have ht : t = .twD := ht
    subst ht
    have hl3 : l = 3 := rckSUm_twD_rank_eq_three hrow
    subst hl3
    subst hneq
    simp [markDeg]

private theorem rckSUm_four_le_markRank {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hrow : ggSixRCKLabelRow lab = .III) (htag : lab.tag = .twA ∨ lab.tag = .twD) :
    4 ≤ markRank lab := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨-, hl⟩ := hlab
  have hn2 : ¬ 2 ≤ n := rckSUm_not_two_le_n hrow htag
  rcases htag with ht | ht
  · have ht : t = .twA := ht
    subst ht
    have hl2 : 2 ≤ l := hl.1
    have hlne : l ≠ 2 := fun h2 => hn2 (hl.2 h2)
    simp only [markRank]
    omega
  · have ht : t = .twD := ht
    subst ht
    have hl3 : l = 3 := rckSUm_twD_rank_eq_three hrow
    subst hl3
    simp only [markRank]
    split_ifs <;> omega

private theorem rckSUm_rawDatum_imp {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hrow : ggSixRCKLabelRow lab = .III) (htag : lab.tag = .twA ∨ lab.tag = .twD)
    {Q Q' : LargeEvenRawCont}
    (hQQ' : ∀ (R : Type) [Group R] (I F : Set (MulAut R)),
      Q R I F → MarkedModel lab R → Q' R I F)
    (h : LargeEvenRawDatum lab Q) :
    LargeEvenRawDatum lab Q' := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, hl⟩ := hlab
  rcases htag with ht | ht
  · have ht : t = .twA := ht
    subst ht
    dsimp only [LargeEvenRawDatum, MarkedModel, markTag, markRank, markChar, markDeg,
      ggSixRCKLabelRow] at hn hl h hQQ' hrow ⊢
    have hn2 : ¬ 2 ≤ n := by
      intro h2
      rw [if_pos h2] at hrow
      exact absurd hrow (by decide)
    have hl2 : l ≠ 2 := fun h2 => hn2 (hl.2 h2)
    refine recipeUnitary_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    refine Or.inl ⟨by decide, statedClassicalModel_unitary (l + 1) n hK
      ⟨Nat.prime_two, hn, by omega, fun h => ?_⟩⟩
    · simp only [Prod.mk.injEq] at h
      exact hl2 (by omega)
  · have ht : t = .twD := ht
    subst ht
    have hn2 : ¬ 2 ≤ n := by simpa using rckSUm_not_two_le_n hrow (Or.inr rfl)
    dsimp only [LargeEvenRawDatum, MarkedModel, markTag, markRank, markChar, markDeg,
      ggSixRCKLabelRow] at hn hl h hQQ' hrow ⊢
    rw [if_neg hn2] at hrow
    split_ifs at h hQQ' ⊢ with h2 h3
    · rw [if_pos h2] at hrow
      exact absurd hrow (by decide)
    · refine recipeUnitary_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
      refine Or.inl ⟨by decide, statedClassicalModel_unitary 4 n hK
        ⟨Nat.prime_two, hn, by omega, fun h => ?_⟩⟩
      · simp only [Prod.mk.injEq] at h
        omega
    · rw [if_neg h2, if_neg h3] at hrow
      exact absurd hrow (by decide)

theorem rckK1IIISU_model
    (hcov : GGLieOddCover) {Jb : Type} [Group Jb] [Finite Jb]
    (hodd : Odd (Nat.card (Subgroup.center Jb)))
    (hmark : LargeEvenMarking Jb (fun lab _ _ _ _ _ =>
      ggSixRCKLabelRow lab = .III ∧ (lab.tag = .twA ∨ lab.tag = .twD))) :
    ∃ (k : ℕ) (φ : (ggU .PSU k 1).K →* Jb), 4 ≤ k ∧ Function.Surjective φ ∧
      φ.ker ≤ Subgroup.center (ggU .PSU k 1).K := by
  obtain ⟨hcomm, lab, hlab, hraw⟩ := hmark
  obtain ⟨R₀, _, I₀, F₀, hq₀⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, -, hθ₀⟩ := hq₀
  obtain ⟨-, hrowIII, htag⟩ := hθ₀
  have hraw' : LargeEvenRawDatum lab (fun R _ I F =>
      (IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ θ : Jb ⧸ Subgroup.center Jb ≃* R,
          ggSixRCKLabelRow lab = .III ∧ (lab.tag = .twA ∨ lab.tag = .twD)) ∧
      MarkedModel lab R) :=
    rckSUm_rawDatum_imp hlab hrowIII htag (fun R _ I F hq hm => ⟨hq, hm⟩) hraw
  obtain ⟨R, _, I, F, hq⟩ := largeEvenRawDatum_exists hraw'
  obtain ⟨hq', hm'⟩ := hq
  obtain ⟨-, -, hθ⟩ := hq'
  obtain ⟨θ, -⟩ := hθ
  have hMc : MarkedModel lab (Jb ⧸ Subgroup.center Jb) := MarkedModel.of_mulEquiv θ.symm hm'
  have hchar : markChar lab = 2 := rckSUm_markChar_two htag
  have htagPSU : markTag lab = .PSU := rckSUm_markTag_PSU hrowIII htag
  have hdeg : markDeg lab = 1 := rckSUm_markDeg_one hlab hrowIII htag
  have hMc2 : LieModel (Jb ⧸ Subgroup.center Jb) (markTag lab) (markRank lab) 2
      (markDeg lab) := by
    have h := hMc
    unfold MarkedModel at h
    rwa [hchar] at h
  have hMc1 : LieModel (Jb ⧸ Subgroup.center Jb) .PSU (markRank lab) 2 1 := by
    rwa [htagPSU, hdeg] at hMc2
  have hadm : StatedLieAdmissible .PSU (markRank lab) 2 1 := LieModel.admissible hMc1
  have hk4 : 4 ≤ markRank lab := rckSUm_four_le_markRank hlab hrowIII htag
  obtain ⟨φ, hsurj, hker⟩ :=
    hcov.1 .PSU (markRank lab) 1 (by simp [GGPosTag]) hadm Jb hcomm hodd hMc1
  exact ⟨markRank lab, φ, hk4, hsurj, hker⟩

end CFSG.StandardType.RCKK1IIISU
