module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IModel

public section

namespace CFSG.StandardType.RCKK1IIISp

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.RCKRP
  CFSG.StandardType.LieOddCover
open CFSG.Open (StatedLieTag StatedLieAdmissible)

private theorem rckK1IIISpM_markTag_PSp {lab : LargeEvenLabel}
    (h : lab.tag = .B ∨ lab.tag = .C) : markTag lab = .PSp := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at h
  rcases h with h | h <;> simp [markTag, h]

private theorem rckK1IIISpM_markChar_two {lab : LargeEvenLabel}
    (h : lab.tag = .B ∨ lab.tag = .C) : markChar lab = 2 := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at h
  rcases h with h | h <;> simp [markChar, h]

private theorem rckK1IIISpM_markDeg_eq_n {lab : LargeEvenLabel}
    (h : lab.tag = .B ∨ lab.tag = .C) : markDeg lab = lab.n := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at h
  rcases h with h | h <;> simp [markDeg, h]

private theorem rckK1IIISpM_n_eq_one {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hP : ggSixRCKLabelRow lab = .III ∧ (lab.tag = .B ∨ lab.tag = .C)) : lab.n = 1 := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, -⟩ := hlab
  dsimp only at hn
  cases t
  case B =>
    have hrow := hP.1
    dsimp only [ggSixRCKLabelRow] at hrow
    by_cases h2 : 2 ≤ n
    · rw [if_pos h2] at hrow
      exact absurd hrow (by decide)
    · dsimp only
      omega
  case C =>
    have hrow := hP.1
    dsimp only [ggSixRCKLabelRow] at hrow
    by_cases h2 : 2 ≤ n
    · rw [if_pos h2] at hrow
      exact absurd hrow (by decide)
    · dsimp only
      omega
  all_goals (exfalso; dsimp only at hP; exact absurd hP.2 (by decide))

private theorem rckK1IIISpM_three_le_markRank {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab)
    (hP : ggSixRCKLabelRow lab = .III ∧ (lab.tag = .B ∨ lab.tag = .C)) :
    3 ≤ markRank lab := by
  obtain ⟨t, l, n⟩ := lab
  have hn1 : n = 1 := rckK1IIISpM_n_eq_one hlab hP
  obtain ⟨-, hl⟩ := hlab
  cases t
  case B =>
    dsimp only at hl
    obtain ⟨hl1, hl2⟩ := hl
    have hl3 : 3 ≤ l := by
      have hne : l ≠ 2 := by
        intro h
        have := hl2 h
        omega
      omega
    simpa [markRank] using hl3
  case C =>
    dsimp only at hl
    obtain ⟨hl1, hl2⟩ := hl
    have hl3 : 3 ≤ l := by
      have hne : l ≠ 2 := by
        intro h
        have := hl2 h
        omega
      omega
    simpa [markRank] using hl3
  all_goals (exfalso; dsimp only at hP; exact absurd hP.2 (by decide))

private theorem rckK1IIISpM_rawDatum_imp {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hP : ggSixRCKLabelRow lab = .III ∧ (lab.tag = .B ∨ lab.tag = .C))
    {Q Q' : LargeEvenRawCont}
    (hQQ' : ∀ (R : Type) [Group R] (I F : Set (MulAut R)),
      Q R I F → MarkedModel lab R → Q' R I F)
    (h : CFSG.Assembly.LargeEvenRawDatum lab Q) :
    CFSG.Assembly.LargeEvenRawDatum lab Q' := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, hl⟩ := hlab
  cases t
  case B =>
    dsimp only [CFSG.Assembly.LargeEvenRawDatum, MarkedModel, markTag, markRank,
      markChar, markDeg] at h hQQ' ⊢
    dsimp only at hl
    obtain ⟨hl1, hl2⟩ := hl
    refine recipeSymplectic_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    refine Or.inl ⟨by decide, statedClassicalModel_symplectic l n hK
      ⟨Nat.prime_two, hn, hl1, fun h => ?_⟩⟩
    simp only [Prod.mk.injEq] at h
    have := four_le_two_pow (hl2 h.1)
    omega
  case C =>
    dsimp only [CFSG.Assembly.LargeEvenRawDatum, MarkedModel, markTag, markRank,
      markChar, markDeg] at h hQQ' ⊢
    dsimp only at hl
    obtain ⟨hl1, hl2⟩ := hl
    refine recipeSymplectic_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    refine Or.inl ⟨by decide, statedClassicalModel_symplectic l n hK
      ⟨Nat.prime_two, hn, hl1, fun h => ?_⟩⟩
    simp only [Prod.mk.injEq] at h
    have := four_le_two_pow (hl2 h.1)
    omega
  all_goals (exfalso; dsimp only at hP; exact absurd hP.2 (by decide))

theorem rckK1IIISp_model
    (hcov : GGLieOddCover) {Jb : Type} [Group Jb] [Finite Jb]
    (hodd : Odd (Nat.card (Subgroup.center Jb)))
    (hmark : LargeEvenMarking Jb (fun lab _ _ _ _ _ =>
      ggSixRCKLabelRow lab = .III ∧ (lab.tag = .B ∨ lab.tag = .C))) :
    ∃ (m : ℕ) (φ : (ggU .PSp m 1).K →* Jb), 3 ≤ m ∧ Function.Surjective φ ∧
      φ.ker ≤ Subgroup.center (ggU .PSp m 1).K := by
  obtain ⟨hcomm, lab, hlab, hraw⟩ := hmark
  obtain ⟨R₀, _, I₀, F₀, hq₀⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, -, hθ₀⟩ := hq₀
  obtain ⟨-, hP⟩ := hθ₀
  have hraw' : LargeEvenRawDatum lab (fun R _ I F =>
      (IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ θ : Jb ⧸ Subgroup.center Jb ≃* R,
          ggSixRCKLabelRow lab = .III ∧ (lab.tag = .B ∨ lab.tag = .C)) ∧
      MarkedModel lab R) :=
    rckK1IIISpM_rawDatum_imp hlab hP (fun R _ I F hq hm => ⟨hq, hm⟩) hraw
  obtain ⟨R, _, I, F, hq⟩ := largeEvenRawDatum_exists hraw'
  obtain ⟨hq', hm'⟩ := hq
  obtain ⟨hs, hna, hθ⟩ := hq'
  obtain ⟨θ, -⟩ := hθ
  have hMc : MarkedModel lab (Jb ⧸ Subgroup.center Jb) := MarkedModel.of_mulEquiv θ.symm hm'
  have hchar : markChar lab = 2 := rckK1IIISpM_markChar_two hP.2
  have hMc2 : LieModel (Jb ⧸ Subgroup.center Jb) (markTag lab) (markRank lab) 2 (markDeg lab) := by
    have h := hMc
    unfold MarkedModel at h
    rwa [hchar] at h
  have hTag : markTag lab = .PSp := rckK1IIISpM_markTag_PSp hP.2
  have hDeg : markDeg lab = 1 := by
    rw [rckK1IIISpM_markDeg_eq_n hP.2, rckK1IIISpM_n_eq_one hlab hP]
  have hMc2' : LieModel (Jb ⧸ Subgroup.center Jb) .PSp (markRank lab) 2 1 := by
    rwa [hTag, hDeg] at hMc2
  have hadm : StatedLieAdmissible .PSp (markRank lab) 2 1 := LieModel.admissible hMc2'
  have hpos : GGPosTag .PSp := by simp [GGPosTag]
  obtain ⟨φ, hsurj, hker⟩ := hcov.1 .PSp (markRank lab) 1 hpos hadm Jb hcomm hodd hMc2'
  exact ⟨markRank lab, φ, rckK1IIISpM_three_le_markRank hlab hP, hsurj, hker⟩

end CFSG.StandardType.RCKK1IIISp
