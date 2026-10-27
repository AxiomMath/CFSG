module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IDefs

public section

namespace CFSG.StandardType.RCKK1I

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.RCKRP
  CFSG.StandardType.LieOddCover
open CFSG.Open (StatedLieTag StatedLieAdmissible)
open CFSG.StandardType.RCKSmall (RCKSmallTag)

private theorem rckK1Im_rawDatum_imp {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hrow : ggSixRCKLabelRow lab = .I) (hns : ¬ RCKSmallTag lab.tag)
    {Q Q' : LargeEvenRawCont}
    (hQQ' : ∀ (R : Type) [Group R] (I F : Set (MulAut R)),
      Q R I F → MarkedModel lab R → Q' R I F)
    (h : CFSG.Assembly.LargeEvenRawDatum lab Q) :
    CFSG.Assembly.LargeEvenRawDatum lab Q' := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, hl⟩ := hlab
  cases t
  all_goals dsimp only [CFSG.Assembly.LargeEvenRawDatum, MarkedModel, markTag, markRank,
    markChar, markDeg] at hn hl h hQQ' ⊢
  case A =>
    obtain ⟨hl1, hl2⟩ := hl
    refine recipeLinear_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    refine Or.inl ⟨by decide, statedClassicalModel_linear (l + 1) n hK
      ⟨Nat.prime_two, hn, by omega, fun h => ?_, fun h => ?_⟩⟩
    · simp only [Prod.mk.injEq] at h
      have := four_le_two_pow (hl2 (by omega))
      omega
    · simp only [Prod.mk.injEq] at h
      exact two_pow_ne_three n h.2
  case twA =>
    obtain ⟨hl1, hl2⟩ := hl
    refine recipeUnitary_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    refine Or.inl ⟨by decide, statedClassicalModel_unitary (l + 1) n hK
      ⟨Nat.prime_two, hn, by omega, fun h => ?_⟩⟩
    simp only [Prod.mk.injEq] at h
    have := four_le_two_pow (hl2 (by omega))
    omega
  case B =>
    obtain ⟨hl1, hl2⟩ := hl
    refine recipeSymplectic_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    refine Or.inl ⟨by decide, statedClassicalModel_symplectic l n hK
      ⟨Nat.prime_two, hn, hl1, fun h => ?_⟩⟩
    simp only [Prod.mk.injEq] at h
    have := four_le_two_pow (hl2 h.1)
    omega
  case C =>
    obtain ⟨hl1, hl2⟩ := hl
    refine recipeSymplectic_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    refine Or.inl ⟨by decide, statedClassicalModel_symplectic l n hK
      ⟨Nat.prime_two, hn, hl1, fun h => ?_⟩⟩
    simp only [Prod.mk.injEq] at h
    have := four_le_two_pow (hl2 h.1)
    omega
  case D =>
    split_ifs at h hQQ' ⊢ with h3
    · refine recipeLinear_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
      exact Or.inl ⟨by decide, statedClassicalModel_linear 4 n hK
        ⟨Nat.prime_two, hn, by omega, by simp, by simp⟩⟩
    · refine recipeOmegaPlus_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
      exact Or.inl ⟨by decide, statedClassicalModel_omegaPlus l n hK
        ⟨Nat.prime_two, hn, by omega⟩⟩
  case twD =>
    split_ifs at h hQQ' ⊢ with h2 h3
    · refine recipeLinear_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
      have hK' : Nat.card K = 2 ^ (2 * n) := by rw [hK, ← pow_mul, mul_comm]
      have h4 := four_le_two_pow (n := 2 * n) (by omega)
      exact Or.inl ⟨by decide, statedClassicalModel_linear 2 (2 * n) hK'
        ⟨Nat.prime_two, by omega, le_rfl, fun h => by simp only [Prod.mk.injEq] at h; omega,
          fun h => by simp only [Prod.mk.injEq] at h; omega⟩⟩
    · refine recipeUnitary_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
      exact Or.inl ⟨by decide, statedClassicalModel_unitary 4 n hK
        ⟨Nat.prime_two, hn, by omega, by simp⟩⟩
    · refine recipeOmegaMinus_imp (fun K _ _ hK b c hbc I F hq => hQQ' _ I F hq ?_) h
      exact Or.inl ⟨by decide, statedClassicalModel_omegaMinus l n hK b c hbc
        ⟨Nat.prime_two, hn, by omega⟩⟩
  case F4 =>
    refine recipeChevalley_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    exact Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, hn, rfl⟩,
      untwistedChevalleyModel_largeEven .F4 hK⟩)
  case E6 =>
    refine recipeChevalley_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    exact Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, hn, rfl⟩,
      untwistedChevalleyModel_largeEven .E6 hK⟩)
  case E7 =>
    refine recipeChevalley_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    exact Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, hn, rfl⟩,
      untwistedChevalleyModel_largeEven .E7 hK⟩)
  case E8 =>
    refine recipeChevalley_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    exact Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, hn, rfl⟩,
      untwistedChevalleyModel_largeEven .E8 hK⟩)
  case twE6 =>
    refine recipeTwisted_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    exact Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, hn, rfl⟩,
      twistedChevalleyModel_largeEven .E6 hK⟩)
  case triD4 =>
    refine recipeTwisted_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    exact Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, hn, rfl⟩,
      twistedChevalleyModel_largeEven .D4 hK⟩)
  case B2der => simp [ggSixRCKLabelRow] at hrow
  case G2der => simp [ggSixRCKLabelRow] at hrow
  case G2 => exact absurd (by simp [RCKSmallTag]) hns
  case twB2 => exact absurd (by simp [RCKSmallTag]) hns
  case twF4 => exact absurd (by simp [RCKSmallTag]) hns
  case twF4der => exact absurd (by simp [RCKSmallTag]) hns

private theorem rckK1Im_markChar_two {lab : LargeEvenLabel}
    (hrow : ggSixRCKLabelRow lab = .I) (hns : ¬ RCKSmallTag lab.tag) : markChar lab = 2 := by
  obtain ⟨t, l, n⟩ := lab
  cases t <;> simp [markChar, ggSixRCKLabelRow, RCKSmallTag] at hrow hns ⊢

private theorem rckK1Im_pos_or_tri {lab : LargeEvenLabel}
    (hrow : ggSixRCKLabelRow lab = .I) (hns : ¬ RCKSmallTag lab.tag) :
    GGPosTag (markTag lab) ∨ markTag lab = .trialityD4 := by
  obtain ⟨t, l, n⟩ := lab
  cases t <;> simp only [markTag, ggSixRCKLabelRow, RCKSmallTag] at hrow hns ⊢
  case A => exact Or.inl (by simp [GGPosTag])
  case twA => exact Or.inl (by simp [GGPosTag])
  case B => exact Or.inl (by simp [GGPosTag])
  case C => exact Or.inl (by simp [GGPosTag])
  case D => left; split_ifs <;> simp [GGPosTag]
  case twD => left; split_ifs <;> simp [GGPosTag]
  case E6 => exact Or.inl (by simp [GGPosTag])
  case E7 => exact Or.inl (by simp [GGPosTag])
  case E8 => exact Or.inl (by simp [GGPosTag])
  case F4 => exact Or.inl (by simp [GGPosTag])
  case twE6 => exact Or.inl (by simp [GGPosTag])
  case triD4 => exact Or.inr trivial
  case G2 => exact absurd (by simp [RCKSmallTag]) hns
  case twB2 => exact absurd (by simp [RCKSmallTag]) hns
  case twF4 => exact absurd (by simp [RCKSmallTag]) hns
  case B2der => simp [ggSixRCKLabelRow] at hrow
  case G2der => simp [ggSixRCKLabelRow] at hrow
  case twF4der => exact absurd (by simp [RCKSmallTag]) hns

private theorem rckK1Im_two_le_markDeg {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hrow : ggSixRCKLabelRow lab = .I) (hns : ¬ RCKSmallTag lab.tag) : 2 ≤ markDeg lab := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, hl⟩ := hlab
  cases t
  case twD =>
    simp only [markDeg, ggSixRCKLabelRow] at hrow ⊢
    by_cases h2 : l = 2
    · rw [if_pos h2]
      have hn' : 1 ≤ n := hn
      show 2 ≤ 2 * n
      omega
    · rw [if_neg h2]
      by_cases hn2 : 2 ≤ n
      · exact hn2
      · exfalso
        simp only [if_neg hn2, if_neg h2] at hrow
        split_ifs at hrow <;> exact absurd hrow (by decide)
  case G2 => exact absurd (by simp [RCKSmallTag]) hns
  case twB2 => exact absurd (by simp [RCKSmallTag]) hns
  case twF4 => exact absurd (by simp [RCKSmallTag]) hns
  case B2der => simp [ggSixRCKLabelRow] at hrow
  case G2der => simp [ggSixRCKLabelRow] at hrow
  case twF4der => exact absurd (by simp [RCKSmallTag]) hns
  all_goals
    simp only [markDeg, ggSixRCKLabelRow] at hrow ⊢
    split_ifs at hrow <;> (first | assumption | exact absurd hrow (by decide))

private theorem rckK1Im_markRank_zero_of_tri {lab : LargeEvenLabel}
    (htri : markTag lab = .trialityD4) : markRank lab = 0 := by
  obtain ⟨t, l, n⟩ := lab
  cases t <;> simp only [markTag, markRank] at htri ⊢
  all_goals (try (split_ifs at htri)) <;> simp_all

theorem rckK1I_model
    (hcov : GGLieOddCover) {Jb : Type} [Group Jb] [Finite Jb] (hodd : Odd (Nat.card (Subgroup.center Jb)))
    (hmark : LargeEvenMarking Jb (fun lab _ _ _ _ _ => ggSixRCKLabelRow lab = .I ∧ ¬ RCKSmallTag lab.tag)) :
    (∃ (t : StatedLieTag) (n f : ℕ) (φ : (ggU t n f).K →* Jb), GGPosTag t ∧ StatedLieAdmissible t n 2 f ∧ 2 ≤ f ∧
        Function.Surjective φ ∧ φ.ker ≤ Subgroup.center (ggU t n f).K) ∨
      ∃ (F : Type) (_ : Field F) (_ : Finite F) (σ : F →+* F) (g : ℕ) (φ : (triD4Universal F σ).K →* Jb),
        TriField F σ g ∧ 2 ≤ g ∧ Function.Surjective φ ∧ φ.ker ≤ Subgroup.center (triD4Universal F σ).K := by
  obtain ⟨hcomm, lab, hlab, hraw⟩ := hmark
  obtain ⟨R₀, _, I₀, F₀, hq₀⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, -, hθ₀⟩ := hq₀
  obtain ⟨-, hP₀⟩ := hθ₀
  have hrow : ggSixRCKLabelRow lab = .I := hP₀.1
  have hns : ¬ RCKSmallTag lab.tag := hP₀.2
  have hraw' : LargeEvenRawDatum lab (fun R _ I F =>
      (IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ θ : Jb ⧸ Subgroup.center Jb ≃* R,
          ggSixRCKLabelRow lab = .I ∧ ¬ RCKSmallTag lab.tag) ∧
      MarkedModel lab R) :=
    rckK1Im_rawDatum_imp hlab hrow hns (fun R _ I F hq hm => ⟨hq, hm⟩) hraw
  obtain ⟨R, _, I, F, hq⟩ := largeEvenRawDatum_exists hraw'
  obtain ⟨hq', hm'⟩ := hq
  obtain ⟨hs, hna, hθ⟩ := hq'
  obtain ⟨θ, hP⟩ := hθ
  have hMc : MarkedModel lab (Jb ⧸ Subgroup.center Jb) := MarkedModel.of_mulEquiv θ.symm hm'
  have hchar : markChar lab = 2 := rckK1Im_markChar_two hrow hns
  have hMc2 : LieModel (Jb ⧸ Subgroup.center Jb) (markTag lab) (markRank lab) 2 (markDeg lab) := by
    have h := hMc
    unfold MarkedModel at h
    rwa [hchar] at h
  have hadm : StatedLieAdmissible (markTag lab) (markRank lab) 2 (markDeg lab) :=
    LieModel.admissible hMc2
  have hge : 2 ≤ markDeg lab := rckK1Im_two_le_markDeg hlab hrow hns
  have hpt : GGPosTag (markTag lab) ∨ markTag lab = .trialityD4 :=
    rckK1Im_pos_or_tri hrow hns
  rcases hpt with hpos | htri
  · left
    obtain ⟨φ, hsurj, hker⟩ :=
      hcov.1 (markTag lab) (markRank lab) (markDeg lab) hpos hadm Jb hcomm hodd hMc2
    exact ⟨markTag lab, markRank lab, markDeg lab, φ, hpos, hadm, hge, hsurj, hker⟩
  · right
    have hrk : markRank lab = 0 := rckK1Im_markRank_zero_of_tri htri
    have htriM : LieModel (Jb ⧸ Subgroup.center Jb) .trialityD4 0 2 (markDeg lab) := by
      have h := hMc2
      rw [htri, hrk] at h
      exact h
    obtain ⟨F, hFieldF, hFiniteF, σ, hF, φ, hsurj, hker⟩ :=
      hcov.2 (markDeg lab) (by omega) Jb hcomm hodd htriM
    exact ⟨F, hFieldF, hFiniteF, σ, markDeg lab, φ, hF, hge, hsurj, hker⟩

end CFSG.StandardType.RCKK1I
