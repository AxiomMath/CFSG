module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IModel

public section

namespace CFSG.StandardType.RCKK1II

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.RCKRP
  CFSG.StandardType.LieOddCover
open CFSG.Open (StatedLieTag StatedLieAdmissible)

@[expose] def RCKRowIIModel (t : StatedLieTag) (n : ℕ) : Prop :=
  (t = .PSL ∧ 5 ≤ n) ∨ (t = .POmegaPlus ∧ 4 ≤ n) ∨ (t = .POmegaMinus ∧ 4 ≤ n) ∨ t = .E6 ∨ t = .E7 ∨
    t = .E8 ∨ t = .F4 ∨ t = .twistedE6

@[expose] def RCKRowIIAt
    (t : StatedLieTag) (n : ℕ) : Prop :=
  ∀ (Jb : Type) [Group Jb] [Finite Jb], Odd (Nat.card (Subgroup.center Jb)) →
    ∀ φ : (ggU t n 1).K →* Jb, Function.Surjective φ → φ.ker ≤ Subgroup.center (ggU t n 1).K →
      ∃ (rb : Jb ⧸ Subgroup.center Jb) (Vb : Subgroup (Jb ⧸ Subgroup.center Jb)),
        RCKK1Data rb Vb ∧ RCKPosRootElt Jb rb Vb

@[expose] def RCKRowIIAtTri
    (F : Type) [Field F] [Finite F] (σ : F →+* F) : Prop :=
  ∀ (Jb : Type) [Group Jb] [Finite Jb], Odd (Nat.card (Subgroup.center Jb)) →
    ∀ φ : (triD4Universal F σ).K →* Jb, Function.Surjective φ →
      φ.ker ≤ Subgroup.center (triD4Universal F σ).K →
      ∃ (rb : Jb ⧸ Subgroup.center Jb) (Vb : Subgroup (Jb ⧸ Subgroup.center Jb)),
        RCKK1Data rb Vb ∧ RCKPosRootElt Jb rb Vb

private theorem rckK1IIm_not_two_le_n {lab : LargeEvenLabel}
    (hrow : ggSixRCKLabelRow lab = .II) : ¬ 2 ≤ lab.n := by
  obtain ⟨t, l, n⟩ := lab
  cases t <;> simp only [ggSixRCKLabelRow] at hrow
  all_goals
    intro h2
    first
      | (rw [if_pos h2] at hrow; exact absurd hrow (by decide))
      | exact absurd hrow (by decide)

private theorem rckK1IIm_rawDatum_imp {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hrow : ggSixRCKLabelRow lab = .II)
    {Q Q' : LargeEvenRawCont}
    (hQQ' : ∀ (R : Type) [Group R] (I F : Set (MulAut R)),
      Q R I F → MarkedModel lab R → Q' R I F)
    (h : CFSG.Assembly.LargeEvenRawDatum lab Q) :
    CFSG.Assembly.LargeEvenRawDatum lab Q' := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, hl⟩ := hlab
  cases t
  all_goals dsimp only [CFSG.Assembly.LargeEvenRawDatum, MarkedModel, markTag, markRank,
    markChar, markDeg, ggSixRCKLabelRow] at hn hl h hQQ' hrow ⊢
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
  case D =>
    split_ifs at h hQQ' ⊢ with h3
    · exfalso
      rw [if_pos h3] at hrow
      by_cases h2n : 2 ≤ n
      · rw [if_pos h2n] at hrow; exact absurd hrow (by decide)
      · rw [if_neg h2n] at hrow; exact absurd hrow (by decide)
    · refine recipeOmegaPlus_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
      exact Or.inl ⟨by decide, statedClassicalModel_omegaPlus l n hK
        ⟨Nat.prime_two, hn, by omega⟩⟩
  case twD =>
    split_ifs at h hQQ' ⊢ with h2 h3
    · exfalso
      rw [if_pos h2] at hrow
      by_cases h2n : 2 ≤ n
      · rw [if_pos h2n] at hrow; exact absurd hrow (by decide)
      · rw [if_neg h2n] at hrow; exact absurd hrow (by decide)
    · exfalso
      rw [if_neg h2, if_pos h3] at hrow
      by_cases h2n : 2 ≤ n
      · rw [if_pos h2n] at hrow; exact absurd hrow (by decide)
      · rw [if_neg h2n] at hrow; exact absurd hrow (by decide)
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
  all_goals
    exfalso
    first
      | (split_ifs at hrow <;> exact absurd hrow (by decide))
      | exact absurd hrow (by decide)

private theorem rckK1IIm_markChar_two {lab : LargeEvenLabel}
    (hrow : ggSixRCKLabelRow lab = .II) : markChar lab = 2 := by
  obtain ⟨t, l, n⟩ := lab
  cases t <;> simp only [markChar, ggSixRCKLabelRow] at hrow ⊢
  all_goals
    first
      | rfl
      | (exfalso; first
          | (split_ifs at hrow <;> exact absurd hrow (by decide))
          | exact absurd hrow (by decide))

private theorem rckK1IIm_markDeg_one {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hrow : ggSixRCKLabelRow lab = .II) : markDeg lab = 1 := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, hl⟩ := hlab
  have hn1 : 1 ≤ n := hn
  have h2 : ¬ 2 ≤ n := rckK1IIm_not_two_le_n hrow
  cases t <;> simp only [markDeg, ggSixRCKLabelRow] at hrow hl ⊢
  case twD =>
    have hl2 : l ≠ 2 := by
      intro h
      rw [if_pos h] at hrow
      by_cases h2n : 2 ≤ n
      · rw [if_pos h2n] at hrow; exact absurd hrow (by decide)
      · rw [if_neg h2n] at hrow; exact absurd hrow (by decide)
    rw [if_neg hl2]
    omega
  all_goals
    first
      | rfl
      | omega
      | (exfalso; first
          | (split_ifs at hrow <;> exact absurd hrow (by decide))
          | exact absurd hrow (by decide))

private theorem rckK1IIm_pos_or_tri {lab : LargeEvenLabel}
    (hrow : ggSixRCKLabelRow lab = .II) :
    GGPosTag (markTag lab) ∨ markTag lab = .trialityD4 := by
  obtain ⟨t, l, n⟩ := lab
  cases t <;> simp only [markTag, ggSixRCKLabelRow] at hrow ⊢
  case A => exact Or.inl (by simp [GGPosTag])
  case D => left; split_ifs <;> simp [GGPosTag]
  case twD => left; split_ifs <;> simp [GGPosTag]
  case E6 => exact Or.inl (by simp [GGPosTag])
  case E7 => exact Or.inl (by simp [GGPosTag])
  case E8 => exact Or.inl (by simp [GGPosTag])
  case F4 => exact Or.inl (by simp [GGPosTag])
  case twE6 => exact Or.inl (by simp [GGPosTag])
  case triD4 => simp
  all_goals
    exfalso
    first
      | (split_ifs at hrow <;> exact absurd hrow (by decide))
      | exact absurd hrow (by decide)

private theorem rckK1IIm_markRank_zero_of_tri {lab : LargeEvenLabel}
    (htri : markTag lab = .trialityD4) : markRank lab = 0 := by
  obtain ⟨t, l, n⟩ := lab
  cases t <;> simp only [markTag, markRank] at htri ⊢
  all_goals (try (split_ifs at htri)) <;> simp_all

private theorem rckK1IIm_model_or_tri {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hrow : ggSixRCKLabelRow lab = .II) :
    markTag lab = .trialityD4 ∨ RCKRowIIModel (markTag lab) (markRank lab) := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, hl⟩ := hlab
  cases t <;> simp only [markTag, markRank, ggSixRCKLabelRow] at hrow hl ⊢
  case A =>
    have h4 : 4 ≤ l := by
      by_contra hlt
      by_cases h2n : 2 ≤ n
      · rw [if_pos h2n] at hrow; exact absurd hrow (by decide)
      · rw [if_neg h2n] at hrow
        by_cases hl3 : l = 3
        · rw [if_pos hl3] at hrow; exact absurd hrow (by decide)
        · rw [if_neg hl3, if_neg hlt] at hrow; exact absurd hrow (by decide)
    right; left; exact ⟨rfl, by omega⟩
  case D =>
    have hl' : 3 ≤ l := hl
    have hl3 : l ≠ 3 := by
      intro h
      by_cases h2n : 2 ≤ n
      · rw [if_pos h2n] at hrow; exact absurd hrow (by decide)
      · rw [if_neg h2n, if_pos h] at hrow; exact absurd hrow (by decide)
    simp only [if_neg hl3]
    right; right; left; exact ⟨rfl, by omega⟩
  case twD =>
    have hl' : 2 ≤ l := hl
    have hl2 : l ≠ 2 := by
      intro h
      by_cases h2n : 2 ≤ n
      · rw [if_pos h2n] at hrow; exact absurd hrow (by decide)
      · rw [if_neg h2n, if_pos h] at hrow; exact absurd hrow (by decide)
    have hl3 : l ≠ 3 := by
      intro h
      by_cases h2n : 2 ≤ n
      · rw [if_pos h2n] at hrow; exact absurd hrow (by decide)
      · rw [if_neg h2n, if_neg hl2, if_pos h] at hrow; exact absurd hrow (by decide)
    simp only [if_neg hl2, if_neg hl3]
    right; right; right; left; exact ⟨rfl, by omega⟩
  case E6 => right; simp [RCKRowIIModel]
  case E7 => right; simp [RCKRowIIModel]
  case E8 => right; simp [RCKRowIIModel]
  case F4 => right; simp [RCKRowIIModel]
  case twE6 => right; simp [RCKRowIIModel]
  case triD4 => simp
  all_goals
    exfalso
    first
      | (split_ifs at hrow <;> exact absurd hrow (by decide))
      | exact absurd hrow (by decide)

theorem rckK1II_model
    (hcov : GGLieOddCover) {Jb : Type} [Group Jb] [Finite Jb]
    (hodd : Odd (Nat.card (Subgroup.center Jb)))
    (hmark : LargeEvenMarking Jb (fun lab _ _ _ _ _ => ggSixRCKLabelRow lab = .II)) :
    (∃ (t : StatedLieTag) (n : ℕ) (φ : (ggU t n 1).K →* Jb), RCKRowIIModel t n ∧
        StatedLieAdmissible t n 2 1 ∧ Function.Surjective φ ∧
        φ.ker ≤ Subgroup.center (ggU t n 1).K) ∨
      ∃ (F : Type) (_ : Field F) (_ : Finite F) (σ : F →+* F) (φ : (triD4Universal F σ).K →* Jb),
        TriField F σ 1 ∧ Function.Surjective φ ∧
          φ.ker ≤ Subgroup.center (triD4Universal F σ).K := by
  obtain ⟨hcomm, lab, hlab, hraw⟩ := hmark
  obtain ⟨R₀, _, I₀, F₀, hq₀⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, -, hθ₀⟩ := hq₀
  obtain ⟨-, hrow⟩ := hθ₀
  have hraw' : LargeEvenRawDatum lab (fun R _ I F =>
      (IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ θ : Jb ⧸ Subgroup.center Jb ≃* R, ggSixRCKLabelRow lab = .II) ∧
      MarkedModel lab R) :=
    rckK1IIm_rawDatum_imp hlab hrow (fun R _ I F hq hm => ⟨hq, hm⟩) hraw
  obtain ⟨R, _, I, F, hq⟩ := largeEvenRawDatum_exists hraw'
  obtain ⟨hq', hm'⟩ := hq
  obtain ⟨hs, hna, hθ⟩ := hq'
  obtain ⟨θ, hP⟩ := hθ
  have hMc : MarkedModel lab (Jb ⧸ Subgroup.center Jb) := MarkedModel.of_mulEquiv θ.symm hm'
  have hchar : markChar lab = 2 := rckK1IIm_markChar_two hrow
  have hMc2 : LieModel (Jb ⧸ Subgroup.center Jb) (markTag lab) (markRank lab) 2 (markDeg lab) := by
    have h := hMc
    unfold MarkedModel at h
    rwa [hchar] at h
  have hdeg : markDeg lab = 1 := rckK1IIm_markDeg_one hlab hrow
  have hMc1 : LieModel (Jb ⧸ Subgroup.center Jb) (markTag lab) (markRank lab) 2 1 := by
    rwa [hdeg] at hMc2
  have hadm : StatedLieAdmissible (markTag lab) (markRank lab) 2 1 := LieModel.admissible hMc1
  have hpt : GGPosTag (markTag lab) ∨ markTag lab = .trialityD4 := rckK1IIm_pos_or_tri hrow
  rcases hpt with hpos | htri
  · left
    rcases rckK1IIm_model_or_tri hlab hrow with htri' | hmodel
    · exfalso
      rw [htri'] at hpos
      simp [GGPosTag] at hpos
    · obtain ⟨φ, hsurj, hker⟩ :=
        hcov.1 (markTag lab) (markRank lab) 1 hpos hadm Jb hcomm hodd hMc1
      exact ⟨markTag lab, markRank lab, φ, hmodel, hadm, hsurj, hker⟩
  · right
    have hrk : markRank lab = 0 := rckK1IIm_markRank_zero_of_tri htri
    have htriM : LieModel (Jb ⧸ Subgroup.center Jb) .trialityD4 0 2 1 := by
      have h := hMc2
      rw [htri, hrk, hdeg] at h
      exact h
    obtain ⟨F, hFieldF, hFiniteF, σ, hF, φ, hsurj, hker⟩ :=
      hcov.2 1 (le_refl 1) Jb hcomm hodd htriM
    exact ⟨F, hFieldF, hFiniteF, σ, φ, hF, hsurj, hker⟩

theorem rckRowK1_II_of_at
    (hcov : GGLieOddCover)
    (hAt : ∀ (t : StatedLieTag) (n : ℕ), RCKRowIIModel t n → StatedLieAdmissible t n 2 1 →
      RCKRowIIAt t n)
    (hTri : ∀ (F : Type) [Field F] [Finite F] (σ : F →+* F), TriField F σ 1 → RCKRowIIAtTri F σ) :
    RCKRowK1 .II RCKPosRootElt := by
  intro Jb _ _ hodd hmark
  rcases rckK1II_model hcov hodd hmark with ⟨t, n, φ, hM, hadm, hsurj, hker⟩ |
      ⟨F, _, _, σ, φ, hF, hsurj, hker⟩
  · exact hAt t n hM hadm Jb hodd φ hsurj hker
  · exact hTri F σ hF Jb hodd φ hsurj hker

end CFSG.StandardType.RCKK1II
