module

public import CFSG.LocalAnalysis.WeakClosure81.W18Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)

variable {G : Type} [Group G] [Finite G]

private theorem lGen_le_inf' {M H T : Subgroup G} (P : ∀ (X : Type) [Group X], Prop)
    (hP : ∀ X : Subgroup G, T ≤ X → X < H → ¬ HasCompFactor X P → X ≤ M) :
    lGen P H T ≤ H ⊓ M :=
  iSup₂_le fun X hX => le_inf hX.2.1.le (hP X hX.1 hX.2.1 hX.2.2)

namespace MinCex183

variable {D : Data G} {V₀ V H : Subgroup G} {i : ℕ}

theorem le_normalizer_one (h : MinCex183 D V₀ V H i) (h1 : ¬ Concl181 D V₀ V H)
    {X : Subgroup G} (hTX : D.T ≤ X) (hXH : X < H) (hX : ¬ HasCompFactor X IsCalL1) :
    X ≤ D.M := by
  by_contra hXM
  have hX183 := h.hyp.of_le hTX hXH.le hXM
  have hc := (h.concl_of_lt hX183 hXH).1
  obtain ⟨h181, hm, -⟩ := not_concl181_iff.mp h1
  exact hX (hc (W3Hyp181.of_le h181 hXH.le) hm)

theorem le_normalizer_zero (h : MinCex183 D V₀ V H i) (h2 : ¬ Concl182 D V₀ V H i)
    {X : Subgroup G} (hTX : D.T ≤ X) (hXH : X < H) (hX : ¬ HasCompFactor X IsCalL0) :
    X ≤ D.M := by
  by_contra hXM
  have hX183 := h.hyp.of_le hTX hXH.le hXM
  have hc := (h.concl_of_lt hX183 hXH).2
  obtain ⟨h182, hm, -⟩ := not_concl182_iff.mp h2
  exact hX (hc (W3Hyp182.of_le h182 hXH.le) hm)

theorem inf_lt (h : MinCex183 D V₀ V H i) : D.T ≤ H ⊓ D.M ∧ H ⊓ D.M < H :=
  ⟨le_inf h.hyp.hyp171.2.1 D.sylowM.le,
    lt_of_le_of_ne inf_le_left fun heq => h.hyp.notLe (heq ▸ inf_le_right)⟩

theorem lGen_one_le_inf (h : MinCex183 D V₀ V H i) (h1 : ¬ Concl181 D V₀ V H) :
    lGen IsCalL1 H D.T ≤ H ⊓ D.M :=
  lGen_le_inf' (M := D.M) (H := H) (T := D.T) IsCalL1
    (fun X hTX hXH hX => h.le_normalizer_one h1 hTX hXH hX)

theorem lGen_zero_le_inf (h : MinCex183 D V₀ V H i) (h2 : ¬ Concl182 D V₀ V H i) :
    lGen IsCalL0 H D.T ≤ H ⊓ D.M :=
  lGen_le_inf' (M := D.M) (H := H) (T := D.T) IsCalL0
    (fun X hTX hXH hX => h.le_normalizer_zero h2 hTX hXH hX)

theorem hyps_5_13 (h : MinCex183 D V₀ V H i) (h1 : ¬ Concl181 D V₀ V H) :
    CFSG.Open.IsKGroup ↥H ∧ IsSylowIn 2 D.T H ∧ D.T < H ∧ CFSG.Open.pRank 3 H ≤ 1 ∧
      ¬ HasCompFactor H IsCalL1 ∧ H ≠ lGen IsCalL1 H D.T := by
  obtain ⟨h181, -, hno⟩ := not_concl181_iff.mp h1
  obtain ⟨hTM, hlt⟩ := inf_lt h
  refine ⟨h.hyp.kgroup, h.hyp.isSylowIn_T, h.hyp.T_lt, ?_, hno, ?_⟩
  · rw [← CFSG.SectionRank.pRank_coe_eq_openPRank]
    exact h181.1
  · intro heq
    have hle := lGen_le_inf' (M := D.M) (H := H) (T := D.T) IsCalL1
      (fun X hTX hXH hX => h.le_normalizer_one h1 hTX hXH hX)
    rw [← heq] at hle
    exact absurd (lt_of_le_of_lt hle hlt) (lt_irrefl _)

theorem hyps_5_11 (h : MinCex183 D V₀ V H i) (h2 : ¬ Concl182 D V₀ V H i) :
    CFSG.Open.IsKGroup ↥H ∧ IsSylowIn 2 D.T H ∧ D.T < H ∧ ¬ HasCompFactor H IsCalL0 ∧
      H ≠ lGen IsCalL0 H D.T ∧
      ∀ p : ℕ, p.Prime → p ≠ 2 →
        CFSG.Open.pRank p H ≤ 3 ∨ CFSG.Open.pRank p (lGen IsCalL0 H D.T) ≤ 1 := by
  obtain ⟨h182, -, hno⟩ := not_concl182_iff.mp h2
  obtain ⟨hTM, hlt⟩ := inf_lt h
  have hle := lGen_le_inf' (M := D.M) (H := H) (T := D.T) IsCalL0
    (fun X hTX hXH hX => h.le_normalizer_zero h2 hTX hXH hX)
  refine ⟨h.hyp.kgroup, h.hyp.isSylowIn_T, h.hyp.T_lt, hno, ?_, ?_⟩
  · intro heq
    rw [← heq] at hle
    exact absurd (lt_of_le_of_lt hle hlt) (lt_irrefl _)
  · intro p hpp hp2
    by_cases hp3 : CFSG.Open.pRank p H ≤ 3
    · exact Or.inl hp3
    · refine Or.inr ((CFSG.SectionRank.pRank_mono hpp.one_lt hle).trans ?_)
      have h3 : 3 < CFSG.pRank p ↥H := by
        rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
        exact not_le.mp hp3
      have h4 := h182.2 p hpp hp2 h3
      rwa [CFSG.SectionRank.pRank_coe_eq_openPRank] at h4

end MinCex183

end CFSG.LocalAnalysis.WeakClosure81

end
