module

public import CFSG.LocalAnalysis.StandardType.GGQTwoVACOrth
public import CFSG.LocalAnalysis.StandardType.GGQTwoVACUnit

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggQ2GuardFailsOn_orthNoMarking :
    GGQTwoGuardFailsOn (fun p lab => GGQ2VACLabOrth p lab ∧
      ((lab.tag = .D ∧ lab.rank < 3) ∨ (lab.tag = .twD ∧ lab.rank < 2))) := by
  intro G _ _ p B Bs x L D J hS hp hL
  have hmark := ggInnerDiagOnLabel_L_pRank_ge_three hS.1.1 hL
  have hbound : ¬ LargeEvenMarking ↥L (fun lab R _ I _ _ =>
      (GGQ2VACLabOrth p lab ∧
        ((lab.tag = .D ∧ lab.rank < 3) ∨ (lab.tag = .twD ∧ lab.rank < 2))) ∧
      ∃ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I ∧ IsElemAbelian p E ∧
        p ^ 3 ≤ Nat.card E) := by
    refine not_largeEvenMarking_of_labelAll_card_lt (p := p)
      (S := fun lab => GGQ2VACLabOrth p lab ∧
        ((lab.tag = .D ∧ lab.rank < 3) ∨ (lab.tag = .twD ∧ lab.rank < 2))) ?_
    intro lab hlab hS'
    rcases lab with ⟨tag, rank, n⟩
    simp only [GGQ2VACLabOrth] at hS'
    rcases hS' with ⟨-, hD | htwD⟩
    · simp only [LargeEvenInLambda2] at hlab
      rcases hD with ⟨rfl, hrank⟩
      simp at hlab
      omega
    · simp only [LargeEvenInLambda2] at hlab
      rcases htwD with ⟨rfl, hrank⟩
      simp at hlab
      omega
  exact absurd hmark hbound

theorem ggQ2GuardFailsOn_orthSmallRows :
    GGQTwoGuardFailsOn (fun p lab => GGQ2VACLabOrth p lab ∧
      ((lab.tag = .D ∧ lab.rank = 3) ∨ (lab.tag = .twD ∧ lab.rank = 2))) := by
  simpa only [GGQ2VACLabOrth] using
    ggQTwoGuardFailsOn_orthSmall

theorem ggQ2GuardFailsOn_orthFullRows
    (hCav : GGQ2CavOfTBFull) :
    GGQTwoGuardFailsOn (fun p lab => GGQ2VACLabOrth p lab ∧ 4 ≤ lab.rank ∧
      ((lab.tag = .D ∧ Even lab.rank) ∨ (lab.tag = .twD ∧ ¬ Even lab.rank))) :=
  ggQTwoGuardFailsOn_of_cavFull hCav fun hS hp hL =>
    ggQ2TBFull_of_orthFull hS hp (by simpa only [GGQ2VACLabOrth] using hL)


theorem ggQ2TBFull_orth_twD3
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J) (hp : p = 3)
    (hL : GGInnerDiagOnLabel (fun p lab => GGQ2VACLabOrth p lab ∧ lab.tag = .twD ∧
      lab.rank = 3) p Bs L) :
    GGQ2TBFull p Bs L := by
  subst hp
  obtain ⟨hperf, lab, hlab, hraw⟩ := hL
  obtain ⟨R, hR, I, F, hQ⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, -, θ, hP⟩ := hQ
  obtain ⟨hS, hBsN, hBsI0⟩ := hP
  obtain ⟨hgl, htag, hrank⟩ := hS
  have hn1 : lab.n = 1 := by
    have h1 : 1 ≤ lab.n := hlab.1
    have h2 : lab.n < 2 := hgl.1
    omega
  dsimp only [CFSG.Assembly.LargeEvenRawDatumLegacy] at hraw
  rw [htag] at hraw
  simp [hrank, hn1] at hraw
  have hraw' := hraw
  obtain ⟨K, i1, i2, hK, hQ'⟩ := hraw
  rcases hQ' with ⟨hsimple, hnab, θ', hS', hBsN', hBsI0'⟩
  refine ggQ2TBFull_of_orthLabel (lab := lab) ?_ ?_ hS' ?_
  · exact θ'.1
  · refine ⟨hperf, lab, hlab, ?_⟩
    have hraw_canon : LargeEvenRawDatum lab (fun R _ I F => IsSimpleGroup R ∧
      (∃ a b : R, a * b ≠ b * a) ∧
      GGQ2VACLabOrth 3 lab ∧ Bs ≤ Subgroup.normalizer ↑L ∧
      ∃ θ : ↥L ⧸ Subgroup.center ↥L ≃* R,
        ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => ↑l' = b⁻¹ * l * b) φ) := by
      simpa [LargeEvenRawDatum, htag, hrank, hn1] using hraw'
    exact largeEvenRawDatum_mono (fun R _ I F ⟨hsimple, hnab, θ'', hS'', hBsN'', hBsI0''⟩ =>
      ⟨hsimple, hnab, hBsN'', rfl⟩) hraw_canon
  · rw [ggQ2Unit_gamma_card (K := K) (n := 1) (d := 4) hS hK (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (θ := hBsN') hperf hS' hBsI0']
    simp [GGQ2LieRank, htag, hrank]

theorem ggQ2GuardFailsOn_orth_twD3
    (hCav : GGQ2CavOfTBFull) :
    GGQTwoGuardFailsOn (fun p lab => GGQ2VACLabOrth p lab ∧ lab.tag = .twD ∧
      lab.rank = 3) :=
  ggQTwoGuardFailsOn_of_cavFull hCav fun hS hp hL =>
    ggQ2TBFull_orth_twD3 hS hp (by simpa only [GGQ2VACLabOrth] using hL)


@[expose] def GGQ2VACLabOrthNonFull (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGQ2VACLabOrth p lab ∧ 4 ≤ lab.rank ∧
    ((lab.tag = .D ∧ ¬ Even lab.rank) ∨ (lab.tag = .twD ∧ Even lab.rank))

theorem ggQ2VACLabOrth_rows {p : ℕ} {lab : LargeEvenLabel} (h : GGQ2VACLabOrth p lab) :
    (GGQ2VACLabOrth p lab ∧
        ((lab.tag = .D ∧ lab.rank < 3) ∨ (lab.tag = .twD ∧ lab.rank < 2))) ∨
      (GGQ2VACLabOrth p lab ∧
        ((lab.tag = .D ∧ lab.rank = 3) ∨ (lab.tag = .twD ∧ lab.rank = 2))) ∨
      (GGQ2VACLabOrth p lab ∧ 4 ≤ lab.rank ∧
        ((lab.tag = .D ∧ Even lab.rank) ∨ (lab.tag = .twD ∧ ¬ Even lab.rank))) ∨
      (GGQ2VACLabOrth p lab ∧ lab.tag = .twD ∧ lab.rank = 3) ∨
      GGQ2VACLabOrthNonFull p lab := by
  rcases Nat.even_or_odd lab.rank with he | ho
  · rcases h.2 with hD | htw
    · by_cases h3 : lab.rank < 3
      · exact Or.inl ⟨h, Or.inl ⟨hD, h3⟩⟩
      · have h4 : 4 ≤ lab.rank := by obtain ⟨k, hk⟩ := he; omega
        exact Or.inr (Or.inr (Or.inl ⟨h, h4, Or.inl ⟨hD, he⟩⟩))
    · by_cases h2 : lab.rank < 2
      · exact Or.inl ⟨h, Or.inr ⟨htw, h2⟩⟩
      · by_cases h2' : lab.rank = 2
        · exact Or.inr (Or.inl ⟨h, Or.inr ⟨htw, h2'⟩⟩)
        · have h4 : 4 ≤ lab.rank := by obtain ⟨k, hk⟩ := he; omega
          refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
          unfold GGQ2VACLabOrthNonFull
          exact ⟨h, h4, Or.inr ⟨htw, he⟩⟩
  · have hne : ¬ Even lab.rank := Nat.not_even_iff_odd.mpr ho
    rcases h.2 with hD | htw
    · by_cases h3 : lab.rank < 3
      · exact Or.inl ⟨h, Or.inl ⟨hD, h3⟩⟩
      · by_cases h3' : lab.rank = 3
        · exact Or.inr (Or.inl ⟨h, Or.inl ⟨hD, h3'⟩⟩)
        · refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
          unfold GGQ2VACLabOrthNonFull
          exact ⟨h, by omega, Or.inl ⟨hD, hne⟩⟩
    · by_cases h2 : lab.rank < 2
      · exact Or.inl ⟨h, Or.inr ⟨htw, h2⟩⟩
      · by_cases h3 : lab.rank = 3
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h, htw, h3⟩)))
        · have h4 : 4 ≤ lab.rank := by obtain ⟨k, hk⟩ := ho; omega
          exact Or.inr (Or.inr (Or.inl ⟨h, h4, Or.inr ⟨htw, hne⟩⟩))

theorem ggQTwoGuardFailsOn_orth
    (hCav : GGQ2CavOfTBFull)
    (hNonFull : GGQTwoGuardFailsOn GGQ2VACLabOrthNonFull) :
    GGQTwoGuardFailsOn GGQ2VACLabOrth := by
  intro G _ _ p B Bs x L D J hS hp hL
  have hL' : GGInnerDiagOnLabel (fun p lab =>
      (GGQ2VACLabOrth p lab ∧
          ((lab.tag = .D ∧ lab.rank < 3) ∨ (lab.tag = .twD ∧ lab.rank < 2))) ∨
        (GGQ2VACLabOrth p lab ∧
          ((lab.tag = .D ∧ lab.rank = 3) ∨ (lab.tag = .twD ∧ lab.rank = 2))) ∨
        (GGQ2VACLabOrth p lab ∧ 4 ≤ lab.rank ∧
          ((lab.tag = .D ∧ Even lab.rank) ∨ (lab.tag = .twD ∧ ¬ Even lab.rank))) ∨
        (GGQ2VACLabOrth p lab ∧ lab.tag = .twD ∧ lab.rank = 3) ∨
        GGQ2VACLabOrthNonFull p lab) p Bs L :=
    hL.mono_label fun _ h => ggQ2VACLabOrth_rows h
  rcases hL'.elim_or with h | h
  · exact ggQ2GuardFailsOn_orthNoMarking G p B Bs x L D J hS hp h
  rcases h.elim_or with h | h
  · exact ggQ2GuardFailsOn_orthSmallRows G p B Bs x L D J hS hp h
  rcases h.elim_or with h | h
  · exact ggQ2GuardFailsOn_orthFullRows hCav G p B Bs x L D J hS hp h
  rcases h.elim_or with h | h
  · exact ggQ2GuardFailsOn_orth_twD3 hCav G p B Bs x L D J hS hp h
  · exact hNonFull G p B Bs x L D J hS hp h

end CFSG.StandardType

end
