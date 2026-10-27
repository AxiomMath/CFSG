module

public import CFSG.Quasithin.Background.E2TwoProofDefs

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique B6

namespace E2P

variable {X : Type} [Group X] [Finite X] {K T M : Subgroup X}

theorem not_asHyp_of_two_max (hX : ASHyp K T M) {M₁ M₂ : Subgroup X}
    (h₁ : IsMaxSubgroupIn ⊤ M₁) (h₂ : IsMaxSubgroupIn ⊤ M₂) (hne : M₁ ≠ M₂) (hT₁ : T ≤ M₁)
    (hT₂ : T ≤ M₂) : False := by
  have hU := hX.minPar.uniqueMax
  have e₁ : M₁ ∈ maxOver ⊤ T := ⟨h₁, hT₁⟩
  have e₂ : M₂ ∈ maxOver ⊤ T := ⟨h₂, hT₂⟩
  rw [IsUniqueMaxOver] at hU
  rw [hU] at e₁ e₂
  exact hne (e₁.trans e₂.symm)

theorem false_of_asc86b (hX : ASHyp K T M) {s : TauCeti.SporadicName} (h : Asc86bClauseB s)
    (hs : IsSporadic s ↥K) : False := by
  obtain ⟨M₁, M₂, h₁, h₂, hne, hT₁, hT₂⟩ :=
    h X K T hX.normal hs hX.cent hX.minPar.isSylow hX.sup
  exact not_asHyp_of_two_max hX h₁ h₂ hne hT₁ hT₂

theorem eq_five_of_pow {p f : ℕ} (hp : p.Prime) (hf : f = 1 ∨ f = 2) (h : p ^ f = 5) :
    p = 5 ∧ f = 1 := by
  rcases hf with rfl | rfl
  · exact ⟨by simpa using h, rfl⟩
  · exfalso
    have hp2 := hp.two_le
    have : p ≤ 2 := by nlinarith
    have : p = 2 := by omega
    subst this
    norm_num at h

theorem eq_nine_of_pow {p f : ℕ} (hp : p.Prime) (hf : f = 1 ∨ f = 2) (h : p ^ f = 9) :
    p = 3 ∧ f = 2 := by
  rcases hf with rfl | rfl
  · exfalso
    rw [pow_one] at h
    subst h
    norm_num at hp
  · have : p = 3 := by
      have h3 : p * p = 3 * 3 := by rw [← pow_two]; simpa using h
      nlinarith [hp.two_le]
    exact ⟨this, rfl⟩

theorem isSp4Prime_one_iff {Y : Type} [Group Y] : E2.IsSp4Prime 1 Y ↔ IsAlt 6 Y := by
  simp [E2.IsSp4Prime]

theorem isSp4Prime_of_ne {Y : Type} [Group Y] {n : ℕ} (hn : n ≠ 1) :
    E2.IsSp4Prime n Y ↔ IsPSp4 2 n Y := by
  simp [E2.IsSp4Prime, hn]

theorem asCases_of_families (hF : E22Families) (hX : ASHyp K T M) (hlist : A23List ↥K) :
    ASCases K T M := by
  have hAlt := hF.alt X K T M hX
  rcases hlist with ⟨n, h5, h8, he⟩ | ⟨p, hp, hp2, hodd⟩ | hchar2 | ⟨n, hn, hLn⟩ | ⟨s, hs, he⟩
  ·
    have hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 := by omega
    rcases hn with rfl | rfl | rfl | rfl
    · obtain ⟨h1, h2⟩ := hAlt.1 (Or.inl he)
      exact Or.inl ⟨2, ⟨le_rfl, Or.inl h1⟩, h2⟩
    · obtain ⟨h1, h2, h3⟩ := hAlt.2.1 (Or.inl he)
      exact Or.inr (Or.inl ⟨1, le_rfl, Or.inr h1, h2, h3⟩)
    · exact absurd he hAlt.2.2.1
    · exact absurd he hAlt.2.2.2
  ·
    rcases hodd with ⟨f, hf, h⟩ | h | h
    · by_cases h5 : p ^ f = 5
      · obtain ⟨rfl, rfl⟩ := eq_five_of_pow hp hf h5
        obtain ⟨h1, h2⟩ := hAlt.1 (Or.inr h)
        exact Or.inl ⟨2, ⟨le_rfl, Or.inl h1⟩, h2⟩
      by_cases h9 : p ^ f = 9
      · obtain ⟨rfl, rfl⟩ := eq_nine_of_pow hp hf h9
        obtain ⟨h1, h2, h3⟩ := hAlt.2.1 (Or.inr h)
        exact Or.inr (Or.inl ⟨1, le_rfl, Or.inr h1, h2, h3⟩)
      obtain ⟨hp3, hcong, hC, hA⟩ := hF.oddL2 X K T M hX p f hp hp2 hf h5 h9 h
      exact Or.inr (Or.inr (Or.inl ⟨p, f, hp, hp3, hf, hcong, h, hC, hA⟩))
    all_goals
      obtain ⟨hC, hcase⟩ := hF.asc80 p hp hp2 X K T M hX.normal hX.simple
        (by first | exact Or.inl h | exact Or.inr h) hX.cent hX.minPar.isSylow hX.sup
        hX.minPar.uniqueMax
      refine Or.inr (Or.inr (Or.inr ⟨p, hp, hp2, ?_, hC⟩))
      rcases hcase with ⟨hL, hp4, hout⟩ | ⟨hU, hp4⟩
      · exact Or.inr ⟨hp4, hL, hout⟩
      · exact Or.inl ⟨hp4, hU⟩
  ·
    rcases hchar2 with ⟨f, ⟨h2, h⟩ | ⟨h1, h⟩ | ⟨h2, h⟩ | ⟨h2, h⟩ | ⟨h2, h⟩ | ⟨h1, h⟩ |
        ⟨ho, h3, h⟩ | ⟨ho, h3, h⟩⟩ | hT
    · have hB : E2.IsBenderOf f ↥K := ⟨h2, Or.inl h⟩
      exact Or.inl ⟨f, hB, hF.bender X K T M hX f hB⟩
    · obtain ⟨hD, hB⟩ := hF.l3sp4 X K T M hX f h1 (Or.inl h)
      exact Or.inr (Or.inl ⟨f, h1, Or.inl h, hD, hB⟩)
    · have hB : E2.IsBenderOf f ↥K := ⟨h2, Or.inr (Or.inr h)⟩
      exact Or.inl ⟨f, hB, hF.bender X K T M hX f hB⟩
    · have hS : E2.IsSp4Prime f ↥K := (isSp4Prime_of_ne (by omega)).mpr h
      obtain ⟨hD, hB⟩ := hF.l3sp4 X K T M hX f (by omega) (Or.inr hS)
      exact Or.inr (Or.inl ⟨f, by omega, Or.inr hS, hD, hB⟩)
    · exact (hF.char2Exc X K T M hX (Or.inl ⟨f, h2, h⟩)).elim
    · exact (hF.char2Exc X K T M hX (Or.inr (Or.inl ⟨f, h1, h⟩))).elim
    · exact (hF.char2Exc X K T M hX (Or.inr (Or.inr (Or.inl ⟨f, ho, h3, h⟩)))).elim
    · have hB : E2.IsBenderOf f ↥K := ⟨by omega, Or.inr (Or.inl h)⟩
      exact Or.inl ⟨f, hB, hF.bender X K T M hX f hB⟩
    · exact (hF.char2Exc X K T M hX (Or.inr (Or.inr (Or.inr hT)))).elim
  ·
    exact (hF.lnTwo X K T M hX n hn hLn).elim
  ·
    by_cases hJ4 : s = .J4
    · subst hJ4
      exact (false_of_asc86b hX hF.asc86b he).elim
    · have hten : SporTen s := by
        rcases hs with h | h | h | h | h | h | h | h | h | h | h <;> subst h
        all_goals first | (exact absurd rfl hJ4) | (unfold SporTen; tauto)
      exact (false_of_asc86b hX (hF.sporTen s hten) he).elim

end E2P

end CFSG.Quasithin
