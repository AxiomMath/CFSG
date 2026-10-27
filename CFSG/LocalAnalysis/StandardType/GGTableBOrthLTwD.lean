module

public import CFSG.LocalAnalysis.StandardType.GGTableBOrthLSp
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenVacMore
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestUnitaryCenter

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableBOrthL

@[expose] def GGOrthLTwDFieldLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twD ∧ 3 ≤ lab.rank ∧ p ∣ 2 ^ lab.n + 1 ∧ p ∣ lab.n

theorem GGOrthLTwDFieldLabel.orthNs_or_unitary {p : ℕ} {lab : LargeEvenLabel}
    (h : GGOrthLTwDFieldLabel p lab) : GGOrthNsLabel p lab ∨ GGUnitaryCoprimeLabel p lab := by
  obtain ⟨ht, hl, hpn, -⟩ := h
  by_cases h3 : lab.rank = 3
  · exact Or.inr (Or.inr ⟨ht, h3, hpn⟩)
  · exact Or.inl ⟨Or.inr ht, by omega, hpn⟩

section TableB

theorem ggTableBIrredInputOn_twDField : GGTableBIrredInputOn GGOrthLTwDFieldLabel :=
  (ggTableBIrredInputOn_orthNs.or ggTableBIrredInputOn_unitary).mono fun _ _ h =>
    h.orthNs_or_unitary

theorem ggTableBCxInputOn_of_not_twDField {S : ℕ → LargeEvenLabel → Prop}
    (hD : GGBstarInnerDiagLInputOn GGOrthLTwDFieldLabel)
    (h : GGTableBCxInputOn fun p lab => S p lab ∧ ¬ GGOrthLTwDFieldLabel p lab) :
    GGTableBCxInputOn S :=
  ((ggTableBCxInputOn_of_irred hD ggTableBIrredInputOn_twDField).or h).mono fun p lab hS => by
    by_cases h1 : GGOrthLTwDFieldLabel p lab
    · exact Or.inl h1
    · exact Or.inr ⟨hS, h1⟩

theorem ggTableBModuleInputOn_of_not_twDField {S : ℕ → LargeEvenLabel → Prop}
    (hD : GGBstarInnerDiagLInputOn GGOrthLTwDFieldLabel)
    (h : GGTableBModuleInputOn fun p lab => S p lab ∧ ¬ GGOrthLTwDFieldLabel p lab) :
    GGTableBModuleInputOn S :=
  ((ggTableBModuleInputOn_of_irred hD ggTableBIrredInputOn_twDField).or h).mono fun p lab hS => by
    by_cases h1 : GGOrthLTwDFieldLabel p lab
    · exact Or.inl h1
    · exact Or.inr ⟨hS, h1⟩

theorem ggTableBActionInputOn_of_not_twDField {S : ℕ → LargeEvenLabel → Prop}
    (hD : GGBstarInnerDiagLInputOn GGOrthLTwDFieldLabel)
    (h : GGTableBActionInputOn fun p lab => S p lab ∧ ¬ GGOrthLTwDFieldLabel p lab) :
    GGTableBActionInputOn S :=
  ((ggTableBActionInputOn_of_irred hD ggTableBIrredInputOn_twDField).or h).mono fun p lab hS => by
    by_cases h1 : GGOrthLTwDFieldLabel p lab
    · exact Or.inl h1
    · exact Or.inr ⟨hS, h1⟩

end TableB

@[expose] def GGOrthLTvLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .D ∧ 4 ≤ lab.rank ∧ (p ∣ 2 ^ lab.n - 1 ∨ (lab.n = 1 ∧ p = 3))) ∨
    (lab.tag = .twD ∧ 4 ≤ lab.rank ∧ (p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1)) ∨
    (lab.tag = .twD ∧ lab.rank = 3 ∧ p ∣ 2 ^ lab.n + 1)

@[expose] def GGOmegaPlusTvSCInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (m p : ℕ), 4 ≤ m → p.Prime → p ≠ 2 →
    (p ∣ Nat.card K - 1 ∨ (Nat.card K = 2 ∧ p = 3)) →
      GGNoTransvectionSC p (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m)))
        (LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))))

@[expose] def GGOmegaMinusTvSCInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (m p : ℕ) (b c : K), 3 ≤ m → p.Prime → p ≠ 2 →
    (∀ s : K, s ^ 2 + b * s + c ≠ 0) → (p ∣ Nat.card K - 1 ∨ p ∣ Nat.card K + 1) →
      GGNoTransvectionSC p (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)))
        (LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))))

@[expose] def GGUnitaryFourTvSCInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n p : ℕ), Nat.card K = (2 ^ n) ^ 2 → 1 ≤ n → p.Prime →
    p ∣ 2 ^ n + 1 →
      GGNoTransvectionSC p (LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ n)))
        (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 4) K (2 ^ n)))
          (LargeEvenGUSet (Fin 4) K (2 ^ n)))

@[expose] def GGOrthLTvSCRest : Prop :=
  GGOmegaPlusTvSCInput ∧ GGOmegaMinusTvSCInput ∧ GGUnitaryFourTvSCInput

section TvLabels

theorem largeEvenLabelAll_tvSC_orthTv (hin : GGOrthLTvSCRest) {p : ℕ} (hp : p.Prime)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (h : GGOrthLTvLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGCenterCoprime p R ∧ GGNoTransvectionSC p R I := by
  obtain ⟨t, l, n⟩ := lab
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  rcases h with ⟨htag, hl, hpq⟩ | ⟨htag, hl, hpq⟩ | ⟨htag, hl, hpq⟩
  · dsimp only at htag hl hpq
    subst htag
    have hp2 : p ≠ 2 := by
      rcases hpq with h1 | ⟨-, rfl⟩
      · exact ne_two_of_dvd_two_pow_sub_one hn h1
      · norm_num
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [ite_eq_right (show ¬ (l = 3) by omega)] at hQ ⊢
    obtain ⟨K, _, _, hK, hQ⟩ := hQ
    have := charP_two_of_card hK
    refine ⟨K, inferInstance, inferInstance, hK, hQ,
      CorFourTwoOpen.ggCenterCoprime_of_centerPrime
        (CorFourTwoOpen.ggCenterPrime_omegaPlus hp hp2 (by omega)), ?_⟩
    refine hin.1 K l p hl hp hp2 ?_
    rw [hK]
    rcases hpq with h1 | ⟨hn1, rfl⟩
    · exact Or.inl h1
    · exact Or.inr ⟨by rw [hn1, pow_one], rfl⟩
  · dsimp only at htag hl hpq
    subst htag
    have hp2 : p ≠ 2 := by
      rcases hpq with h1 | h1
      · exact ne_two_of_dvd_two_pow_sub_one hn h1
      · exact TableBU.ne_two_of_dvd_two_pow_add_one hn h1
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [ite_eq_right (show ¬ (l = 2) by omega),
      ite_eq_right (show ¬ (l = 3) by omega)] at hQ ⊢
    obtain ⟨K, _, _, hK, b, c, hbc, hQ⟩ := hQ
    have := charP_two_of_card hK
    refine ⟨K, inferInstance, inferInstance, hK, b, c, hbc, hQ,
      CorFourTwoOpen.ggCenterCoprime_of_centerPrime
        (CorFourTwoOpen.ggCenterPrime_omegaMinus hp hp2 (by omega) hbc), ?_⟩
    exact hin.2.1 K (l - 1) p b c (by omega) hp hp2 hbc (by rw [hK]; exact hpq)
  · dsimp only at htag hl hpq
    subst htag hl
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [ite_eq_right (show ¬ (3 = 2) by decide), ite_eq_left (show (3 = 3) from rfl)] at hQ ⊢
    obtain ⟨K, _, _, hK, hQ⟩ := hQ
    have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpq
    have hp4 : ¬ p ∣ 4 := fun h4 => hp2 (by
      have h1 : p ∣ 2 ^ 2 := by norm_num; exact h4
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h1))
    refine ⟨K, inferInstance, inferInstance, hK, hQ,
      CorFourTwoOpen.ggCenterCoprime_of_centerPrime
        (StdSubRestU.ggCenterPrime_unitary hK hn (by norm_num) (by simp) hp hp2 hp4), ?_⟩
    exact hin.2.2 K n p hK hn hp hpq

end TvLabels

section Tv

theorem ggLTransvectionCenterInputOn_orthTv (hin : GGOrthLTvSCRest) :
    GGLTransvectionCenterInputOn GGOrthLTvLabel :=
  ggLTransvectionCenterInputOn_of_labelsSC ggLNoncyclicInput_holds fun _ _ hp hlab h =>
    largeEvenLabelAll_tvSC_orthTv hin hp hlab h

end Tv

end CFSG.StandardType

end
