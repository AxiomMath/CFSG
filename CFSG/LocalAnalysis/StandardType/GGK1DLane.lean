module

public import CFSG.LocalAnalysis.StandardType.GGK1DDefs
public import CFSG.LocalAnalysis.StandardType.GGK1DCore

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Polynomial
open CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.PartOne.KCOrthogonal (OddOrderIsometry reciprocalPolynomial)
open CFSG.RankThree.Classical (IsReciprocalTransversal)

theorem ggK1D_raw_plus {p nf r : ℕ} (h4 : 4 ≤ r) (Q : LargeEvenRawCont)
    (hQ : LargeEvenRawDatum ⟨.D, r, nf⟩ Q)
    (hP : ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ nf →
      GGK1Cont GGMultValidCl p ⟨.D, r, nf⟩
        (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K r)))
        (LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K r))))) :
    LargeEvenRawDatum ⟨.D, r, nf⟩ fun R _ I F =>
      Q R I F ∧ GGK1Cont GGMultValidCl p ⟨.D, r, nf⟩ R I := by
  have h3 : r ≠ 3 := by omega
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  rw [if_neg h3] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQR⟩ := hQ
  refine ⟨K, i1, i2, hK, hQR, ?_⟩
  letI := i1
  letI := i2
  exact hP K hK

theorem ggK1D_raw_minus {p nf r : ℕ} (h4 : 4 ≤ r) (Q : LargeEvenRawCont)
    (hQ : LargeEvenRawDatum ⟨.twD, r, nf⟩ Q)
    (hP : ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ nf → ∀ b c : K,
      (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
      GGK1Cont GGMultValidCl p ⟨.twD, r, nf⟩
        (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (r - 1) b c)))
        (LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (r - 1) b c))))) :
    LargeEvenRawDatum ⟨.twD, r, nf⟩ fun R _ I F =>
      Q R I F ∧ GGK1Cont GGMultValidCl p ⟨.twD, r, nf⟩ R I := by
  have h2 : r ≠ 2 := by omega
  have h3 : r ≠ 3 := by omega
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  rw [if_neg h2, if_neg h3] at hQ ⊢
  obtain ⟨K, i1, i2, hK, b, c, hirr, hQR⟩ := hQ
  refine ⟨K, i1, i2, hK, b, c, hirr, hQR, ?_⟩
  letI := i1
  letI := i2
  exact hP K hK b c hirr

theorem ggK1D_coprime_center_plus (hS : GGK0Schur GGKacGenericClD)
    {p nf r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1)
    (hlab : LargeEvenInLambda2 ⟨.D, r, nf⟩) (h4 : 4 ≤ r)
    {K : Type} [Field K] [Finite K] (hKcard : Nat.card K = 2 ^ nf) :
    ∀ (L' : Type) [Group L'] [Finite L']
      (ψ : L' →* LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K r))),
      Function.Surjective ψ → ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
      (Nat.card (Subgroup.center L')).Coprime p := by
  have hgenCl : GGKacGenericCl ⟨.D, r, nf⟩ p := by
    change p.Prime ∧ p ≠ 2 ∧ (p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1) ∧
      (LargeEvenLieTag.D = LargeEvenLieTag.A ∨ LargeEvenLieTag.D = LargeEvenLieTag.twA ∨
        LargeEvenLieTag.D = LargeEvenLieTag.B ∨ LargeEvenLieTag.D = LargeEvenLieTag.C ∨
        LargeEvenLieTag.D = LargeEvenLieTag.D ∨ LargeEvenLieTag.D = LargeEvenLieTag.twD) ∧
      ¬ (LargeEvenLieTag.D = LargeEvenLieTag.A ∧ p ∣ r + 1 ∧ p ∣ 2 ^ nf - 1) ∧
      ¬ (LargeEvenLieTag.D = LargeEvenLieTag.twA ∧ p ∣ r + 1 ∧ p ∣ 2 ^ nf + 1)
    refine ⟨hp, hp2, hdvd, ?_, ?_, ?_⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · intro h; exact absurd h.1 (by decide)
    · intro h; exact absurd h.1 (by decide)
  have hgenD : GGKacGenericClD ⟨.D, r, nf⟩ p := ⟨hgenCl, Or.inl rfl, h4⟩
  intro L' _ _ ψ hψ hker hcomm
  have hQpin : LargeEvenRawDatum ⟨.D, r, nf⟩
      (fun R _ _ _ => Nonempty (R ≃* LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K r)))) := by
    dsimp only [LargeEvenRawDatum]
    rw [if_neg (show r ≠ 3 by omega)]
    exact ⟨K, inferInstance, inferInstance, hKcard, ⟨MulEquiv.refl _⟩⟩
  have hSchur := hS p ⟨.D, r, nf⟩ hlab hgenD _ hQpin
  obtain ⟨R₀, _hR₀grp, _I₀, _F₀, hQ₀, hCop⟩ := largeEvenRawDatum_exists hSchur
  obtain ⟨e₀⟩ := hQ₀
  exact hCop L' (e₀.symm.toMonoidHom.comp ψ) (e₀.symm.surjective.comp hψ) (by
    intro l hl
    apply hker
    have h1 : e₀.symm (ψ l) = 1 := hl
    have := congrArg e₀ h1
    simpa using this) hcomm

theorem ggK1D_coprime_center_minus (hS : GGK0Schur GGKacGenericClD)
    {p nf r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1)
    (hlab : LargeEvenInLambda2 ⟨.twD, r, nf⟩) (h4 : 4 ≤ r)
    {K : Type} [Field K] [Finite K] (hKcard : Nat.card K = 2 ^ nf) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∀ (L' : Type) [Group L'] [Finite L']
      (ψ : L' →* LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (r - 1) b c))),
      Function.Surjective ψ → ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
      (Nat.card (Subgroup.center L')).Coprime p := by
  have hgenCl : GGKacGenericCl ⟨.twD, r, nf⟩ p := by
    change p.Prime ∧ p ≠ 2 ∧ (p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1) ∧
      (LargeEvenLieTag.twD = LargeEvenLieTag.A ∨ LargeEvenLieTag.twD = LargeEvenLieTag.twA ∨
        LargeEvenLieTag.twD = LargeEvenLieTag.B ∨ LargeEvenLieTag.twD = LargeEvenLieTag.C ∨
        LargeEvenLieTag.twD = LargeEvenLieTag.D ∨ LargeEvenLieTag.twD = LargeEvenLieTag.twD) ∧
      ¬ (LargeEvenLieTag.twD = LargeEvenLieTag.A ∧ p ∣ r + 1 ∧ p ∣ 2 ^ nf - 1) ∧
      ¬ (LargeEvenLieTag.twD = LargeEvenLieTag.twA ∧ p ∣ r + 1 ∧ p ∣ 2 ^ nf + 1)
    refine ⟨hp, hp2, hdvd, ?_, ?_, ?_⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
    · intro h; exact absurd h.1 (by decide)
    · intro h; exact absurd h.1 (by decide)
  have hgenD : GGKacGenericClD ⟨.twD, r, nf⟩ p := ⟨hgenCl, Or.inr rfl, h4⟩
  intro L' _ _ ψ hψ hker hcomm
  have hQpin : LargeEvenRawDatum ⟨.twD, r, nf⟩
      (fun R _ _ _ => Nonempty (R ≃* LargeEvenProj
        (LargeEvenOmega (LargeEvenQMinus (r - 1) b c)))) := by
    dsimp only [LargeEvenRawDatum]
    rw [if_neg (show r ≠ 2 by omega), if_neg (show r ≠ 3 by omega)]
    exact ⟨K, inferInstance, inferInstance, hKcard, b, c, hirr, ⟨MulEquiv.refl _⟩⟩
  have hSchur := hS p ⟨.twD, r, nf⟩ hlab hgenD _ hQpin
  obtain ⟨R₀, _hR₀grp, _I₀, _F₀, hQ₀, hCop⟩ := largeEvenRawDatum_exists hSchur
  obtain ⟨e₀⟩ := hQ₀
  exact hCop L' (e₀.symm.toMonoidHom.comp ψ) (e₀.symm.surjective.comp hψ) (by
    intro l hl
    apply hker
    have h1 : e₀.symm (ψ l) = 1 := hl
    have := congrArg e₀ h1
    simpa using this) hcomm

theorem ggK0MainBS_clD (hS : GGK0Schur GGKacGenericClD) :
    GGK0MainBS GGKacGenericClD GGMultValidCl := by
  classical
  intro p lab hlab hgen
  intro Q hQ
  obtain ⟨tag, r, nf⟩ := lab
  have hp : p.Prime := hgen.1.1
  have hp2 : p ≠ 2 := hgen.1.2.1
  have hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1 := hgen.1.2.2.1
  have htag : tag = .D ∨ tag = .twD := hgen.2.1
  have h4 : 4 ≤ r := hgen.2.2
  rcases htag with hD | htwD
  · subst hD
    exact ggK1D_raw_plus h4 Q hQ (fun K _ _ hK =>
      ggK1_cont_of_core (ggK1D_coprime_center_plus hS hp hp2 hdvd hlab h4 hK)
        (ggK1D_core_plus hp hp2 hdvd hlab h4 hK))
  · subst htwD
    exact ggK1D_raw_minus h4 Q hQ (fun K _ _ hK b c hirr =>
      ggK1_cont_of_core (ggK1D_coprime_center_minus hS hp hp2 hdvd hlab h4 hK hirr)
        (ggK1D_core_minus hp hp2 hdvd hlab h4 hK hirr))

end CFSG.StandardType

end
