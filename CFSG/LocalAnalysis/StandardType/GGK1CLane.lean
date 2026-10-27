module

public import CFSG.LocalAnalysis.StandardType.GGK1Cover
public import CFSG.LocalAnalysis.StandardType.GGK1CMult
public import CFSG.LocalAnalysis.StandardType.GGK1CComp
public import CFSG.LocalAnalysis.StandardType.GGK1CDvd
public import CFSG.LocalAnalysis.StandardType.GGK1CCenter
public import CFSG.LocalAnalysis.StandardType.GGK1CValid
public import CFSG.LocalAnalysis.StandardType.GGK1CLift
public import CFSG.LocalAnalysis.StandardType.GGK1CBij
public import CFSG.LocalAnalysis.StandardType.GGK1CSigma

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Polynomial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.Classical (spEnd IsReciprocalTransversal)
open CFSG.RankThree.PartOne.KCPrimary

theorem ggK1C_core {p nf r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1) (hlab : LargeEvenInLambda2 ⟨.C, r, nf⟩)
    (h2r : 2 ≤ r) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ nf) :
    GGK1Core GGMultValidCl p ⟨.C, r, nf⟩ (LargeEvenProj (LargeEvenSpGroup K r))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K r)) (LargeEvenGSpSet K r)) := by
  intro φ hφ hφp
  obtain ⟨x, hxp, rfl⟩ := ggK1C_exists_lift hlab.1 hK φ hφ hφp
  obtain ⟨m, hm⟩ := ggK1C_mult_exists (p := p) (nf := nf) (r := r) hp hp2 hlab.1 hK hdvd hxp
  exact ⟨ggMultDatumC p nf (ggMultOrd p nf) m, ggK1C_core_valid h2r hm,
    ggK1C_core_comp hp hp2 hdvd hK hm hxp, ggK1C_core_dvd hp hp2 hdvd hlab.1 hK hm hxp,
    ggK1C_core_center hp hp2 hdvd hlab.1 hK rfl hm hxp, ggK1C_core_bij hp hp2 hdvd hK hm hxp,
    ggK1C_core_sigma hp hp2 hdvd hK (by omega) hm hxp⟩

theorem ggK1C_raw_symp {p nf r : ℕ} (Q : LargeEvenRawCont)
    (hQ : LargeEvenRawDatum ⟨.C, r, nf⟩ Q)
    (hP : ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ nf →
      GGK1Cont GGMultValidCl p ⟨.C, r, nf⟩ (LargeEvenProj (LargeEvenSpGroup K r))
        (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K r)) (LargeEvenGSpSet K r))) :
    LargeEvenRawDatum ⟨.C, r, nf⟩ fun R _ I F =>
      Q R I F ∧ GGK1Cont GGMultValidCl p ⟨.C, r, nf⟩ R I := by
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  dsimp only [LargeEvenRecipeSymplectic] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQR⟩ := hQ
  refine ⟨K, i1, i2, hK, hQR, ?_⟩
  letI := i1
  letI := i2
  exact hP K hK

theorem ggK1C_coprime_center (hS : GGK0Schur GGKacGenericClC)
    {p nf r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1)
    (hlab : LargeEvenInLambda2 ⟨.C, r, nf⟩)
    {K : Type} [Field K] [Finite K] (hKcard : Nat.card K = 2 ^ nf) :
    ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* LargeEvenProj (LargeEvenSpGroup K r)),
      Function.Surjective ψ → ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
      (Nat.card (Subgroup.center L')).Coprime p := by
  have hgenCl : GGKacGenericCl ⟨.C, r, nf⟩ p := by
    change p.Prime ∧ p ≠ 2 ∧ (p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1) ∧
      (LargeEvenLieTag.C = LargeEvenLieTag.A ∨ LargeEvenLieTag.C = LargeEvenLieTag.twA ∨
        LargeEvenLieTag.C = LargeEvenLieTag.B ∨ LargeEvenLieTag.C = LargeEvenLieTag.C ∨
        LargeEvenLieTag.C = LargeEvenLieTag.D ∨ LargeEvenLieTag.C = LargeEvenLieTag.twD) ∧
      ¬ (LargeEvenLieTag.C = LargeEvenLieTag.A ∧ p ∣ r + 1 ∧ p ∣ 2 ^ nf - 1) ∧
      ¬ (LargeEvenLieTag.C = LargeEvenLieTag.twA ∧ p ∣ r + 1 ∧ p ∣ 2 ^ nf + 1)
    refine ⟨hp, hp2, hdvd, ?_, ?_, ?_⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · intro h; exact absurd h.1 (by decide)
    · intro h; exact absurd h.1 (by decide)
  have hgenC : GGKacGenericClC ⟨.C, r, nf⟩ p := ⟨hgenCl, Or.inr rfl⟩
  intro L' _ _ ψ hψ hker hcomm
  have hQpin : LargeEvenRawDatum ⟨.C, r, nf⟩
      (fun R _ _ _ => Nonempty (R ≃* LargeEvenProj (LargeEvenSpGroup K r))) := by
    dsimp only [LargeEvenRawDatum, LargeEvenRecipeSymplectic]
    exact ⟨K, inferInstance, inferInstance, hKcard, ⟨MulEquiv.refl _⟩⟩
  have hSchur := hS p ⟨.C, r, nf⟩ hlab hgenC _ hQpin
  obtain ⟨R₀, _hR₀grp, _I₀, _F₀, hQ₀, hCop⟩ := largeEvenRawDatum_exists hSchur
  obtain ⟨e₀⟩ := hQ₀
  exact hCop L' (e₀.symm.toMonoidHom.comp ψ) (e₀.symm.surjective.comp hψ) (by
    intro l hl
    apply hker
    have h1 : e₀.symm (ψ l) = 1 := hl
    have := congrArg e₀ h1
    simpa using this) hcomm

theorem ggK0MainBS_clC (hS : GGK0Schur GGKacGenericClC) :
    GGK0MainBS GGKacGenericClC GGMultValidCl := by
  classical
  intro p lab hlab hgen
  intro Q hQ
  obtain ⟨tag, r, nf⟩ := lab
  have hp : p.Prime := hgen.1.1
  have hp2 : p ≠ 2 := hgen.1.2.1
  have hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1 := hgen.1.2.2.1
  have htag : tag = .B ∨ tag = .C := hgen.2
  have hcont : (2 ≤ r) → LargeEvenInLambda2 ⟨.C, r, nf⟩ →
      ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ nf →
      GGK1Cont GGMultValidCl p ⟨.C, r, nf⟩ (LargeEvenProj (LargeEvenSpGroup K r))
        (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K r)) (LargeEvenGSpSet K r)) := by
    intro h2r hlabC K _ _ hK
    exact ggK1_cont_of_core (ggK1C_coprime_center hS hp hp2 hdvd hlabC hK)
      (ggK1C_core hp hp2 hdvd hlabC h2r hK)
  rcases htag with hB | hC
  · subst hB
    have h2r : 2 ≤ r := hlab.2.1
    exact ggK1C_raw_symp (p := p) Q hQ (hcont h2r hlab)
  · subst hC
    have h2r : 2 ≤ r := hlab.2.1
    exact ggK1C_raw_symp (p := p) Q hQ (hcont h2r hlab)

end CFSG.StandardType

end