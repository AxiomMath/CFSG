module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeReturnAssembly
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeStepA

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos
  CFSG.StandardType.RCKC1 CFSG.StandardType.GGFinModel CFSG.StandardType.LieCore
open CFSG.Open (StatedLieTag StatedLieAdmissible)
open scoped commutatorElement
open CFSG.StandardType.ExcFramesHalf (IsToralSubgroup)

theorem rckFlag_of_classicalModel
    (hF : RCKLemmaF) {X : Type} [Group X] [Finite X] {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* X} {p : ℕ} {G₀ A B₁ D J L R Rm K : Subgroup X} {e : X}
    (h : RCKRPConfig t n f ψ p G₀ A B₁ D J L R Rm K e) (hModel : RCKClassicalModelID K B₁) :
    GGRootPosFlag K R := by
  obtain ⟨hBK, d, hdD, -, hJc⟩ := rckRP_stepA h
  unfold RCKRPConfig at h
  rcases h with
    ⟨hGG, hOddG0, hp, hp2, hAel, hB1A, hDB1, hDcard, hAnorm, hMarkG0, hB1J, hB1Jc,
      hp4, hA2, hrank2, hAc, hB1L, hMarkL, hJcomp, hOddJ, hLG0, hx, hDnotc, hJcompL,
      hJnotA6, hRJ, hRmJ, hRootJ, heD, he1, hKcomp, hJK, hOddK⟩
  have hB1el : IsElemAbelian p B₁ := by
    have := hAel.1
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => hAel.2 x (hB1A hx)⟩
    have hc := congrArg Subtype.val
      (mul_comm' (⟨(a : X), hB1A a.2⟩ : A) ⟨(b : X), hB1A b.2⟩)
    exact Subtype.ext (by simpa using hc)
  have hdB1 : d ∈ B₁ := hDB1 hdD
  have hrank : p ^ 2 * Nat.card ↥(B₁ ⊓ Subgroup.centralizer (J : Set X)) ≤ Nat.card B₁ := by
    rw [hB1Jc, hDcard]
    have hp22 : p ^ 2 * p ^ 2 = p ^ 4 := by rw [← pow_add]
    rw [hp22]
    exact hp4
  exact hF X p K J R Rm B₁ d hp hp2 hB1el hdB1 hBK hB1J hrank hModel hOddK hJc hJnotA6
    hRJ hRmJ hRootJ

theorem rckNbr_of_classicalModelII
    (hF : RCKLemmaFII) {X : Type} [Group X] [Finite X] {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* X} {p : ℕ} {G₀ A B₁ D J L R Rm K : Subgroup X} {e : X}
    (h : RCKRPConfig t n f ψ p G₀ A B₁ D J L R Rm K e) (hRow : GGSixRCKJRow .II J)
    (hR2 : Nat.card R = 2) (hModel : RCKClassicalModelID K B₁) :
    GGRootPosNbr K R := by
  obtain ⟨hBK, d, hdD, -, hJc⟩ := rckRP_stepA h
  unfold RCKRPConfig at h
  rcases h with
    ⟨hGG, hOddG0, hp, hp2, hAel, hB1A, hDB1, hDcard, hAnorm, hMarkG0, hB1J, hB1Jc,
      hp4, hA2, hrank2, hAc, hB1L, hMarkL, hJcomp, hOddJ, hLG0, hx, hDnotc, hJcompL,
      hJnotA6, hRJ, hRmJ, hRootJ, heD, he1, hKcomp, hJK, hOddK⟩
  have hB1el : IsElemAbelian p B₁ := by
    have := hAel.1
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => hAel.2 x (hB1A hx)⟩
    have hc := congrArg Subtype.val
      (mul_comm' (⟨(a : X), hB1A a.2⟩ : A) ⟨(b : X), hB1A b.2⟩)
    exact Subtype.ext (by simpa using hc)
  have hdB1 : d ∈ B₁ := hDB1 hdD
  have hrank : p ^ 2 * Nat.card ↥(B₁ ⊓ Subgroup.centralizer (J : Set X)) ≤ Nat.card B₁ := by
    rw [hB1Jc, hDcard]
    have hp22 : p ^ 2 * p ^ 2 = p ^ 4 := by rw [← pow_add]
    rw [hp22]
    exact hp4
  exact hF X p K J R Rm B₁ d hp hp2 hB1el hdB1 hBK hB1J hrank hModel hOddK hJc hRow
    hJnotA6 hRJ hRmJ hRootJ hR2

theorem rckRPAt_exceptional_of
    (hF : RCKLemmaF) (hT : RCKExcToral) (hV : RCKExcCaseVReduction) (hN : RCKExcCaseVNbr) :
    RCKRPAt GGExcFive := by
  intro X _ _ t n f ψ p G₀ A B₁ D J L R Rm K e ht h
  by_cases hKJ : K = J
  · exact Or.inl hKJ
  · by_cases hTor : RCKToralFrame t f p G₀ A
    · rcases hT X t n f ψ p G₀ A B₁ D J L R Rm K e ht h hKJ hTor with hmodel | hnbr
      · exact Or.inr (Or.inr (rckFlag_of_classicalModel hF h hmodel))
      · exact Or.inr (Or.inl hnbr)
    · exact Or.inr (Or.inl (hN X t n f ψ p G₀ A B₁ D J L R Rm K e ht h hKJ
        (hV X t n f ψ p G₀ A B₁ D J L R Rm K e ht h hTor)))

theorem rckRPIIAt_exceptional_of
    (hF : RCKLemmaFII) (hT : RCKExcToralII) (hV : RCKExcCaseVReduction) (hN : RCKExcCaseVNbr) :
    RCKRPIIAt GGExcFive := by
  intro X _ _ t n f ψ p G₀ A B₁ D J L R Rm K e ht hRow hR2 h
  by_cases hKJ : K = J
  · exact Or.inl hKJ
  · by_cases hTor : RCKToralFrame t f p G₀ A
    · rcases hT X t n f ψ p G₀ A B₁ D J L R Rm K e ht hRow hR2 h hKJ hTor with hmodel | hnbr
      · exact Or.inr (rckNbr_of_classicalModelII hF h hRow hR2 hmodel)
      · exact Or.inr hnbr
    · exact Or.inr (hN X t n f ψ p G₀ A B₁ D J L R Rm K e ht h hKJ
        (hV X t n f ψ p G₀ A B₁ D J L R Rm K e ht h hTor))

theorem rck_exc_toral_of
    (h1 : RCKExcRelOneAt GGExcFive) (h2 : RCKExcReturnModelAt) : RCKExcToral :=
  fun X _ _ t n f ψ p G₀ A B₁ D J L R Rm K e ht h hKJ hT =>
    h2 h1 X t n f ψ p G₀ A B₁ D J L R Rm K e ht h hKJ hT

theorem rck_exc_toralII_of
    (h1 : RCKExcRelOneAt GGExcFive) (h2 : RCKExcReturnModelAt) : RCKExcToralII :=
  fun X _ _ t n f ψ p G₀ A B₁ D J L R Rm K e ht _ _ h hKJ hT =>
    h2 h1 X t n f ψ p G₀ A B₁ D J L R Rm K e ht h hKJ hT

end CFSG.StandardType.RCKRP
