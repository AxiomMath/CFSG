module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeGlue
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeStepA

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1
open CFSG.Open (StatedLieTag)

theorem rckRPAt_classical_of
    (hF : RCKLemmaF) (hM : RCKClassicalCompModel) :
    RCKRPAt RCKClassicalTag := by
  intro X _ _ t n f ψ p G₀ A B₁ D J L R Rm K e hcl h
  by_cases hKJ : K = J
  · exact Or.inl hKJ
  · right; right
    obtain ⟨hBK, d, hdD, -, hJc⟩ := rckRP_stepA h
    have hModel : RCKClassicalModelID K B₁ := hM X t n f ψ p G₀ A B₁ D J L R Rm K e hcl h hKJ
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

theorem rckRPIIAt_classical_of
    (hF : RCKLemmaFII) (hM : RCKClassicalCompModel) :
    RCKRPIIAt RCKClassicalTag := by
  intro X _ _ t n f ψ p G₀ A B₁ D J L R Rm K e hcl hRow hR2 h
  by_cases hKJ : K = J
  · exact Or.inl hKJ
  · right
    obtain ⟨hBK, d, hdD, -, hJc⟩ := rckRP_stepA h
    have hModel : RCKClassicalModelID K B₁ := hM X t n f ψ p G₀ A B₁ D J L R Rm K e hcl h hKJ
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

end CFSG.StandardType.RCKRP
