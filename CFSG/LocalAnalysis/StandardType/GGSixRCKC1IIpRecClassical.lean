module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpRecDefs
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeStepA

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos
  CFSG.StandardType.RCKRP

theorem rckIIpAt_classical_of
    (hF : RCKLemmaFIIp) (hM : RCKCompModel) : RCKIIpAt RCKClassicalTag := by
  intro X _ _ t n f ψ p G₀ A B₁ D J L K e ht hrow hcfg
  by_cases hKJ : K = J
  · exact Or.inl hKJ
  have hmodel := hM X t n f ψ p G₀ A B₁ D J L K e ht hcfg hKJ
  unfold RCKCompConfig at hcfg
  obtain ⟨-, -, hp, hp2, hAel, hB1A, hDB1, hDcard, hAnorm, -, hB1J, hB1CJ, hB1card, -, -, -, -, -,
    hJcomp, hOddJ, -, -, -, -, -, heD, he1, hKcomp, hJK, hOddK⟩ := hcfg
  have hrank : p ^ 2 * Nat.card ↥(B₁ ⊓ Subgroup.centralizer (J : Set X)) ≤ Nat.card B₁ := by
    rw [hB1CJ, hDcard, show p ^ 2 * p ^ 2 = p ^ 4 by ring]
    exact hB1card
  obtain ⟨hBK, d, hdD, -, hJc⟩ := le_normalizer_and_exists_isComponentOf_of_plane hp hAel hB1A
    hDB1 hDcard hAnorm hB1J hJcomp heD he1 hKcomp hJK
  exact hF X p K J B₁ d hp hp2 (hAel.mono hB1A) (hDB1 hdD) hBK hB1J hrank hmodel hOddK hJc hOddJ
    hrow

end CFSG.StandardType.RCKC1
