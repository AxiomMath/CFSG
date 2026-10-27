module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIIE6Action
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIINativeLinear
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIINativeMinus
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeStepA

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.StandardType


theorem k2At_of_e6_two_compConfig
    {X : Type} [Group X] [Finite X] {n p : ℕ}
    {ψ : (ggU .E6 n 1).K →* X} {G₀ A B₁ D J L K : Subgroup X} {e r : X}
    {V : Subgroup X} (hcfg : RCKRP.RCKCompConfig .E6 n 1 ψ p G₀ A B₁ D J L K e)
    (hrow : GGSixRCKJRow .III J)
    (hFour : FourAt J V r) (hCore : CoreCommAt J V r) (hShort : ShortAt J r) :
    K2At K V r := by
  have hmodel := e6_two_compConfig_linear_or_minus_modelID hcfg
  obtain ⟨-, -, hp, hp2, hA, hBA, hDB, hDcard, hAN, -, hBNJ, hBCJ, hBcard, -, -, -, -, -,
    hJcomp, hOddJ, -, -, -, -, -, heD, hene, hKcomp, hJK, hOddK⟩ := hcfg
  obtain ⟨hBNK, d, hdD, -, hJd⟩ := RCKRP.le_normalizer_and_exists_isComponentOf_of_plane
    hp hA hBA hDB hDcard hAN hBNJ hJcomp heD hene hKcomp hJK
  have hdB : d ∈ B₁ := hDB hdD
  rcases hmodel with hlinear | hminus
  · exact (false_of_row_III_of_linear_modelID hp hp2 (fun b hb => hA.2 b (hBA hb))
      hBNK hdB hlinear hJd hrow).elim
  · have hrank : p ^ 2 * Nat.card ↥(B₁ ⊓ Subgroup.centralizer (J : Set X)) ≤ Nat.card B₁ := by
      rw [hBCJ, hDcard]
      calc p ^ 2 * p ^ 2 = p ^ 4 := by ring
        _ ≤ Nat.card B₁ := hBcard
    exact k2At_of_row_III_of_minus_modelID hp hp2 (CFSG.Open.IsElemAbelian.mono hA hBA)
      hdB hBNK hrank hminus hJd hrow hOddJ hOddK hJK hFour hCore hShort

end CFSG.StandardType.RCKC1
