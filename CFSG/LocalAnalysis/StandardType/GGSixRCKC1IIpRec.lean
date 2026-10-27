module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpRecDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeGlue

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos
  CFSG.StandardType.RCKRP
open CFSG.Open (StatedLieTag StatedLieAdmissible)

theorem rckIIpRecognition_of_at
    (hC : RCKIIpAt RCKClassicalTag) (hE : RCKIIpAt GGExcFive) : RCKIIpRecognition := by
  intro X _ _ t n f ψ p G₀ A B₁ D J L hrow hpres hodd hprime hne2 habel hB1A hDB1 hcardD hAnorm
    hmarkG hnormJ hinf hpow hAnorm2 hrankA hbot hnormL hmarkL hcompJ hoddJ hLG0 hex hnotD hcompJL
    hisEmpty e heD hene K hcompK hJK hoddK
  have hcfg : RCKCompConfig t n f ψ p G₀ A B₁ D J L K e :=
    ⟨hpres, hodd, hprime, hne2, habel, hB1A, hDB1, hcardD, hAnorm, hmarkG,
      hnormJ, hinf, hpow, hAnorm2, hrankA, hbot, hnormL, hmarkL, hcompJ, hoddJ, hLG0, hex,
      hnotD, hcompJL, hisEmpty, heD, hene, hcompK, hJK, hoddK⟩
  unfold GGPresentsG0 at hpres
  have hadm : StatedLieAdmissible t n 2 f := hpres.1.1
  have hrank : 2 ≤ (ggU t n f).D.rank := hpres.1.2
  rcases rckRPG_tag_trichotomy t n f hadm hrank with hcls | hexc
  · exact hC X t n f ψ p G₀ A B₁ D J L K e hcls hrow hcfg
  · exact hE X t n f ψ p G₀ A B₁ D J L K e hexc hrow hcfg

theorem rckLemmaFIIp_of_at
    (h : ∀ t, RCKClassicalTag t → RCKLemmaFIIpAt t) : RCKLemmaFIIp := by
  intro X _ _ p K J B d hp hp2 hBab hdB hBK hBJ hrank hmodel hodd hcomp hoddJ hrow
  rcases hmodel with ⟨t, m, g, φ, ht, hg, hr, hk, hdiag⟩
  exact h t ht X p K J B d hp hp2 hBab hdB hBK hBJ hrank ⟨m, g, φ, hg, hr, hk, hdiag⟩ hodd hcomp
    hoddJ hrow

end CFSG.StandardType.RCKC1
