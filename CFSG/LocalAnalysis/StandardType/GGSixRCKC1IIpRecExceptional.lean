module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpModel
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpAction
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpFPSL
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpFPOmegaMinus
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpFPOmegaPlus
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamInBCDCharTwo

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKRP
open CFSG.Open (StatedLieTag)

section Certificates


theorem rckIIpAt_excFive : RCKIIpAt GGExcFive := by
  intro X _ _ t n f ψ p G₀ A B₁ D J L K e ht hrow hcfg
  have hcfg0 := hcfg
  rcases rckIIp_config_classical_model hrow hcfg with
    hKJ | ⟨s, m, g, _hclass, hLM, hshape⟩
  · exact Or.inl hKJ
  obtain ⟨-, -, hp, hp2, hAel, hB1A, hDB1, hDc, hAnorm, -, hB1J, hB1CJ, hB1card, -,
    -, -, -, -, hJcomp, hoddJ, -, -, -, -, -, heD, hene, hKcomp, hJK, hoddK⟩ := hcfg0
  obtain ⟨hB1K, d, hdD, _hdnot, hJcompK⟩ :=
    le_normalizer_and_exists_isComponentOf_of_plane
      (p := p) (G₀ := G₀) (A := A) (B₁ := B₁) (D := D) (J := J) (K := K) (e := e)
      hp hAel hB1A hDB1 hDc hAnorm hB1J hJcomp heD hene hKcomp hJK
  have hrank : p ^ 2 * Nat.card ↥(B₁ ⊓ Subgroup.centralizer (J : Set X)) ≤ Nat.card B₁ := by
    rw [hB1CJ, hDc, show p ^ 2 * p ^ 2 = p ^ 4 by ring]
    exact hB1card
  have hdN : d ∈ Subgroup.normalizer (K : Set X) := hB1K (hDB1 hdD)
  have hD_le_A : D ≤ A := hDB1.trans hB1A
  have hB : IsElemAbelian p (Subgroup.zpowers d) :=
    hAel.mono (Subgroup.zpowers_le.mpr (hD_le_A hdD))
  have hdmem : d ∈ Subgroup.zpowers d := Subgroup.mem_zpowers d
  have hBN : Subgroup.zpowers d ≤ Subgroup.normalizer (K : Set X) :=
    Subgroup.zpowers_le.mpr hdN
  rcases hshape with ⟨rfl, hm⟩ | ⟨rfl, hm, hg⟩ | ⟨rfl, hm, hg⟩
  ·
    have hModel : RCKClassicalModelIDAt .PSL K (Subgroup.zpowers d) :=
      rckIIpAt_excFive_classicalModelIDAt_of_model ht hrow hcfg hdD hdN hLM
        (Or.inl ⟨rfl, hm⟩)
    exact rckIIp_PSL_of_classicalModelID X p K J (Subgroup.zpowers d) d hp hp2 hB hdmem hBN
      hModel hoddK hJcompK hoddJ hrow
  ·
    have hLM1 : LieModel (↥K ⧸ Subgroup.center ↥K) .POmegaMinus m 2 1 := by
      simpa only [hg] using hLM
    obtain ⟨ψM, hψMrange, hψMker, hψMdiag⟩ :=
      exists_orthogonal_two_innerDiag_presentation hp hp2 (hAel.mono hB1A) hB1K
        hKcomp.2.2.1 hoddK hLM1 (Or.inl ⟨rfl, hm⟩)
    exact rckLemmaFIIp_POmegaMinus_of_four_le
      (X := X) (p := p) (K := K) (J := J) (B := B₁) (d := d)
      hp hp2 (hAel.mono hB1A) (hDB1 hdD) hrank hm le_rfl ψM hψMrange hψMker hψMdiag
      hJcompK hoddJ hrow
  ·
    have hLM1 : LieModel (↥K ⧸ Subgroup.center ↥K) .POmegaPlus m 2 1 := by
      simpa only [hg] using hLM
    have hModel : RCKClassicalModelIDAt .POmegaPlus K B₁ :=
      rckClassicalModelIDAt_orthogonal_two_of_elemAbelian hp hp2 (hAel.mono hB1A) hB1K
        hKcomp.2.2.1 hoddK hLM1 (Or.inr ⟨rfl, hm⟩)
    exact rckLemmaFIIpAt_POmegaPlus X p K J B₁ d hp hp2 (hAel.mono hB1A) (hDB1 hdD)
      hB1K hB1J hrank hModel hoddK hJcompK hoddJ hrow

end Certificates

end CFSG.StandardType.RCKC1
