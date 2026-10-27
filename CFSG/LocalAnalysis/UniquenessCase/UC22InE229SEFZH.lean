module

public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229SEFZSm
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsIdent
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsSolvableKID
import CFSG.RankThree.PartOne.S12.Sec1511SPEFStar
public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229SEFZR1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.AGLEmbeddingD2 (D2HeisLocalAt)

theorem goodZ_of_d2Heis {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {i : TauCeti.CFSGIndex}
    (hH : D2HeisLocalAt i fun q => q = p) {X : Type} [Group X] [Finite X]
    (hO : CFSG.pPrimeCore p X = ⊥) {N : Subgroup X} (hN : IsStronglyPEmbedded p N)
    (hK : Nonempty (↥(CFSG.generalizedFitting X) ≃* i.Group)) :
    InvolutionCentralizerHasPElementOutside p N ∧ AbelianPSubgroupLeFStar p N := by
  obtain ⟨-, -, hKn, hKC⟩ := CFSG.RankThree.PartOne.Sec1511.spe_fstar (p := p) Fact.out hO hN
  obtain ⟨P, hP, hPN⟩ := hN.exists_isSylowOf_le
  let R : Sylow p X := hP.2.1.toSylow (by simpa [Subgroup.relIndex_top_right] using hP.2.2)
  have hRcoe : (R : Subgroup X) = P :=
    IsPGroup.toSylow_coe hP.2.1 (by simpa [Subgroup.relIndex_top_right] using hP.2.2)
  have hRN : (R : Subgroup X) ≤ N := hRcoe ▸ hPN
  obtain ⟨-, hcard, hmax, hC, hZ, hcomm, -⟩ := hH X _ hKn hKC hK p rfl R
  exact goodZ_of_heis hp2 hN hRN hcard hmax hC hZ hcomm

section Certificates


theorem stronglyEmbeddedFiveZ_of_kFacts (hId : CFSG.AGLEmbedding.KFactSmallIdent)
    (hLie : CFSG.AGLEmbedding.KFactOneLieIdent)
    (hCyc : CFSG.LocalAnalysis.RankThreeTheoremC.StronglyEmbeddedCyclicOuterKFact)
    (hMcL : D2HeisLocalAt (.sporadic .McL) fun q => q = 5)
    (hJ4 : D2HeisLocalAt (.sporadic .J4) fun q => q = 11) :
    StronglyEmbeddedFiveZ := by
  intro p hp hp5 X _ _ hX hO h2 N hN
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  obtain ⟨hKs, -, hKn, hKC⟩ := CFSG.RankThree.PartOne.Sec1511.spe_fstar hp hO hN
  haveI : (CFSG.generalizedFitting X).Normal := hKn
  rcases identification_of_isStronglyPEmbedded hId hLie hCyc hp hp5 hX hO h2 hN with
    hS | ⟨d, hd, ⟨e⟩⟩ | ⟨rfl, hv, ⟨e⟩⟩
  · rcases hS with ⟨d, hd, ⟨e⟩⟩ | ⟨d, ⟨q, hqp, -, hdq⟩, ⟨e⟩⟩ | hA | ⟨rfl, -⟩ |
      ⟨rfl, hT | hM | hF⟩ | ⟨rfl, hJ⟩
    ·
      obtain ⟨f⟩ := CFSG.AGLEmbedding.nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hd
      exact Or.inl (goodZ_psl2GF hp2 (by norm_num) hO hN (e.trans f))
    ·
      exact Or.inl (goodZ_unitary hp2 ⟨q, hqp, hdq⟩ hO hN e)
    ·
      exact Or.inl (goodZ_of_sylow hp2 (sylow_of_isAltTwoP hp5 hKC hA) N)
    ·
      omega
    ·
      exact Or.inl (goodZ_of_sylow hp2 (sylow_of_isTitsGroup hKC hT) N)
    ·
      exact Or.inl (goodZ_of_d2Heis hp2 hMcL hO hN hM)
    ·
      exact Or.inr (coverHasLargeTwoLocal_of_isFi22 hKs hF)
    ·
      exact Or.inl (goodZ_of_d2Heis hp2 hJ4 hO hN hJ)
  · rcases hd with ⟨n, hn, hdn⟩ | ⟨hU, -⟩ | ⟨rfl, -⟩
    ·
      obtain ⟨f⟩ := CFSG.AGLEmbedding.nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hdn
      exact Or.inl (goodZ_psl2GF hp2 (by omega) hO hN (e.trans f))
    ·
      exact Or.inl (goodZ_unitary hp2 hU hO hN e)
    ·
      omega
  ·
    exact Or.inl (goodZ_of_sz32
      (CFSG.AGLEmbeddingD2.sz32Normal_of_mulEquiv ⟨.suzuki 2, hv⟩ rfl hKn hKC e) N)

end Certificates

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
