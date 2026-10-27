module

public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrA
public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrLabelAux
public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrLabelAuxInn
public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrLabelAuxFour
public import CFSG.LocalAnalysis.StandardType.GGQTwoJoinDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEsu
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrEnnolaLabel

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly CFSG.Blueprint CFSG.ClassicalInvolution.Phan
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem qTwoNbrLabel_nonSplit
    {B Bs L D J : Subgroup G} {x : G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) (hTCJ : GGTCJKnown) {y : G} {K : Subgroup G}
    (hnbr : GGNbr 3 B x D J y K) (hJK : J ≤ K) {t : ℕ} (ht : 4 ≤ t)
    (hJ : LieModel (↥J ⧸ Subgroup.center ↥J) .PSU t 2 1) : ¬ GGSplitLie 3 K := by
  intro hs
  obtain ⟨lab, hΛ, hhas, hdvd⟩ := ggSplitLie_label Nat.prime_three (by norm_num) hs
  have h1 := qTwoNbr_field hcfg hTCJ hnbr hJK ht hJ lab hΛ hhas
  rw [h1] at hdvd
  norm_num at hdvd

theorem qTwoNbr_label
    {B Bs L D J : Subgroup G} {x : G} {𝒦 : Finset (Subgroup G)}
    (hG : QTwoJoinGuard 3 B Bs x L D J 𝒦) (hEn : GGSecFiveNSEnnolaInput) (hTCJ : GGTCJKnown)
    {y : G} {K : Subgroup G} (hnbr : GGNbr 3 B x D J y K)
    (hA : ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦) (hJK : J ≤ K) {t : ℕ} (ht : 4 ≤ t)
    (hJ : LieModel (↥J ⧸ Subgroup.center ↥J) .PSU t 2 1) :
    ¬ GGSplitLie 3 K ∧ GGInnerDiagOnLabel ggRowP_ESU 3 Bs K ∧
      ∃ d : ℕ, 5 ≤ d ∧ LieModel (↥K ⧸ Subgroup.center ↥K) .PSU d 2 1 := by
  have hcfg := hG.1
  have hns : ¬ GGSplitLie 3 K := qTwoNbrLabel_nonSplit hcfg hTCJ hnbr hJK ht hJ
  obtain ⟨ι, M, e, hpres, hAn, -⟩ := hG.2.2.2
  have hesu : GGInnerDiagOnLabel ggRowP_ESU 3 Bs K :=
    ggX_esu_of_nonSplit hEn hcfg hG.2.2.1 hpres hAn (Or.inr ⟨⟨y, hnbr⟩, hA⟩) hns
  refine ⟨hns, hesu, ?_⟩
  have hfield := qTwoNbr_field hcfg hTCJ hnbr hJK ht hJ
  obtain ⟨d, hd4, hKd⟩ := qTwoNbrLabel_lieModel hesu hfield
  refine ⟨d, ?_, hKd⟩
  by_contra hlt
  obtain rfl : d = 4 := by omega
  obtain ⟨hperf, hN⟩ := qTwoNbrLabel_perfect_normalizer hesu
  have hxBs : x ∈ Bs := hcfg.1.1.2.1.1 hcfg.1.1.1.2.2.2.2.2.2.1.2.1
  have hx3 : x ^ 3 = 1 := hcfg.1.1.2.1.2.1.2 x hxBs
  exact qTwoNbrLabel_four_false hnbr hxBs hx3 hperf hN (qTwoNbr_component hcfg hnbr hJK) hKd

end CFSG.StandardType.QTwo

end
