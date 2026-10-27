module

public import CFSG.RankThree.PartTwo.Sec15.Gagen155Y1Defs
import CFSG.RankThree.PartTwo.Sec15.Gagen155Y1Close
import CFSG.RankThree.PartTwo.Sec15.Gagen155Y1Chain
import CFSG.RankThree.PartTwo.Sec14.Item148Res7ProofPoint
public import CFSG.RankThree.PartTwo.Sec17.RouteWire14
public import CFSG.RankThree.PartTwo.Sec4.Census.Open46
public import CFSG.RankThree.PartTwo.Sec4.Item41Narrow

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem step155HostE0W_of_y1 (h1 : Sec4.Item4_1LargePrime) (h2 : Sec4.Item4_1ThreeCover)
    (h43 : Sec4.Item4_3) (hin : Sec4.Census.CoverInputs46) (h142 : Concl142S14)
    (h1444 : Item1444S14) (h143 : Y1SecondFormExcl) {A L : Subgroup G} {c : G}
    (hR : Sec15R G A c L)
    (hW : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) (hcL : c ∉ L) (hres : Step155HostE0WRes1 A c L) :
    Step155HostE0W A c L := by
  intro h X K Y M T P hC hmax hab hE h146 hRP hIX
  have h3L : 3 ∣ Nat.card L :=
    Sec14.three_dvd_card_of_types148
      (hR.chosen136.2 c hR.zpowers_mem_omegaA L hR.mem_lA).1
  have hNL : Subgroup.normalizer (Subgroup.zpowers c : Set G) ≤
      Subgroup.normalizer (L : Set G) :=
    Sec14.Res7Point.normalizer_zpowers_le148 hR.toSec14Std hR.zpowers_mem_omegaA hR.mem_lA h3L
  have hWL : Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) :=
    (le_inf le_rfl (hW.trans hNL)).trans Subgroup.inf_normalizer_le_normalizer_inf
  by_cases hres1 : Res1At A c L M
  · exact hres h X K Y M T P hC hmax hab hE h146 hRP hIX hres1
  · refine Gagen155Y1.layerOddPreimage_le_of_balComp (h142 G A c L h) (h1444 G A c L h) h hC
      hE h146 hRP hIX ?_
    intro g hg hgZ hodd B hBA hfree hcon
    by_contra hcomm
    obtain ⟨hBeq, Yc, hYcomp, hcY, hYbot⟩ :=
      Gagen155Y1.eq_inf_of_not_isPConstrained h1 h2 h43 hin h143 hR hW h9 hcL hWL
        hBA hfree hcon
    subst B
    exact hres1 ⟨hBA, hfree, hcon, ⟨Yc, hYcomp, hcY, hYbot⟩, g, hg, hgZ, hodd, hcomm⟩

end CFSG.RankThree.PartTwo.Sec15
