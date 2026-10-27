module

public import CFSG.LocalAnalysis.StandardType.GGQTwoAssemble
public import CFSG.LocalAnalysis.StandardType.GGQ2TwD4Aut48
public import CFSG.LocalAnalysis.StandardType.GGB48Assembly
public import CFSG.LocalAnalysis.StandardType.GGStdSpSixExcl
public import CFSG.LocalAnalysis.StandardType.GGQTwoNoWeylA3Free
public import CFSG.LocalAnalysis.StandardType.GGTBJConfigFacts
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyDichotomy
public import CFSG.LocalAnalysis.StandardType.GGF4QTwoHypA
public import CFSG.CGT.Timmesfeld75.NodeAux

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Module

theorem ggQ2_rankFour_automizer_ge
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig 3 B Bs x L D J) (hlab : GGInnerDiagOnLabel GGLabQTwo 3 Bs L)
    (hcard : Nat.card ↥Bs = 3 ^ 4) :
    48 ≤ Nat.card ↥(ggAutomizer L Bs) := by
  rcases ggQTwoEnds_of_card_bstar hcfg hcard hlab with hsp | hA | htwD
  · exact absurd hsp (not_ggInnerDiagOnLabel_sp6 hcfg)
  · obtain ⟨n, hn, hA⟩ := hA
    let m := n - 2
    have hm : m = 3 ∨ m = 4 := by
      rcases hn with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    have hperf : commutator L = ⊤ := hA.1
    have hnorm : Bs ≤ Subgroup.normalizer (L : Set G) := by
      obtain ⟨-, lab, -, hraw⟩ := hlab
      obtain ⟨R, _, I, F, hQ⟩ := largeEvenRawDatum_exists hraw
      obtain ⟨θ, hθ⟩ := hQ.2.2
      exact hθ.2.1
    have hZ : Subgroup.center ↥L = ⊥ := by
      refine center_eq_bot_of_f4EndMarking
        (P := fun lab => lab.tag = .A ∧ lab.rank = n ∧ lab.n = 1) ?_ hA
      intro lab hl
      rcases hn with rfl | rfl
      · exact ⟨Or.inl ⟨hl.1, hl.2.1⟩, hl.2.2⟩
      · exact ⟨Or.inr (Or.inl ⟨hl.1, hl.2.1⟩), hl.2.2⟩
    have hM : StatedClassicalModel ↥L .PSL (n + 1) 2 1 :=
      statedClassicalModel_of_markingA hA hZ
    have e : ↥L ⧸ Subgroup.center ↥L ≃* ↥L :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    have hmod : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL (m + 1 + 1 + 1) 2 1 := by
      rcases hn with rfl | rfl
      · exact CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e.symm hM
      · exact CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e.symm hM
    have hBs : GGBstar 3 B Bs := hcfg.2.1
    exact ggB48_of_sl_two (N := L) hm hBs hperf hnorm hmod
  · exact ggQ2_twD4_automizer_ge48 hcfg hlab hcard htwD

theorem ggQTwoNoWeylA3Free_holds
    : GGQTwoNoWeylA3Free := by
  intro G _ _ p B Bs x L D J hS hcard
  have hp3 : p = 3 := ggQ2_pThree hS
  subst hp3
  have h := ggQ2_rankFour_automizer_ge hS.1.1 hS.2.1 hcard
  omega

end CFSG.StandardType

end
