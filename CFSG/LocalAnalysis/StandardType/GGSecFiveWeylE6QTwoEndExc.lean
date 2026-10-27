module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoEndFacts
public import CFSG.LocalAnalysis.StandardType.GGNbrLang
public import CFSG.LocalAnalysis.StandardType.GGF4ThreeNbrRankDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylKnownDefs
public import CFSG.LocalAnalysis.StandardType.GGTwE6BadWeyl
public import CFSG.LocalAnalysis.StandardType.GGFrameRouteCard
public import CFSG.LocalAnalysis.StandardType.GGF4ThreeNbrRank

public section

namespace CFSG.StandardType

open CFSG.Assembly

variable {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}

theorem GGSecFiveE6QTwoCfg.false_of_twE6
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) (hC : GGSecFiveE6QTwoCfg 3 B Bs x L D J)
    (hL : GGInnerDiagOnLabel GGTwE6BadLabel 3 Bs L) : False := by
  have hC' := hC
  obtain ⟨𝒦, hR, -⟩ := hC
  have hcfg : GGConfig 3 B Bs x L D J := hR.1.1
  obtain ⟨-, -, -, hBs, hxB, hx1, -, hLx, -, -, -⟩ := e6QTwo_config_facts hC'
  have hWeyl : GGWeylOfType 3 CoxeterMatrix.E₆ (ggAutomizer L Bs) :=
    ggTwE6Bad_weylOfType ⟨hR.1.1, hR.1.2.1, hR.1.2.2.1, hR.1.2.2.2.1, hR.1.2.2.2.2⟩ hL
  obtain ⟨f, -⟩ := hWeyl
  have hcardA : Nat.card ↥(ggAutomizer L Bs) = 51840 :=
    (Nat.card_congr f.toEquiv).symm.trans card_coxeterE6_group
  obtain ⟨-, -, -, -, -, hbound⟩ := GGSecFiveE6QTwoCfg.exists_join hC'
  obtain ⟨y, K, hnbr⟩ := exists_ggNbr hcfg.1.2.2.2.2.2.2.2 hcfg.2.2
  have hEq : ggAutomizer L Bs = ggAutomizer L Bs ⊔ ggAutomizer K Bs :=
    Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hcardA]; exact hbound y K hnbr)
  have hb : ∀ φ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs, φ ⟨x, hxB⟩ = ⟨x, hxB⟩ := by
    intro φ hφ
    rw [← hEq] at hφ
    exact ggAutomizer_apply_eq_of_le_centralizer (x := ⟨x, hxB⟩) hLx hφ
  have hb1 : (⟨x, hxB⟩ : ↥Bs) = 1 :=
    FrameRoute.eq_one_of_fix_join hTBF hWI hR.1
      (ggSecFiveWeylCase_of_prime_three hR.1.1 hR.2.1) hnbr ⟨x, hxB⟩ hb
  have hxeq : x = 1 := by
    have := congrArg Subtype.val hb1
    simpa using this
  exact hx1 hxeq

theorem GGSecFiveE6QTwoCfg.false_of_f4
    (hC : GGSecFiveE6QTwoCfg 3 B Bs x L D J) (hL : GGInnerDiagOnLabel GGF4ThreeLabel 3 Bs L) :
    False := by
  have hC' := hC
  obtain ⟨𝒦, hR, hns, ι, M, e, hP, ⟨e', hM⟩, -⟩ := hC
  have hconf : GGConfig 3 B Bs x L D J := hR.1.1
  have hM4 : GGF4ThreeMarking Bs L :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hP => hP) hL
  obtain ⟨-, -, -, hBs, hxB, hx1, -, hLx, -, hcyc, -⟩ := e6QTwo_config_facts hC'
  have hN : Bs ≤ Subgroup.normalizer (L : Set G) :=
    GGDichotomy.le_normalizer_of_innerDiagOn hR.1.2.2.1.1
  have hrank : ∀ hN : Bs ≤ Subgroup.normalizer (L : Set G),
      3 ^ 4 ≤ Nat.card (ggGamma L hN).range := by
    intro hN
    have hmul := card_range_ggGamma_mul_of Nat.prime_three hBs hxB hx1 hLx
      (fun S hSL hSp => hcyc S hSp hSL) hN
    have hlow := GGSecFiveE6QTwoCfg.three_pow_five_le_card hC'
    rw [← hmul, pow_succ] at hlow
    exact Nat.le_of_mul_le_mul_right hlow (by norm_num)
  obtain ⟨c₁, hc₁, c₂, hc₂, hr₁, hr₂, h4⟩ :=
    ggF4Three_framePair_of_rank hconf hM4 hrank
  exact ggRow_absurd_of_framePair hR hP
    (GGIsWeylMatrixE.le_three (Or.inl ⟨e', hM⟩)) le_sup_left
    ⟨c₁, hc₁, c₂, hc₂, hr₁, hr₂, h4⟩

end CFSG.StandardType

end
