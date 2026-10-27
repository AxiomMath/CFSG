module

public import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseTwE6TwoSplit
public import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseTwoAEightE
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortGlueFSPoint
public import CFSG.LocalAnalysis.StandardType.GGFrameRouteLower
import CFSG.LocalAnalysis.StandardType.GGSecFiveBWeylInfType
import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP5TwE6
import CFSG.LocalAnalysis.StandardType.GGB36JExcE6Core
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyQFourTBSmall

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.FrameRoute


theorem GGSecFiveRouteCfg.lt_bstar_of_twE6Two_full_typeE
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) (hb1 : GGFrameTBNumerologyInput)
    (hb1' : GGFrameTBVacuousInput) (hrig : GGLabelRigidInput) (hPU : GGPumpupInput)
    (hO : GGOuterThreeRankInput) (hTCJ : GGTCJKnown)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) M e) (hE : GGIsWeylMatrixE M)
    (hmark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twE6, 0, 1⟩) 3 Bs L)
    (hcard : Nat.card Bs = 3 ^ 7) : B < Bs := by
  have hW := ggSecFiveWeylCase_of_prime_three hcfg.1.1 hcfg.2.1
  rcases hE with ⟨σ, hM⟩ | ⟨σ, hM⟩ | ⟨σ, hM⟩
  · have hW6 : GGWeylOfType 3 CoxeterMatrix.E₆ (ggAutomizerJoin L Bs 𝒦) := by
      subst hM
      exact GGWeylOfType.of_reindex ⟨e, hpres.2⟩
    have hle := hcfg.card_le_pow_of_weylOfType hTBF hWI le_rfl hW6
    rw [hcard] at hle
    norm_num at hle
  · have hJ : GGSecFiveWeylAtJoin 3 B Bs x L D J CoxeterMatrix.E₇ :=
      hcfg.weylAtJoin_of_reindex hpres σ hM
    have hq : GGInnerDiagOnLabel GGLabQTwo 3 Bs L := by
      refine largeEvenMarking_mono ?_ hmark
      rintro lab R _ I F θ ⟨rfl, hN, hInd⟩
      exact ⟨by norm_num [GGLabQTwo], hN, hInd⟩
    have hm : CFSG.StandardType.LargeEvenMarking L (fun lab _ _ _ _ _ =>
        lab.tag = .twE6 ∧ lab.rank = 0 ∧ lab.n = 1) := by
      refine largeEvenMarking_mono ?_ hmark
      rintro lab R _ I F θ ⟨rfl, -, -⟩
      exact ⟨rfl, rfl, rfl⟩
    have hN : Bs ≤ Subgroup.normalizer (L : Set G) :=
      GGDichotomy.marking_elim_const
        (largeEvenMarking_mono (fun _ _ _ _ _ _ hP => hP.2.1) hmark)
    have hP5 := TwE6Model.exists_p5Out_of_twE6 hcfg.1.1.1 hcfg.1.1.2.1
      hN hcfg.1.1.bstar_inf_centralizer_L hcard hmark
    have hstrict := (fsPoint_twE6 hTBF hWI hb1 hb1' hrig hPU hO hTCJ
      hcfg.1 hW hq hJ hm hP5).1
    refine lt_of_le_of_ne hcfg.1.1.2.1.1 ?_
    intro hEq
    rw [hEq] at hstrict
    have hpos := Nat.card_pos (α := Bs)
    omega
  · have hW8 : GGWeylOfType 3 CoxeterMatrix.E₈ (ggAutomizerJoin L Bs 𝒦) := by
      subst hM
      exact GGWeylOfType.of_reindex ⟨e, hpres.2⟩
    obtain ⟨-, hBs, -, -, -⟩ := hcfg.1.1.tableB_facts
    have hle := pow_le_card_of_weylOfType_of_two Nat.prime_three (by norm_num)
      hBs hW8 exists_elemAbelian_two_coxeterE8
    rw [hcard] at hle
    norm_num at hle

theorem GGSecFiveRouteCfg.lt_bstar_of_twE6Two_typeE
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) (hb1 : GGFrameTBNumerologyInput)
    (hb1' : GGFrameTBVacuousInput) (hrig : GGLabelRigidInput) (hPU : GGPumpupInput)
    (hO : GGOuterThreeRankInput) (hTCJ : GGTCJKnown)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hE : GGIsWeylMatrixE M)
    (hmark : GGInnerDiagOnLabel (fun p lab => ggRowP_ETwE6 p lab ∧ lab.n = 1) p Bs L) :
    B < Bs := by
  obtain ⟨hp, -, -, -, -⟩ := hcfg.1.1.tableB_facts
  obtain ⟨lab, -, -, -, -, -, -, -, ⟨⟨-, hdvd⟩, hn⟩, -⟩ :=
    largeEvenMarking_exists_hasLabel hmark
  have hp3 : p = 3 := by
    rw [hn] at hdvd
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hdvd
  subst hp3
  rcases GGConfig.lt_bstar_or_card_eq_three_pow_seven_of_twE6Two hcfg.1.1 hmark with hlt | hcard
  · exact hlt
  have hExact : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twE6, 0, 1⟩) 3 Bs L :=
    GGInnerDiagOnLabel.mono_label_of_hasLabel (fun lab hΛ _ hP => by
      have he := ltqE6c_label_eq hΛ (Or.inr hP.1.1)
      simpa only [hP.1.1, hP.2] using he) hmark
  exact GGSecFiveRouteCfg.lt_bstar_of_twE6Two_full_typeE
    hTBF hWI hb1 hb1' hrig hPU hO hTCJ hcfg hpres hE hExact hcard

end CFSG.StandardType

end
