module

public import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseRankFive
public import CFSG.LocalAnalysis.StandardType.GGNbrD4TwoUnitaryHigher
public import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseTwoAFiveE
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoBridge
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLExc11R
public import CFSG.LocalAnalysis.StandardType.GGNsq2U62
public import CFSG.LocalAnalysis.StandardType.GGResidualRk1FrameRest
import CFSG.LocalAnalysis.StandardType.GGSecFiveNSQ2U62Setup
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseOrthFrame

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section Facts


theorem GGSecFiveRouteCfg.lt_bstar_of_D4two_nbr_of_unitarySixTwo_of_facts
    (hT : GGSecFiveE6QTwoTimmesfeldInput) (hTB : GGTBFixInput)
    (hU62 : GGU62OuterDiagInput) (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) (hns : ¬ GGSplitLie p L)
    (hA : ¬ GGIsWeylMatrixA M) {y : G} {X : Subgroup G} (hnb : GGNbr p B x D J y X)
    (hmark : GGInnerDiagOnLabel
      (fun p lab => ggRowP_EOmP p lab ∧ lab.n = 1 ∧ lab.rank = 4) p Bs X)
    (hbase : GGInnerDiagOnLabel
      (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5) p Bs L) :
    B < Bs := by
  classical
  rcases lt_or_eq_of_le hcfg.1.1.2.1.1 with hlt | hEq
  · exact hlt
  · obtain ⟨lab, -, -, R, _, I, F, θ, ⟨-, hN, -⟩⟩ :=
      largeEvenMarking_exists_hasLabel hmark
    obtain ⟨rfl, hCard, -⟩ :=
      hcfg.1.1.card_bstar_twoLocalRank_of_D4two_nbr_of_eq hnb hRig hmark hN hEq
    by_cases hD : NSJoin.NSTypeD M
    · have hFix : ∀ b : Bs, (∀ φ ∈ ggAutomizer L Bs, φ b = b) →
          (b : G) ∈ Subgroup.zpowers x := by
        intro b hb
        exact hTB G 3 B Bs x L D J hcfg.1.1 hcfg.1.2.1 hcfg.1.2.2.1
          hcfg.1.2.2.2.1 y X hnb (hcfg.2.1 y X hnb) (Or.inr hcfg.2.1) b hb
      have hSix := (nsQ2U62_card_D hcfg hFix hbase hpres hD).1
      rw [hCard] at hSix
      norm_num at hSix
    · have hE := GGIsWeylMatrixE.of_not_typeA_not_typeD hpres.1 h3 hA hD
      exact ((ne_of_lt (hcfg.lt_bstar_of_twA5_typeE hT hTB hU62 hpres hE hns hbase)) hEq).elim

end Facts

section Native


theorem GGSecFiveRouteCfg.lt_bstar_of_D4two_nbr_of_unitarySixTwo
    (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) (hns : ¬ GGSplitLie p L)
    (hA : ¬ GGIsWeylMatrixA M) {y : G} {X : Subgroup G} (hnb : GGNbr p B x D J y X)
    (hmark : GGInnerDiagOnLabel
      (fun p lab => ggRowP_EOmP p lab ∧ lab.n = 1 ∧ lab.rank = 4) p Bs X)
    (hbase : GGInnerDiagOnLabel
      (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5) p Bs L) :
    B < Bs :=
  hcfg.lt_bstar_of_D4two_nbr_of_unitarySixTwo_of_facts
    ggSecFiveE6QTwoTimmesfeldInput_holds ggTBFixInput_holds ggU62OuterDiagInput_holds
    hRig hpres h3 hns hA hnb hmark hbase


theorem GGSecFiveRouteCfg.ne_bstar_of_D4two_nbr_of_center_ne_bot
    (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) (hnsL : ¬ GGSplitLie p L)
    (hA : ¬ GGIsWeylMatrixA M) {y : G} {X : Subgroup G} (hnb : GGNbr p B x D J y X)
    (hmark : GGInnerDiagOnLabel
      (fun p lab => ggRowP_EOmP p lab ∧ lab.n = 1 ∧ lab.rank = 4) p Bs X)
    (hZ : Subgroup.center X ≠ ⊥) : B ≠ Bs := by
  intro hEq
  obtain ⟨lab, -, -, R, _, I, F, θ, ⟨-, hN, -⟩⟩ :=
    largeEvenMarking_exists_hasLabel hmark
  obtain ⟨rfl, -, hMu⟩ :=
    hcfg.1.1.card_bstar_twoLocalRank_of_D4two_nbr_of_eq hnb hRig hmark hN hEq
  have htwo := hcfg.unitary_baseLabel_field_two_singular_of_D4two_nbr_eq_center
    hRig hnb hmark hEq hZ hpres h3 hnsL
  have hsix := hcfg.1.1.innerDiagOnLabel_unitary_rank_five_of_singular_two htwo
    (by rw [hMu]; decide)
  exact (ne_of_lt (hcfg.lt_bstar_of_D4two_nbr_of_unitarySixTwo
    hRig hpres h3 hnsL hA hnb hmark hsix)) hEq

theorem GGSecFiveRouteCfg.center_eq_bot_of_D4two_nbr
    (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) (hnsL : ¬ GGSplitLie p L)
    (hA : ¬ GGIsWeylMatrixA M) {y : G} {X : Subgroup G} (hnb : GGNbr p B x D J y X)
    (hmark : GGInnerDiagOnLabel
      (fun p lab => ggRowP_EOmP p lab ∧ lab.n = 1 ∧ lab.rank = 4) p Bs X) :
    Subgroup.center X = ⊥ := by
  by_cases hZ : Subgroup.center X = ⊥
  · exact hZ
  have hne := hcfg.ne_bstar_of_D4two_nbr_of_center_ne_bot
    hRig hpres h3 hnsL hA hnb hmark hZ
  have hlt : B < Bs := (lt_iff_le_and_ne).mpr ⟨hcfg.1.1.2.1.1, hne⟩
  exact hcfg.1.1.center_eq_bot_of_D4two_of_lt hlt hmark

theorem ggRk1ConclEx_of_D4two
    (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) {X : Subgroup G}
    (hXw : X = L ∨ GGSecFiveWeakNbr p B Bs x L D J 𝒦 X) (hnsX : ¬ GGSplitLie p X)
    (hmark : GGInnerDiagOnLabel
      (fun p lab => ggRowP_EOmP p lab ∧ lab.n = 1 ∧ lab.rank = 4) p Bs X)
    (hnsL : ¬ GGSplitLie p L) (hA : ¬ GGIsWeylMatrixA M) :
    ∀ r ∈ ggAutomizer X Bs, r ∈ ggCoxRefl M e → GGRk1ConclEx p Bs X r := by
  have hZ : Subgroup.center X = ⊥ := by
    by_cases hXL : X = L
    · subst X
      exact GGConfig.center_eq_bot_of_D4two hRig hcfg.1.1 hmark
    · obtain ⟨y, hnb⟩ := (hXw.resolve_left hXL).1
      exact hcfg.center_eq_bot_of_D4two_nbr hRig hpres h3 hnsL hA hnb hmark
  exact ggRk1ConclEx_of_orthTwoMarking hRig hcfg hpres h3 hXw hnsX
    (fun _ hl => ⟨Or.inl hl.1, hl.2.1⟩) hmark (fun _ _ _ => hZ)

end Native

end CFSG.StandardType

end
