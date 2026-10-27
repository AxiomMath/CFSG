module

public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeProp1010
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeU52Models
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.GGQ2Prime

open Subgroup CFSG.Open CFSG.Models

theorem u52SimpleSix : U52SimpleSix := by
  intro K _ _ hK
  have hmod := model_SU K 5 (by norm_num) hK
  refine ⟨CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hmod, ?_⟩
  rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_five_two hmod]
  norm_num

theorem u42Nonabelian : U42Nonabelian := by
  intro K _ _ hK
  have hmod := model_SU K 4 le_rfl hK
  have hcard := CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_four_two hmod
  haveI : Finite (StatedProj (StatedSU 4 (2 ^ 1) K)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  haveI := CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hmod
  exact exists_noncomm_of_simple Nat.prime_two (by rw [hcard]; norm_num) (by rw [hcard]; norm_num)

theorem prop_10_10_not_component_closed {G : Type} [Group G] [Finite G]
    {B L X Xk Tk : Subgroup G} {x zn : G} (h : O1ppData B x zn L X Xk Tk) :
    ¬ CFSG.Open.IsComponentOf (O1ppXBar x zn X) ⊤ :=
  prop_10_10_not_component u52SimpleSix u42Nonabelian h

end CFSG.GGQ2Prime
