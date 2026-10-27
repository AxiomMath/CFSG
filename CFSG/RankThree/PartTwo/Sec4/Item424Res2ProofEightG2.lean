module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie3ProofThree
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.RankThree.PartTwo.Sec4.Item424ProofKFacts

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace Item424Res2

theorem fixSub_conj_eq_centralizer_singleton {G : Type*} [Group G] (z : G) :
    Item426.fixSub (MulAut.conj z) = Subgroup.centralizer ({z} : Set G) := by
  ext x
  rw [Item426.mem_fixSub, MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hx
    calc x * z = z * x * z⁻¹ * z := by rw [hx]
      _ = z * x := by group
  · intro hx
    calc z * x * z⁻¹ = x * z * z⁻¹ := by rw [hx]
      _ = x := by group


theorem census424_of_g2_three {X : Type} [Group X] [Finite X] (hZ : Subgroup.center X = ⊥)
    (hG : Blueprint.ChevalleyExceptionalModel (X ⧸ Subgroup.center X) .G2 3 1) :
    Census424 X := by
  obtain ⟨-, K, _, _, hK, ⟨φ⟩⟩ := hG
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 3 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK, pow_one])
  let E : X ≃* adjointGroup Tag.G2 K :=
    (((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans
      φ).trans ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
        QuotientGroup.quotientBot)
  intro D c d J h
  exfalso
  have hc3 : c ^ 3 = 1 := h.maximal.prop.2 c h.c_mem
  have hHas : Sec11.KS11Lie2Proof.HasType424 (Item426.fixSub (MulAut.conj c)) := by
    rw [fixSub_conj_eq_centralizer_singleton]
    exact Sec11.KS11Lie2Proof.hasType424_of_mem h.mem_thetaComponentsIn h.isType424
  have hT := hHas.of_mulEquiv (Sec11.KS11Lie2Proof.fixSubCongr E (MulAut.conj c))
  rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj] at hT
  refine Sec11.KS11Lie3Proof.not_hasType424_fixSub_g2_three (z := E c) ?_ ?_ hT
  · intro h1
    exact h.c_ne_one (E.injective (h1.trans (map_one E).symm))
  · rw [← map_pow, hc3, map_one]

end Item424Res2

end CFSG.RankThree.PartTwo.Sec4
