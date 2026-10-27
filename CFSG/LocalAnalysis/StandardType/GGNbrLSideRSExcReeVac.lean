module

public import CFSG.LocalAnalysis.StandardType.GGNbrLSideRSExcVac
public import CFSG.LocalAnalysis.StandardType.GGNbrLSideKitExcl
import CFSG.LieType.ChevTwo.OppositeFixedExcReeModel
import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofReeConj
import CFSG.RankThree.PartTwo.Sec8.Item87ProofGamma
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Basic
import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporCrit
import CFSG.HardMathSupport.Dickson.SuzukiReeB.Helpers
import CFSG.Quasithin.Background.Harris.OrdinaryProofs.CoverSU3
import CFSG.HardMathSupport.Solomon.Coordinator.I14_20Alt
import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltMain
import CFSG.HardMathSupport.Solomon.Coordinator.ONCAutSix
import CFSG.HardMathSupport.Solomon.Coordinator.ONNotIso
import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Down
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma43Rest
import CFSG.HardMathSupport.Solomon.LocalBalance.Prop22
import CFSG.HardMathSupport.Solomon.LocalBalance.Sec3Statements
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Input252
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6D62
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E66
import CFSG.LieType.Chevalley.EvenOddCentralizerRadical
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyStatements
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Engine
import CFSG.Quasithin.Background.A3Structure319
import CFSG.Quasithin.Background.F9FiveStruct
import CFSG.Quasithin.Background.F9G2
import CFSG.Quasithin.Background.F9Geometry
import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
import CFSG.Quasithin.EmptyFaithful.S1421Defs
import CFSG.Quasithin.EmptyFaithful.S142Statements
import CFSG.Quasithin.H13.A5S1326
import CFSG.Quasithin.H13.A5Top
import CFSG.Quasithin.H13.J4Order
import CFSG.Quasithin.Vol2.Ch11SecAFacts02
import CFSG.Quasithin.Vol2.Ch11SecAFacts03
import CFSG.Quasithin.Vol2.Ch11StatementsB
import CFSG.Quasithin.Vol2.Ch11StatementsC
import CFSG.RankThree.PartTwo.Sec8.Steps

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LieType.Ree
open CFSG.Assembly.LowTwoRank (StatedSU)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

theorem ggNbrLSideNoPSL3_twF4
    (hDet : GGNbrLSideClsDet) (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    GGNbrLSideNoPSL3 (LargeEvenChevIDImage LargeEvenCartanF4 K (LargeEvenTwF4H a K)) := by
  classical
  intro φ hφI hφ1 hφ3 J hJ F _ _ hF4
  have hφinn := chevIDImage_subset_inn_twF4 ha K hK hφI
  have hR : CFSG.Blueprint.ReeTitsModel (LargeEvenCenterQuot (LargeEvenTwF4H a K)) .twistedF4 2
      (2 * a + 1) :=
    ⟨⟨Nat.prime_two, by omega, rfl, rfl, ⟨a, rfl⟩, by omega⟩, a, rfl,
      CFSG.StandardType.reeTitsRelationModel_largeEven a hK⟩
  obtain ⟨K', _, _, _, hK'card, ⟨eR⟩⟩ :=
    CFSG.LieType.ChevTwo.Semi.exists_mulEquiv_reeGamma ha hR
  have hZ : Subgroup.center ↥(ReeTag.F4.reeGamma K' a) = ⊥ :=
    ReeTag.large_Ree_fixed_group_center_trivial a K' hK'card
  have hconj : ∀ r : LargeEvenCenterQuot (LargeEvenTwF4H a K),
      MulAut.congr eR (MulAut.conj r) = MulAut.conj (eR r) := by
    intro r
    ext x
    simp [MulAut.congr_apply, MulAut.conj_apply, map_mul, map_inv]
  have hφ'inn : MulAut.congr eR φ ∈
      (MulAut.conj :
        ↥(ReeTag.F4.reeGamma K' a) →* MulAut ↥(ReeTag.F4.reeGamma K' a)).range := by
    obtain ⟨r, hr⟩ := MonoidHom.mem_range.1 hφinn
    refine ⟨eR r, ?_⟩
    rw [← hr]
    exact (hconj r).symm
  have hφ'3 : (MulAut.congr eR φ) ^ 3 = 1 := by rw [← map_pow, hφ3, map_one]
  have hφ'1 : MulAut.congr eR φ ≠ 1 := fun h =>
    hφ1 ((MulAut.congr eR).injective (h.trans (map_one _).symm))
  obtain ⟨y, hyconj, hy3, hy1⟩ :=
    CFSG.HardMathSupport.Dickson.SuzukiReeB.exists_eq_conj_of_mem_range hZ hφ'inn hφ'3 hφ'1
  have hyord : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  obtain ⟨eSU⟩ :=
    CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof.centralizer_mulEquiv_unitarySU
      a K' hK'card y hyord
  have hFcard : Nat.card (GaloisField 2 (2 * (2 * a + 1))) = (2 ^ (2 * a + 1)) ^ 2 := by
    rw [GaloisField.card 2 _ (by omega), ← pow_mul, mul_comm]
  have hq := (CFSG.RankThree.PartTwo.Sec8.Item87Proof.isQuasisimple_statedSU_three
    (F := GaloisField 2 (2 * (2 * a + 1))) (f := 2 * a + 1) hFcard (by omega)).1
  let E : ↥(fixSubgroup φ) ≃*
      ↥(StatedSU 3 (2 ^ (2 * a + 1)) (GaloisField 2 (2 * (2 * a + 1)))) :=
    (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroupCongrEquiv eR φ).trans
      ((MulEquiv.subgroupCongr (by rw [hyconj])).trans
        ((MulEquiv.subgroupCongr
          (CFSG.HardMathSupport.Dickson.SuzukiReeB.fixSubgroup_conj y)).trans eSU))
  have hCq : CFSG.IsQuasisimple ↥(fixSubgroup φ) :=
    CFSG.IsQuasisimple.of_mulEquiv E hq
  haveI : Finite ↥(ReeTag.F4.reeGamma K' a) := Subtype.finite
  haveI : Finite (LargeEvenCenterQuot (LargeEvenTwF4H a K)) :=
    Finite.of_injective eR eR.injective
  have hJC : J = fixSubgroup φ :=
    CFSG.HardMathSupport.Solomon.Coordinator.component_eq_of_normal_quasisimple hJ le_rfl
      (by rw [Subgroup.subgroupOf_self]; infer_instance) hCq fun H hH _ => hH
  subst hJC
  refine ⟨fun e => ?_⟩
  have hSC : CFSG.Open.StatedClassicalModel
      (↥(fixSubgroup φ) ⧸ Subgroup.center ↥(fixSubgroup φ)) .PSU 3 2 (2 * a + 1) :=
    CFSG.Quasithin.Background.Harris.OrdinaryProofs.statedClassicalModel_quotient_of_statedSU
      (e := 2 * a + 1) (K := GaloisField 2 (2 * (2 * a + 1))) (by omega) hFcard ⟨E⟩
  have hX : CFSG.Blueprint.LieModel
      (↥(fixSubgroup φ) ⧸ Subgroup.center ↥(fixSubgroup φ)) .PSU 3 2 (2 * a + 1) :=
    Or.inl ⟨by decide, hSC⟩
  exact absurd (ggNbrLSideExcl hDet hO hF4 e hX).1 (by decide)

end CFSG.StandardType

end
