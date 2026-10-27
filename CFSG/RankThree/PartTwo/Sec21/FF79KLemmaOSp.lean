module

public import Mathlib
public import CFSG.Open.StatedDefs
public import CFSG.RankThree.PartTwo.Sec21.FF79KLemmaOGen
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix

import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256h
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2Carrier
import CFSG.RankThree.PartOne.KC.SymplecticNoninnerPlaneDescent
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Assembly.QuasithinDefs
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.Foundations
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.TopScalarLiftSquare
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ComponentClassification.OuterAutomorphisms (inner_normal inner)

theorem three_dvd_of_outer_psp {S : Type} [Group S] [Finite S] {ℓ r f : ℕ}
    (hm : StatedClassicalModel S .PSp r ℓ f)
    {α : MulAut S} (hα : α ^ 3 = 1) (hout : ∀ c : S, α ≠ MulAut.conj c) : 3 ∣ f := by
  obtain ⟨⟨hℓ, hf, hr, -⟩, k, _, _, hk, ⟨e'⟩⟩ := hm
  haveI : Finite (StatedProj (StatedSp r k)) := Finite.of_equiv S e'.toEquiv
  have hβ' : MulAut.congr e' α ^ 3 = 1 := by rw [← map_pow, hα, map_one]
  have hO := CFSG.RankThree.PartOne.KCSpComm.spOuter (K := k) hℓ hf hr hk
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hodd : Odd (orderOf (MulAut.congr e' α)) :=
    (by decide : Odd 3).of_dvd_nat (orderOf_dvd_of_pow_eq_one hβ')
  have hE : MulAut.congr e' α ∈ spSemilinearAutGroup r k :=
    CFSG.RankThree.PartOne.KCSpComm.mem_of_odd_orderOf_of_index_dvd_two _ hO.index_dvd hodd
  have hne1 : MulAut.congr e' α ≠ 1 := fun h1 =>
    hout 1 ((MulAut.congr e').injective (h1.trans (map_one _).symm) |>.trans (map_one _).symm)
  have hord : orderOf (MulAut.congr e' α) = 3 := orderOf_eq_prime hβ' hne1
  by_cases hD : MulAut.congr e' α ∈ spLinearAutGroup r k
  · exfalso
    have : (inner (StatedProj (StatedSp r k))).Normal := inner_normal _
    have hrel : (inner (StatedProj (StatedSp r k))).relIndex (spLinearAutGroup r k) ∣ 2 :=
      hO.relIndex_dvd.trans (Nat.gcd_dvd_left 2 _)
    obtain ⟨t, ht⟩ := CFSG.RankThree.PartOne.KCSpComm.mem_of_pow_eq_one_of_relIndex_dvd_two hrel
      Nat.prime_three (by norm_num) hD hβ'
    apply hout (e'.symm t)
    apply (MulAut.congr e').injective
    rw [← ht, InputsL33c.congr_conj_apply, MulEquiv.apply_symm_apply]
  · obtain ⟨h3f, -⟩ := hO.descent 3 Nat.prime_three _ hE hD hord
    exact h3f

end CFSG.RankThree.PartTwo.Sec21.FF79
