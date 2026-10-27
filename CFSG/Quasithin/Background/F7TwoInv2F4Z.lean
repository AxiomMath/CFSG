module

public import CFSG.Quasithin.Background.F7TwoInv2F4Oct
public import CFSG.Quasithin.Background.F7TwoInvSz
public import CFSG.CharacterTheory.CyclicBlocks.Family
public import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
public import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
public import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.GH74.GLS.SP.GlueDefs
public import CFSG.GH74.Statements
public import CFSG.GH74.Uniqueness.Lemma311
public import CFSG.GH74.Uniqueness.Prop38
public import CFSG.GH74.Uniqueness.Setup
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedPointHull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointFullTransport
public import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalCatSuzuki
public import CFSG.LocalAnalysis.QuasithinUnique.K1.Interface
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureConjugation
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPair
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyData
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyProper
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthLinearFrobenius
public import CFSG.Permutation.UnitaryThreeRecognition.Model
public import CFSG.Quasithin.Background.F7TwoDefs
public import CFSG.Quasithin.Background.F7TwoInvExcBasic
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModF4
public import CFSG.StronglyEmbedded.MatrixGroups.PSL2
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount

public section

namespace CFSG.Quasithin.F7Two

open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
  CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Quasithin.H13.F431.TwoF4

set_option linter.unusedSectionVars false


variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {m : ℕ}

local notation "X[" k "]" => largeReeBlockGroup K m (octBlock k)
local notation "Γ" => F4.reeGamma K m
local notation "wZ" => weylOne K * weylTwo K * weylOne K

theorem forall_invAutGen_rankOneGroupTwo (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    ∀ φ : MulAut ↥(rankOneGroupTwo K m), φ * φ = 1 → φ ≠ 1 →
      InvAutGen ↥(rankOneGroupTwo K m) φ :=
  invAutGen_of_suzukiModel
    ⟨rfl, m, hm, K, inferInstance, inferInstance, rfl, hK, ⟨rankOneEquivSuzuki K m hm hK⟩⟩

theorem rankOneGroupTwo_le_closure_invXi (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1))
    {u : ModGL F4.tag K} (hu : u ∈ rankOneGroupTwo K m) (hu2 : u * u = 1) (hu1 : u ≠ 1) :
    rankOneGroupTwo K m ≤ Subgroup.closure (invXi (rankOneGroupTwo K m) u) :=
  le_closure_invXi_of_forall_invAutGen (forall_invAutGen_rankOneGroupTwo hm hK)
    (isSimpleGroup_rankOneGroupTwo hm hK).1 (isSimpleGroup_rankOneGroupTwo hm hK).2 hu hu2 hu1

theorem map_conj_nH_octX_two :
    (X[2]).map (MulAut.conj ((weylOne K * weylTwo K * weylOne K) * weylTwo K *
      (weylOne K * weylTwo K * weylOne K)⁻¹)).toMonoidHom = X[-8] := by
  simp only [mul_inv_rev, conjSub_mul]
  rw [map_conj_weylOne_inv (k := 2) (by decide), show octSig₂ 2 = 6 by decide,
    map_conj_weylTwo_inv (k := 6) (by decide), show octSig₁ 6 = 4 by decide,
    map_conj_weylOne_inv (k := 4) (by decide), show octSig₂ 4 = 4 by decide,
    map_conj_weylTwo (k := 4) (by decide), show octSig₁ 4 = 6 by decide,
    map_conj_weylOne (k := 6) (by decide), show octSig₂ 6 = 2 by decide,
    map_conj_weylTwo (k := 2) (by decide), show octSig₁ 2 = 8 by decide,
    map_conj_weylOne (k := 8) (by decide), show octSig₂ 8 = -8 by decide]

theorem sylowH_zero_one_mem (hK : Nat.card K = 2 ^ (2 * m + 1)) : sylowH m K 0 1 ∈ Γ := by
  have hB : sylowB m K 0 1 ∈ X[1] := by
    rw [octX_one]
    exact sylowB_mem_U2 hK 0 1
  rw [← weyl_conj_sylowB_zero (m := m) (K := K) 1]
  exact mul_mem (mul_mem (mul_mem (mul_mem weylOne_mem weylTwo_mem) weylOne_mem)
    (rankOneGroupTwo_le_reeGamma hK (octX_one_le_rankOneGroupTwo hB)))
    (inv_mem (mul_mem (mul_mem weylOne_mem weylTwo_mem) weylOne_mem))

theorem invGen_zOne (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    InvGen (F4.reeGamma K m) (sylowH m K 0 1) := by
  have hwΓ : wZ ∈ Γ := mul_mem (mul_mem weylOne_mem weylTwo_mem) weylOne_mem
  have hz : wZ * sylowB m K 0 1 * wZ⁻¹ = sylowH m K 0 1 := weyl_conj_sylowB_zero 1
  have hB : sylowB m K 0 1 ∈ X[1] := by
    rw [octX_one]
    exact sylowB_mem_U2 hK 0 1
  have hBR : sylowB m K 0 1 ∈ rankOneGroupTwo K m := octX_one_le_rankOneGroupTwo hB
  have hB2 : sylowB m K 0 1 * sylowB m K 0 1 = 1 := by
    have e : sylowB m K 0 1 = wZ⁻¹ * sylowH m K 0 1 * wZ := by rw [← hz]; group
    rw [e]
    have hzz : sylowH m K 0 1 * sylowH m K 0 1 = 1 := by rw [← sq]; exact zOne_sq
    calc wZ⁻¹ * sylowH m K 0 1 * wZ * (wZ⁻¹ * sylowH m K 0 1 * wZ) =
        wZ⁻¹ * (sylowH m K 0 1 * sylowH m K 0 1) * wZ := by group
      _ = 1 := by rw [hzz]; group
  have hB1 : sylowB m K 0 1 ≠ 1 := by
    intro h
    rw [h] at hz
    exact zOne_ne_one (by rw [← hz]; group)
  have hRΓ : rankOneGroupTwo K m ≤ Γ := rankOneGroupTwo_le_reeGamma hK
  have hR := rankOneGroupTwo_le_closure_invXi hm hK hBR hB2 hB1
  have h1 : (rankOneGroupTwo K m).map (MulAut.conj wZ).toMonoidHom ≤
      Subgroup.closure (invXi Γ (sylowH m K 0 1)) := by
    have h := (Subgroup.map_mono hR).trans (map_closure_invXi_le hRΓ (sylowB m K 0 1) hwΓ)
    rwa [hz] at h
  have hnH : wZ * weylTwo K * wZ⁻¹ ∈ Subgroup.closure (invXi Γ (sylowH m K 0 1)) :=
    h1 (Subgroup.mem_map.2 ⟨weylTwo K, weylTwo_mem_rankOneGroupTwo, rfl⟩)
  have hne : (invXi Γ (sylowH m K 0 1)).Nonempty := by
    have := (isSimpleGroup_rankOneGroupTwo hm hK).1
    have hR' : (rankOneGroupTwo K m) ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot _).1 inferInstance
    obtain ⟨x, hx⟩ := nonempty_invXi_of_le_closure hR hR'
    have h := conj_mem_invXi_of_le hRΓ hwΓ hx
    rw [hz] at h
    exact ⟨_, h⟩
  have hC := centralizer_le_closure_invXi hne
  have hcent := (large_Ree_two_involution_centralizers m hm K hK).1
  rw [← sylowH_zero_eq_centralZ (m := m) (K := K) 1] at hcent
  rw [hcent] at hC
  have hV := le_sup_left.trans hC
  have hR2 := le_sup_right.trans hC
  have h2 : X[2] ≤ Subgroup.closure (invXi Γ (sylowH m K 0 1)) :=
    (octX_le_complement (by decide) (by decide +kernel)).trans hV
  have h8 : X[8] ≤ Subgroup.closure (invXi Γ (sylowH m K 0 1)) :=
    (octX_le_complement (by decide) (by decide +kernel)).trans hV
  have h8' : X[-8] ≤ Subgroup.closure (invXi Γ (sylowH m K 0 1)) := by
    rw [← map_conj_nH_octX_two]
    exact conjSub_le_of_mem hnH h2
  have hge := reeGamma_le_of_octX hK h8 h8' (octX_one_le_rankOneGroupTwo.trans hR2)
    (octX_neg_one_le_rankOneGroupTwo.trans hR2)
  exact le_antisymm closure_invXi_le hge

end CFSG.Quasithin.F7Two
