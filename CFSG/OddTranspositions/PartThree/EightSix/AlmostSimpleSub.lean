module

public import CFSG.Timmesfeld.Bridge.Asc72Defs
public import CFSG.Timmesfeld.Closure.MinCex
public import CFSG.OddTranspositions.O4CloseReduction
public import Certificates.Certificate43
public import Certificates.Certificate82
public import Certificates.Certificate83
public import Certificates.Certificate84
public import Certificates.Certificate85
public import Certificates.Certificate86
public import Certificates.Certificate87
public import Certificates.Certificate88
public import Certificates.Certificate89
public import Certificates.Certificate90
public import Certificates.Certificate91
public import Certificates.Certificate92
public import Certificates.Certificate93
public import Certificates.Certificate94
public import Certificates.Certificate95
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117

import CFSG.OddTranspositions.TheoremTwo.StepSeven
import CFSG.Timmesfeld.Bridge.Asc72ZMain
import CFSG.OddTranspositions.O4Minus5Pair
import CFSG.OddTranspositions.WreathBase
import CFSG.OddTranspositions.WreathBaseMinimal
import CFSG.OddTranspositions.MinimalNormalTransport
import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveFL2B
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.OddTranspositions.SixEight
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore
import CFSG.CGT.Timmesfeld75.Statements
import CFSG.CGT.Timmesfeld75.Targets
import CFSG.Fischer.NoF25.Local
import CFSG.GroupTheory.ABGDGroups.LinearCentralizers
import CFSG.GroupTheory.Fitting.LayerTopBot
import CFSG.GroupTheory.PerfectLeOfPGroupQuotient
import CFSG.LocalAnalysis.ComponentClassification.Asc76BenderFacts
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3GoldschmidtFacts
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvUnitary
import CFSG.LocalAnalysis.ComponentClassification.FooteLitAut5L2Base
import CFSG.LocalAnalysis.ComponentClassification.FooteLitAut5Transport
import CFSG.LocalAnalysis.ComponentClassification.FooteLitCor34
import CFSG.LocalAnalysis.ComponentClassification.HarrisLitPSL
import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderAutE4Unitary
import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderONan
import CFSG.LocalAnalysis.ComponentClassification.SolMaxClaimA11Q
import CFSG.LocalAnalysis.ComponentClassification.SolMaxClaimA9K
import CFSG.LocalAnalysis.ComponentClassification.SolMaxDiagD
import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36B
import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36M
import CFSG.LocalAnalysis.ComponentClassification.SolMaxSigDichMain
import CFSG.LocalAnalysis.ComponentClassification.SolMaxSmallD
import CFSG.LocalAnalysis.ComponentClassification.SolMaxSmallG
import CFSG.OddTranspositions.AlmostSimple
import CFSG.OddTranspositions.Disconnected
import CFSG.OddTranspositions.O4PairTenWidth
import CFSG.OddTranspositions.WreathQuotient
import CFSG.Sporadic.FischerOddCore.Fi24AlmostSimple
import CFSG.Sporadic.FischerOddCore.Fi24R2CompBase
import CFSG.Sporadic.FischerOddCore.FischerOuterBasic
import CFSG.Timmesfeld.Transvection.Statement

public section

namespace CFSG.OddTranspositions.PartThree.EightSix

open CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
open CFSG.Timmesfeld.Bridge.Asc72
open CFSG.OddTranspositions

theorem not_isBenderGroup_subPair {X : Type} [Group X] [Finite X]
    {M : Subgroup X} [M.Normal] (hMs : IsSimpleGroup M) {u : X} (huM : u ∉ M) :
    ¬ CFSG.BenderSuzuki.IsBenderGroup ↥(M ⊔ Subgroup.zpowers u) := by
  classical
  intro hB
  let K : Subgroup X := M ⊔ Subgroup.zpowers u
  have hM0 : Asc72.IsMinimalNormal (M.subgroupOf K) :=
    isMinimalNormal_subgroupOf le_sup_left hMs
  have hsimpleK : IsSimpleGroup K := IsBenderGroup.isSimpleGroup hB
  have hMtop : M.subgroupOf K ≠ ⊤ := by
    intro htop
    have : u ∈ M := Subgroup.mem_subgroupOf.mp (by
      rw [htop]
      exact Subgroup.mem_top (⟨u, Subgroup.mem_sup_right (Subgroup.mem_zpowers u)⟩ : K))
    exact huM this
  have hMnorm : (M.subgroupOf K).Normal := hM0.1
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal K _ hsimpleK (M.subgroupOf K) hMnorm
    with h | h
  · exact hM0.2.1 h
  · exact hMtop h

theorem not_exists_mulEquiv_l2Wreath_subPair
    {X : Type} [Group X] [Finite X] {M : Subgroup X} [M.Normal] (hMs : IsSimpleGroup M) {u : X}
    {Θ : Set ↥(M ⊔ Subgroup.zpowers u)}
    (hS : Setup ↥(M ⊔ Subgroup.zpowers u) Θ)
    (hrad : ∀ N : Subgroup ↥(M ⊔ Subgroup.zpowers u), N.Normal →
      Group.IsSolvable N → N = ⊥) :
    ¬ ∃ f n : ℕ, 2 ≤ f ∧ 2 ≤ n ∧
      Nonempty (↥(M ⊔ Subgroup.zpowers u) ≃* L2Wreath f n) := by
  classical
  rintro ⟨f, n, hf, hn2, ⟨e⟩⟩
  let K : Subgroup X := M ⊔ Subgroup.zpowers u
  have hM0 : Asc72.IsMinimalNormal (M.subgroupOf K) :=
    isMinimalNormal_subgroupOf le_sup_left hMs
  have hbase : Asc72.IsMinimalNormal (l2WreathBase f n) := by
    simpa [l2WreathBase] using base_isMinimalNormal f n hf hn2
  have hbmin : Asc72.IsMinimalNormal
      ((l2WreathBase f n).comap (e : K →* L2Wreath f n)) :=
    IsMinimalNormal.comap_mulEquiv e hbase
  have hbns : ¬ IsSimpleGroup ((l2WreathBase f n).comap (e : K →* L2Wreath f n)) :=
    not_isSimpleGroup_comap_mulEquiv e (l2WreathBase_not_isSimpleGroup hf hn2)
  have heq : (l2WreathBase f n).comap (e : K →* L2Wreath f n) = M.subgroupOf K :=
    eq_of_minimal hS hrad hM0 hbmin
  have hsimple : IsSimpleGroup (M.subgroupOf K) :=
    (MulEquiv.isSimpleGroup_congr (Subgroup.subgroupOfEquivOfLe le_sup_left)).mpr hMs
  rw [← heq] at hsimple
  exact hbns hsimple

theorem not_almostSimpleCase_subPair
    {X : Type} [Group X] [Finite X] {M : Subgroup X} [M.Normal] (hMs : IsSimpleGroup M) {u : X}
    (hcls : IsOddTranspClass (conjSet M u)) :
    ¬ AlmostSimpleCase ↥(M ⊔ Subgroup.zpowers u) (conjSet M u) := by
  classical
  intro hAS
  let K : Subgroup X := M ⊔ Subgroup.zpowers u
  have hMK : M ≤ K := le_sup_left
  have hM0 : Asc72.IsMinimalNormal (M.subgroupOf K) := isMinimalNormal_subgroupOf hMK hMs
  obtain ⟨-, hoddT, -⟩ := hcls
  have humem : (⟨u, Subgroup.mem_sup_right (Subgroup.mem_zpowers u)⟩ : K) ∈ conjSet M u :=
    ⟨1, one_mem M, by simp⟩
  have hu2K : (⟨u, Subgroup.mem_sup_right (Subgroup.mem_zpowers u)⟩ : K) *
      (⟨u, Subgroup.mem_sup_right (Subgroup.mem_zpowers u)⟩ : K) = 1 :=
    hoddT.mul_self_eq_one humem
  have hu2 : u * u = 1 := by
    simpa using congrArg (fun k : K => (k : X)) hu2K
  obtain ⟨M₀, -, hM₀min, huniq, -, -, hidx, -, -⟩ := hAS
  have hidxle : (M.subgroupOf K).index ≤ 2 := relIndex_sup_zpowers_le_two hu2
  rw [huniq _ hM0] at hidxle
  omega

theorem not_disconnected_conjSet_of_theoremOne (h1 : TheoremOne) {X : Type} [Group X] [Finite X]
    {M : Subgroup X} [M.Normal] (hMs : IsSimpleGroup M)
    (hC : Subgroup.centralizer (M : Set X) = ⊥) {u : X} (huM : u ∉ M)
    (hcls : IsOddTranspClass (conjSet M u)) : ¬ Disconnected (conjSet M u) := by
  classical
  let K : Subgroup X := M ⊔ Subgroup.zpowers u
  let Θ : Set K := conjSet M u
  have hMK : M ≤ K := le_sup_left
  obtain ⟨hclass, hoddT, hgen⟩ := hcls
  have hS : Setup K Θ := ⟨hclass, hoddT, hgen⟩
  have hrad : ∀ N : Subgroup K, N.Normal → Group.IsSolvable N → N = ⊥ :=
    solvable_normal_eq_bot_of_le hMK hMs hC
      ((Subgroup.nontrivial_iff_ne_bot M).mp hMs.toNontrivial)
  intro hdisc
  obtain ⟨H, hHtop, ⟨v, hv, hvH⟩, hclosed⟩ := exists_subgroup_of_disconnected hS hdisc
  rcases h1 K Θ hclass hoddT.1 hoddT.2 hgen hrad
      ⟨H, hHtop, ⟨v, hv, hvH⟩, hclosed⟩ with hB | ⟨f, n, hf, hn, he⟩ | hAS
  · exact not_isBenderGroup_subPair hMs huM hB
  · exact not_exists_mulEquiv_l2Wreath_subPair hMs hS hrad ⟨f, n, hf, by omega, he⟩
  · exact not_almostSimpleCase_subPair hMs ⟨hclass, hoddT, hgen⟩ hAS

theorem not_disconnected_conjSet
    {X : Type} [Group X] [Finite X]
    {M : Subgroup X} [M.Normal] (hMs : IsSimpleGroup M)
    (hC : Subgroup.centralizer (M : Set X) = ⊥) {u : X} (huM : u ∉ M)
    (hcls : IsOddTranspClass (conjSet M u)) : ¬ Disconnected (conjSet M u) :=
  not_disconnected_conjSet_of_theoremOne theoremOne hMs hC huM hcls

theorem not_o4PairData_conjSet {X : Type} [Group X] [Finite X]
    {M : Subgroup X} [M.Normal]
    (hMs : IsSimpleGroup M) (hC : Subgroup.centralizer (M : Set X) = ⊥) {u g : X}
    (hg : g ∉ M) (hodd : Odd (orderOf g)) :
    ¬ CFSG.OddTranspositions.QZ.O4PairData ↥(M ⊔ Subgroup.zpowers u) (conjSet M u) := by
  classical
  intro hO
  let K : Subgroup X := M ⊔ Subgroup.zpowers u
  obtain ⟨e, -⟩ := hO
  let L' : Subgroup K := QZ.L225Subgroup.comap (e : K →* QZ.PSigmaL225)
  have hLmin : Asc72.IsMinimalNormal L' :=
    IsMinimalNormal.comap_mulEquiv e QZ.L225Subgroup_isMinimalNormal
  have hM0 : Asc72.IsMinimalNormal (M.subgroupOf K) :=
    isMinimalNormal_subgroupOf le_sup_left hMs
  have hLMeq : L' = M.subgroupOf K :=
    eq_subgroupOf_of_isMinimalNormal le_sup_left hMs hC hLmin
  have hmapM : (M.subgroupOf K).map (e : K →* QZ.PSigmaL225) = QZ.L225Subgroup := by
    rw [← hLMeq]
    exact Subgroup.map_comap_eq_self_of_surjective e.surjective QZ.L225Subgroup
  let eM : M ≃* M.subgroupOf K :=
    (Subgroup.subgroupOfEquivOfLe (le_sup_left : M ≤ K)).symm
  let eK : M.subgroupOf K ≃* QZ.L225Subgroup :=
    (Subgroup.equivMapOfInjective (M.subgroupOf K) (e : K →* QZ.PSigmaL225)
      e.injective).trans (MulEquiv.subgroupCongr hmapM)
  let e' : M ≃* QZ.PSL225 := eM.trans (eK.trans QZ.L225SubgroupEquiv.symm)
  let φ : MulAut M := MulAut.conjNormal (H := M) g
  have hφodd : Odd (orderOf φ) :=
    hodd.of_dvd_nat (orderOf_map_dvd (MulAut.conjNormal (H := M)) g)
  obtain ⟨m, hm⟩ :=
    CFSG.ComponentClassification.SolMax.FiveFL2.exists_eq_conj_of_odd_psl2_sq
      (F := QZ.K25) Nat.prime_five (by rw [QZ.card_K25]; norm_num) e' φ hφodd
  have hval : ∀ x : M, g * (x : X) * g⁻¹ = (m : X) * (x : X) * (m : X)⁻¹ := by
    intro x
    have h := congrArg (fun ψ : MulAut M => ((ψ x : M) : X)) hm
    simpa [φ, MulAut.conjNormal_apply, MulAut.conj_apply] using h
  have hcent : (m : X)⁻¹ * g ∈ Subgroup.centralizer (M : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hx' := hval ⟨x, hx⟩
    calc x * ((m : X)⁻¹ * g) = (m : X)⁻¹ * ((m : X) * x * (m : X)⁻¹) * g := by group
      _ = (m : X)⁻¹ * (g * x * g⁻¹) * g := by rw [← hx']
      _ = ((m : X)⁻¹ * g) * x := by group
  have h1 : (m : X)⁻¹ * g = 1 := Subgroup.mem_bot.mp (hC ▸ hcent)
  have hgm : g = (m : X) := by
    calc g = (m : X) * ((m : X)⁻¹ * g) := by group
      _ = (m : X) * 1 := by rw [h1]
      _ = (m : X) := mul_one _
  exact hg (by rw [hgm]; exact m.2)

end CFSG.OddTranspositions.PartThree.EightSix

end
