module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import Mathlib.GroupTheory.SpecificGroups.Alternating
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpAltEightTwo
import CFSG.LieType.Universal.Symplectic
import CFSG.Open.StatedAPI
import CFSG.RankThree.GF2n.Tim79a34CentreSmall
import CFSG.CGT.T75E.Lemma26
import CFSG.CGT.Timmesfeld75.Sec3TenCaseA
import CFSG.CGT.Timmesfeld75.Sec4CaseIBasic
import CFSG.CGT.Timmesfeld75.Sec4CaseIIIFour
import CFSG.CGT.Timmesfeld75.Sec4CaseIJFamily
import CFSG.CGT.Timmesfeld75.Sec4CaseIJIdent
import CFSG.CGT.Timmesfeld75.Sec4CaseIPGroup
import CFSG.CGT.Timmesfeld75.Sec4CaseIPartition4
import CFSG.CGT.Timmesfeld75.Sec4Three
import CFSG.CGT.Timmesfeld75.Sec5FiveEng
import CFSG.CGT.Timmesfeld75.Step511Card
import CFSG.CGT.Timmesfeld75.Step57Reduction
import CFSG.Certificates.Kernel.LocalCompTits.Span
import CFSG.ClassicalGroups.Alternating.PointRadicalFixedCard
import CFSG.ClassicalGroups.Linear.TwoCentres
import CFSG.Combinatorics.AperiodicCentralInvolution
import CFSG.Combinatorics.AperiodicFiveOfSix
import CFSG.Combinatorics.AperiodicOppositeComponents
import CFSG.Combinatorics.AperiodicSixteenGraphDistances
import CFSG.Combinatorics.OuterLayerPredecessors
import CFSG.GH74.Uniqueness.Bender.OddCentralizer
import CFSG.GH74.Uniqueness.Bender.Unitary
import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
import CFSG.LocalAnalysis.ComponentClassification.Asc76BenderFacts
import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupFacts
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3GoldschmidtFacts
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvUnitary
import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderAutE4Unitary
import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderONan
import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
import CFSG.Quasithin.Background.A3Structure318Red
import CFSG.Quasithin.Background.A3Structure36A
import CFSG.Quasithin.Background.A3Structure36BAction
import CFSG.Quasithin.Background.A3Structure36BBase
import CFSG.Quasithin.Background.A3Structure36BCase3Base
import CFSG.Quasithin.Background.A3Structure36BCasesBase
import CFSG.Quasithin.Background.A3Structure36BCommonBase
import CFSG.Quasithin.Background.A3Structure36BFrattini
import CFSG.Quasithin.Background.A3Structure36BHeisBase
import CFSG.Quasithin.Background.A3Structure36BHomocyclic
import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
import CFSG.Quasithin.Background.A3Structure36BStarBase
import CFSG.Quasithin.Background.A3Structure36Base
import CFSG.Quasithin.Background.A3Structure37Base
import CFSG.Quasithin.Background.A3Structure37Comm
import CFSG.Quasithin.Background.A3Structure37Frattini
import CFSG.Quasithin.Background.A3Structure37KeyBase
import CFSG.Quasithin.Background.A3Structure37Schur
import CFSG.Quasithin.Background.A3Structure38Part3
import CFSG.Quasithin.Background.B1MoreElevenE
import CFSG.Quasithin.Background.B1MoreNineG
import CFSG.Quasithin.Background.B4ModelsAction
import CFSG.Quasithin.Background.B4ModelsIso
import CFSG.Quasithin.Background.C2Basic
import CFSG.Quasithin.Background.C2Inputs
import CFSG.Quasithin.Background.E3Cent
import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
import CFSG.Quasithin.Vol2.Ch1Local
import CFSG.RankThree.GF2n.Tim79aSec2
import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Defs
import CFSG.Sporadic.Th.Max3.Involutions
import Certificates.Certificate10089Base
import Certificates.Certificate10091Base
import Certificates.Kernel.J4Count.FixCE
import Certificates.Kernel.J4Count.FixCPairBase1
import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.StandardType.RCKC1

open CFSG.StandardType

theorem rckIIp_false_of_alt_eight_PSp
    {X : Type} [Group X] {r f : ℕ} (hf : 1 ≤ f) (π : (ggU .PSp r f).K →* X)
    (hker : π.ker ≤ Subgroup.center (ggU .PSp r f).K)
    (hodd : Odd (Nat.card (Subgroup.center ↥π.range)))
    (hA8 : Nonempty ((↥π.range ⧸ Subgroup.center ↥π.range) ≃* alternatingGroup (Fin 8))) :
    False := by
  let F := GaloisField 2 f
  have hcenter : Subgroup.center ↥(CFSG.Open.StatedSp r F) = ⊥ := by
    rw [CFSG.LieType.Universal.Symplectic.center_eq,
      CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot]
  have hker' : π.ker ≤ Subgroup.center ↥(CFSG.Open.StatedSp r F) := hker
  have hkerbot : π.ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : x ∈ Subgroup.center ↥(CFSG.Open.StatedSp r F) := hker' hx
    rwa [hcenter] at hx'
  have hinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).mp hkerbot
  have hbij : Function.Bijective π.rangeRestrict := by
    refine ⟨fun x y hxy => hinj (congrArg Subtype.val hxy), ?_⟩
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hy
    exact ⟨x, rfl⟩
  let e : ↥(CFSG.Open.StatedSp r F) ≃* ↥π.range :=
    MulEquiv.ofBijective π.rangeRestrict hbij
  have hZJbot : Subgroup.center ↥π.range = ⊥ := by
    have hmap := Subgroup.map_center_eq e
    rw [hcenter, Subgroup.map_bot] at hmap
    exact hmap.symm
  have hcardZJ : Nat.card (Subgroup.center ↥π.range) = 1 := by
    rw [hZJbot, Subgroup.card_bot]
  have hcardJ : Nat.card ↥π.range = 20160 * Nat.card (Subgroup.center ↥π.range) :=
    rckIIp_card_range_of_alt_eight π hA8
  have hJ20160 : Nat.card ↥π.range = 20160 := by rw [hcardJ, hcardZJ, mul_one]
  have hGJ : Nat.card ↥(CFSG.Open.StatedSp r F) = Nat.card ↥π.range :=
    Nat.card_congr e.toEquiv
  have hcardG : Nat.card ↥(CFSG.Open.StatedSp r F) = 20160 := by rw [hGJ, hJ20160]
  have hv : padicValNat 2 (Nat.card ↥(CFSG.Open.StatedSp r F)) = f * r ^ 2 :=
    CFSG.RankThree.GF2n.Tim79a.padicValNat_card_statedSp f hf r
  have hv6 : f * r ^ 2 = 6 := by
    have h6 : padicValNat 2 20160 = 6 := by
      have h20160 : 20160 = 2 ^ 6 * 315 := by norm_num
      rw [h20160, padicValNat.mul (by positivity) (by norm_num), padicValNat.prime_pow,
        padicValNat.eq_zero_of_not_dvd (by norm_num), add_zero]
    rw [hcardG, h6] at hv
    exact hv.symm
  have hr0 : r ≠ 0 := by
    rintro rfl
    norm_num at hv6
  have hr2 : r ^ 2 ≤ 6 := by
    calc r ^ 2 = 1 * r ^ 2 := (one_mul _).symm
      _ ≤ f * r ^ 2 := Nat.mul_le_mul_right _ hf
      _ = 6 := hv6
  have hrle : r ≤ 2 := by
    by_contra h
    have h3 : 3 ≤ r := by omega
    have h9 : 9 ≤ r ^ 2 := by
      calc 9 = 3 * 3 := by norm_num
        _ ≤ r * r := Nat.mul_le_mul h3 h3
        _ = r ^ 2 := (pow_two r).symm
    omega
  have hr1 : r = 1 := by
    have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
    interval_cases r
    · rfl
    · exfalso
      norm_num at hv6
      omega
  subst hr1
  exact rckIIp_false_of_alt_eight_of_GL_two (F := F) (ι := Fin 1 ⊕ Fin 1)
    (by simp : Fintype.card (Fin 1 ⊕ Fin 1) = 2)
    (Subgroup.subtype (CFSG.Open.StatedSp 1 F))
    (Subgroup.subtype_injective (CFSG.Open.StatedSp 1 F))
    π hA8

end CFSG.StandardType.RCKC1
