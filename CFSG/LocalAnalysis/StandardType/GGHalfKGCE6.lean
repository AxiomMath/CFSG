module

public import CFSG.LocalAnalysis.StandardType.GGHalfKGCDefs
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoT31Cent
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoLevi
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoNum
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotQ2RowOverlap
public import CFSG.GroupTheory.OrderBelowSixtySolvable
public import CFSG.ClassicalInvolution.WeakCT.Main
public import CFSG.LieType.Ree.LargeReeInvolutionTwoCentralizers
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddB
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenTriality
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIIL3Rigid
public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupLinearThreeFour
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.SeitzReduction.CrossCharInputs
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotClassesRoots
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviAutFacts
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotSwapConjGenArith
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotSwapConjGenFactor
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotSwapCoverConj
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotSwapLift
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenClassical
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatSporadic
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourFix
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourLift
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTwistedFusion
public import CFSG.LocalAnalysis.SeitzReduction.RankOneBranches
public import CFSG.LocalAnalysis.SeitzReduction.RankOneHypStarDef
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotAlignImagesSwap
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotUniqueTypeGraph
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B1MoreElevenD
public import CFSG.Quasithin.Background.B1MoreElevenF
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithfulMultiple.InputB19Proof
public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusWeyl
public import CFSG.RankThree.Chevalley.SteinbergCFEvenF4PointwiseInner
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Fi24.Faithful
public import CFSG.Sporadic.Fi24.SepSpec
public import CFSG.Sporadic.HN.CertificateBase
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.OrbitSpec
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.ON.SimpleBase
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.LyChain11
public import Certificates.Certificate1016Base
public import Certificates.Certificate1021
public import Certificates.Certificate3085Base

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.SeitzReduction CFSG.StandardType.GGHalf CFSG.StandardType.GGSixE6Two

private theorem ggHalfKGCE6_cent_eq_of_mem_zpowers {G : Type*} [Group G] [Finite G] {t z : G}
    (hz : z ∈ Subgroup.zpowers t) (hzt : orderOf z = orderOf t) :
    Subgroup.centralizer ({z} : Set G) = Subgroup.centralizer ({t} : Set G) := by
  have hzp : Subgroup.zpowers z = Subgroup.zpowers t := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hz) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, hzt]
  have h1 : Subgroup.centralizer (Subgroup.zpowers z : Set G) =
      Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have h2 : Subgroup.centralizer (Subgroup.zpowers t : Set G) =
      Subgroup.centralizer ({t} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [← h1, ← h2, hzp]

private theorem ggHalfKGCE6_exists_conj_zpowers
    (t y : EC) (ht : orderOf t = 31) (hy : orderOf y = 31) :
    ∃ g : EC, MulAut.conj g y ∈ Subgroup.zpowers t := by
  haveI : Finite EC := finite_EC
  haveI : Fact (Nat.Prime 31) := ⟨by norm_num⟩
  have hPy : IsPGroup 31 ↥(Subgroup.zpowers y) :=
    IsPGroup.of_card (show Nat.card ↥(Subgroup.zpowers y) = 31 ^ 1 by
      rw [Nat.card_zpowers, hy]; norm_num)
  have hidxy : (Subgroup.zpowers y).index * 31 = ordE6 2 := by
    have h := Subgroup.index_mul_card (Subgroup.zpowers y)
    rw [Nat.card_zpowers, hy, card_EC] at h
    exact h
  have hPy2 : ¬ 31 ∣ (Subgroup.zpowers y).index := by
    intro hd
    exact not_thirtyOne_sq_dvd_ordE6 (by
      rw [← hidxy, pow_two]
      exact mul_dvd_mul hd dvd_rfl)
  let Py : Sylow 31 EC := hPy.toSylow hPy2
  have hPycoe : (Py : Subgroup EC) = Subgroup.zpowers y :=
    Subgroup.ext fun _ => IsPGroup.mem_toSylow hPy hPy2
  have hPt : IsPGroup 31 ↥(Subgroup.zpowers t) :=
    IsPGroup.of_card (show Nat.card ↥(Subgroup.zpowers t) = 31 ^ 1 by
      rw [Nat.card_zpowers, ht]; norm_num)
  have hidxt : (Subgroup.zpowers t).index * 31 = ordE6 2 := by
    have h := Subgroup.index_mul_card (Subgroup.zpowers t)
    rw [Nat.card_zpowers, ht, card_EC] at h
    exact h
  have hPt2 : ¬ 31 ∣ (Subgroup.zpowers t).index := by
    intro hd
    exact not_thirtyOne_sq_dvd_ordE6 (by
      rw [← hidxt, pow_two]
      exact mul_dvd_mul hd dvd_rfl)
  let Pt : Sylow 31 EC := hPt.toSylow hPt2
  have hPtcoe : (Pt : Subgroup EC) = Subgroup.zpowers t :=
    Subgroup.ext fun _ => IsPGroup.mem_toSylow hPt hPt2
  haveI : MulAction.IsPretransitive EC (Sylow 31 EC) := Sylow.isPretransitive_of_finite
  obtain ⟨g, hg⟩ := MulAction.IsPretransitive.exists_smul_eq (M := EC) Py Pt
  refine ⟨g, ?_⟩
  have hmem := Subgroup.smul_mem_pointwise_smul y (MulAut.conj g) (Py : Subgroup EC)
    (by rw [hPycoe]; exact Subgroup.mem_zpowers y)
  rw [← Sylow.coe_subgroup_smul, hg] at hmem
  rwa [hPtcoe] at hmem

private theorem ggHalfKGCE6_cent_eq_conj
    (t y : EC) (ht : orderOf t = 31) (hy : orderOf y = 31) :
    ∃ c : EC, Subgroup.centralizer ({y} : Set EC) =
      (Subgroup.centralizer ({t} : Set EC)).map (MulAut.conj c).toMonoidHom := by
  obtain ⟨g, hg⟩ := ggHalfKGCE6_exists_conj_zpowers t y ht hy
  refine ⟨g⁻¹, ?_⟩
  have hy_eq : y = g⁻¹ * (MulAut.conj g y) * (g⁻¹)⁻¹ := by
    simp only [MulAut.conj_apply, inv_inv]
    group
  rw [hy_eq, CFSG.GroupTheory.GL52.centralizer_conj]
  congr 1
  refine ggHalfKGCE6_cent_eq_of_mem_zpowers hg ?_
  exact (orderOf_injective (MulAut.conj g).toMonoidHom (MulEquiv.injective _) y).trans
    (by rw [hy, ht])

private theorem ggHalfKGCE6_isSolvable_cent_of_order31
    (t : EC) (ht : orderOf t = 31)
    (hcent : Subgroup.centralizer ({t} : Set EC) = Subgroup.zpowers t ⊔ sTheta)
    (hcard : Nat.card (Subgroup.centralizer ({t} : Set EC)) = 186) :
    Group.IsSolvable ↥(Subgroup.centralizer ({t} : Set EC)) := by
  rw [hcent]
  set A : Subgroup EC := Subgroup.zpowers t with hA
  set S : Subgroup EC := sTheta with hS
  set G' : Subgroup EC := A ⊔ S with hG'
  have hcent' : Subgroup.centralizer ({t} : Set EC) = G' := by
    rw [hG', hA, hS]; exact hcent
  have hAG' : A ≤ G' := by rw [hG']; exact le_sup_left
  have hSG' : S ≤ G' := by rw [hG']; exact le_sup_right
  have hcardG : Nat.card G' = 186 := by
    rw [← hcent']; exact hcard
  have hcardA : Nat.card A = 31 := by rw [hA, Nat.card_zpowers, ht]
  have hS_le_cent_t : S ≤ Subgroup.centralizer ({t} : Set EC) := by
    rw [hcent']; exact hSG'
  have hS_cent_A : S ≤ Subgroup.centralizer (A : Set EC) := by
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    rw [hA] at ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    have hst : Commute s t :=
      Subgroup.mem_centralizer_singleton_iff.1 (hS_le_cent_t hs)
    exact (hst.zpow_right k).symm
  haveI : (A.subgroupOf G').Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hAG', hG']
    exact sup_le Subgroup.le_normalizer
      (hS_cent_A.trans (Subgroup.centralizer_le_normalizer (A : Set EC)))
  haveI : IsMulCommutative ↥A := by rw [hA]; exact Subgroup.zpowers_isMulCommutative t
  haveI : Group.IsSolvable ↥(A.subgroupOf G') :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hAG').toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hAG').injective
  have hcardA' : Nat.card ↥(A.subgroupOf G') = 31 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAG').toEquiv, hcardA]
  have hidx : (A.subgroupOf G').index = 6 := by
    have h := Subgroup.index_mul_card (A.subgroupOf G')
    rw [hcardA', hcardG] at h
    omega
  haveI : Group.IsSolvable (G' ⧸ A.subgroupOf G') := by
    refine CFSG.GroupTheory.groups_order_below_sixty_solvable ?_
    rw [← Subgroup.index_eq_card, hidx]
    norm_num
  exact Group.isSolvable_of_subgroup_quotient (A.subgroupOf G')

private theorem ggHalfKGCE6_cent_t31_solvable :
    Group.IsSolvable ↥(Subgroup.centralizer ({e6TwoT31} : Set EC)) := by
  have hcent := e6TwoCentT31_holds e6TwoT31 e6TwoT31_mem_lE orderOf_e6TwoT31
  exact ggHalfKGCE6_isSolvable_cent_of_order31 e6TwoT31 orderOf_e6TwoT31 hcent.1 hcent.2.2

private theorem ggHalfKGCE6_cent_solvable
    (y : EC) (hy : orderOf y = 31) :
    Group.IsSolvable ↥(Subgroup.centralizer ({y} : Set EC)) := by
  obtain ⟨c, hc⟩ := ggHalfKGCE6_cent_eq_conj e6TwoT31 y orderOf_e6TwoT31 hy
  rw [hc]
  haveI : Group.IsSolvable ↥(Subgroup.centralizer ({e6TwoT31} : Set EC)) :=
    ggHalfKGCE6_cent_t31_solvable
  let e := Subgroup.equivMapOfInjective (Subgroup.centralizer ({e6TwoT31} : Set EC))
    (MulAut.conj c).toMonoidHom (MulEquiv.injective _)
  exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective

theorem ggKGCCentSolv_E6 :
    GGKGCCentSolv CFSG.StandardType.GGSixE6Two.EC 7 := by
  intro J k hJ hk3 hkne hkJcent
  haveI : Finite EC := finite_EC
  obtain ⟨e⟩ := hJ
  have hcardJ : Nat.card ↥J =
      Nat.card (Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 1)) := by
    simpa using Nat.card_congr e.toEquiv
  have hcardSL : Nat.card (Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 1)) = ordA 5 2 := by
    have hinj : Function.Injective (E6Pilot.slToAdjointE6 F2) :=
      E6Pilot.injective_slToAdjointE6_two (by
        rw [GaloisField.card 2 1 (by norm_num), pow_one])
    have hrange : (E6Pilot.slToAdjointE6 F2).range = lE := E6Pilot.range_slToAdjointE6
    rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hrange, card_lE]
  have h31 : 31 ∣ Nat.card ↥J := by
    rw [hcardJ, hcardSL]
    exact thirtyOne_dvd_ordA
  haveI : Finite ↥J := inferInstance
  haveI : Fact (Nat.Prime 31) := ⟨by norm_num⟩
  obtain ⟨y, hyord⟩ := exists_prime_orderOf_dvd_card' 31 h31
  let ye : EC := y
  have hye : orderOf ye = 31 := by
    change orderOf (y : EC) = 31
    rw [Subgroup.orderOf_coe, hyord]
  have hle : Subgroup.centralizer (J : Set EC) ≤ Subgroup.centralizer ({ye} : Set EC) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.1 hx ye y.2).symm
  haveI : Group.IsSolvable ↥(Subgroup.centralizer ({ye} : Set EC)) :=
    ggHalfKGCE6_cent_solvable ye hye
  exact Group.isSolvable_of_isSolvable_injective
    (f := Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)

end CFSG.StandardType

end
