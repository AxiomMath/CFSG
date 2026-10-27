module

public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoModel
import CFSG.LocalAnalysis.StandardType.GGSixE6TwoCent
import CFSG.LocalAnalysis.StandardType.GGSixE6TwoLevi
import CFSG.LocalAnalysis.StandardType.GGSixE6TwoT31Cent
import CFSG.LocalAnalysis.StandardType.GGSixE6TwoNum
import CFSG.GroupTheory.ClosurePairInvert
import CFSG.LocalAnalysis.SeitzReduction.E6PilotQ2RowOverlap
import CFSG.ClassicalInvolution.WeakCT.Main
import CFSG.LieType.Ree.LargeReeInvolutionTwoCentralizers
import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddB
import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenTriality
import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIIL3Rigid
import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupLinearThreeFour
import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
import CFSG.LocalAnalysis.SectionRank.TitsCover
import CFSG.LocalAnalysis.SeitzReduction.CrossCharInputs
import CFSG.LocalAnalysis.SeitzReduction.E6PilotClassesRoots
import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviAutFacts
import CFSG.LocalAnalysis.SeitzReduction.E6PilotSwapConjGenArith
import CFSG.LocalAnalysis.SeitzReduction.E6PilotSwapConjGenFactor
import CFSG.LocalAnalysis.SeitzReduction.E6PilotSwapCoverConj
import CFSG.LocalAnalysis.SeitzReduction.E8PilotSwapLift
import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenClassical
import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatSporadic
import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourFix
import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourLift
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTwistedFusion
import CFSG.LocalAnalysis.SeitzReduction.RankOneBranches
import CFSG.LocalAnalysis.SeitzReduction.RankOneHypStarDef
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotAlignImagesSwap
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotUniqueTypeGraph
import CFSG.Quasithin.Background.A3Components
import CFSG.Quasithin.Background.A3ComponentsAmbient
import CFSG.Quasithin.Background.B1MoreElevenD
import CFSG.Quasithin.Background.B1MoreElevenF
import CFSG.Quasithin.Background.B1MoreNineG
import CFSG.Quasithin.Background.B4ModelsAction
import CFSG.Quasithin.Background.B4ModelsIso
import CFSG.Quasithin.Background.C2Basic
import CFSG.Quasithin.Background.E1
import CFSG.Quasithin.Background.E1Sec4
import CFSG.Quasithin.Background.E1Sec5
import CFSG.Quasithin.Background.E1Sec8
import CFSG.Quasithin.Background.E1Solv
import CFSG.Quasithin.Background.E1Twelve
import CFSG.Quasithin.Background.E3Cent
import CFSG.Quasithin.EmptyFaithfulMultiple.InputB19Proof
import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusWeyl
import CFSG.RankThree.Chevalley.SteinbergCFEvenF4PointwiseInner
import CFSG.Sporadic.Bridge.LyData
import CFSG.Sporadic.Fi24.Faithful
import CFSG.Sporadic.Fi24.SepSpec
import CFSG.Sporadic.HN.CertificateBase
import CFSG.Sporadic.J4Base
import CFSG.Sporadic.Ly.ActionBase
import CFSG.Sporadic.Ly.CertificateBase
import CFSG.Sporadic.Ly.FaithSpec
import CFSG.Sporadic.Ly.OrbitSpec
import CFSG.Sporadic.Ly.Simple
import CFSG.Sporadic.LyBase
import CFSG.Sporadic.ON.SimpleBase
import CFSG.Sporadic.Presentation.Ly
import CFSG.Sporadic.Schreier.LyChain11
import Certificates.Certificate1016Base
import Certificates.Certificate1021
import Certificates.Certificate3085Base

public section

namespace CFSG.StandardType.GGSixE6Two

open CFSG.SeitzReduction (highRoot)

open scoped Pointwise

section Model

theorem orderOf_xr (β : Fin CFSG.Blueprint.Chevalley.Tag.E6.rank → ℤ) :
    orderOf (xr β) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ ?_
  · rw [pow_two]
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_one, xr, Subtype.coe_mk]
    rw [← CFSG.Blueprint.Chevalley.pinnedX_add,
      show (1 : CFSG.StandardType.GGHalf.F2) + 1 = 0 from by
        rw [← two_mul, CFSG.StandardType.GGHalf.gf2_two, zero_mul],
      CFSG.Blueprint.Chevalley.pinnedX_zero]
  · intro h
    have h' : (CFSG.Blueprint.Chevalley.pinnedX .E6 CFSG.StandardType.GGHalf.F2 β 1 :
        CFSG.Blueprint.Chevalley.ModGL .E6 CFSG.StandardType.GGHalf.F2) = 1 := by
      simpa only [xr, Subgroup.coe_one, Subtype.coe_mk] using congrArg Subtype.val h
    have h2 : CFSG.Blueprint.Chevalley.pinnedX .E6 CFSG.StandardType.GGHalf.F2 β 1 =
        CFSG.Blueprint.Chevalley.pinnedX .E6 CFSG.StandardType.GGHalf.F2 β 0 := by
      rw [CFSG.Blueprint.Chevalley.pinnedX_zero]
      exact h'
    have h'' : (1 : CFSG.StandardType.GGHalf.F2) = 0 :=
      CFSG.Blueprint.Chevalley.pinnedX_injective .E6 CFSG.StandardType.GGHalf.F2 β h2
    exact one_ne_zero h''

theorem orderOf_xr_highRoot : orderOf (xr (highRoot .E6)) = 2 :=
  orderOf_xr (highRoot .E6)

theorem xr_highRoot_mem_sTheta : xr (highRoot .E6) ∈ sTheta := by
  rw [sTheta, Subgroup.mem_subgroupOf]
  show CFSG.Blueprint.Chevalley.pinnedX .E6 CFSG.StandardType.GGHalf.F2 (highRoot .E6) 1 ∈
    CFSG.SeitzReduction.EPilot.highRootSL2 .E6 CFSG.StandardType.GGHalf.F2
  unfold CFSG.SeitzReduction.EPilot.highRootSL2
  exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨1, rfl⟩)

theorem xr_highRoot_mul_zE_mul_inv :
    xr (highRoot .E6) * zE * (xr (highRoot .E6))⁻¹ = zE⁻¹ := by
  have hx2 : xr (highRoot .E6) * xr (highRoot .E6) = 1 := by
    have h := pow_orderOf_eq_one (xr (highRoot .E6))
    rw [orderOf_xr_highRoot] at h
    simpa [pow_two] using h
  have hy2 : xr (-highRoot .E6) * xr (-highRoot .E6) = 1 := by
    have h := pow_orderOf_eq_one (xr (-highRoot .E6))
    rw [orderOf_xr (-highRoot .E6)] at h
    simpa [pow_two] using h
  have hx_inv : (xr (highRoot .E6))⁻¹ = xr (highRoot .E6) :=
    inv_eq_of_mul_eq_one_right hx2
  have hy_inv : (xr (-highRoot .E6))⁻¹ = xr (-highRoot .E6) :=
    inv_eq_of_mul_eq_one_right hy2
  unfold zE
  rw [hx_inv, mul_inv_rev, hx_inv, hy_inv]
  calc xr (highRoot .E6) * (xr (highRoot .E6) * xr (-highRoot .E6)) * xr (highRoot .E6)
      = (xr (highRoot .E6) * xr (highRoot .E6)) *
          (xr (-highRoot .E6) * xr (highRoot .E6)) := by group
    _ = xr (-highRoot .E6) * xr (highRoot .E6) := by rw [hx2, one_mul]

private theorem sTheta_conj_xr_zpow (k : ℤ) :
    xr (highRoot .E6) * zE ^ k * (xr (highRoot .E6))⁻¹ = (zE ^ k)⁻¹ := by
  rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, xr_highRoot_mul_zE_mul_inv, inv_zpow]

private theorem sTheta_mem_of_mem_centralizer_coprime {t x' : EC} (h : E6TwoCentT31)
    (ht : t ∈ lE) (ho : orderOf t = 31) (hx' : x' ∈ Subgroup.centralizer ({t} : Set EC))
    (hco : Nat.Coprime (orderOf x') 31) : x' ∈ sTheta := by
  have hht := h t ht ho
  have hx'AS : x' ∈ Subgroup.zpowers t ⊔ sTheta := by rw [← hht.1]; exact hx'
  have hS_le_C : sTheta ≤ Subgroup.centralizer ({t} : Set EC) := by
    rw [hht.1]; exact le_sup_right
  have hA_le_centS : Subgroup.zpowers t ≤ Subgroup.centralizer (sTheta : Set EC) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hbt : Commute b t := Subgroup.mem_centralizer_singleton_iff.mp (hS_le_C hb)
    have hbk : Commute b (t ^ k) := hbt.zpow_right k
    rw [hk] at hbk
    exact hbk
  have hA_le_normS : Subgroup.zpowers t ≤ Subgroup.normalizer (sTheta : Set EC) :=
    le_trans hA_le_centS (Subgroup.centralizer_le_normalizer (sTheta : Set EC))
  have hxmul : x' ∈ ((Subgroup.zpowers t : Set EC) * (sTheta : Set EC)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.zpowers t) sTheta hA_le_normS]
    exact hx'AS
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hxmul
  have hba : Commute b a := (Subgroup.mem_centralizer_iff.mp (hA_le_centS ha)) b hb
  have habc : Commute a b := hba.symm
  have hpow : (a * b) ^ orderOf x' = 1 := by
    rw [hab]; exact pow_orderOf_eq_one x'
  have h3ab : a ^ orderOf x' = 1 := by
    rw [habc.mul_pow] at hpow
    have hmemS : a ^ orderOf x' ∈ sTheta := by
      rw [eq_inv_of_mul_eq_one_left hpow]
      exact sTheta.inv_mem (Subgroup.pow_mem sTheta hb _)
    have hmem : a ^ orderOf x' ∈ Subgroup.zpowers t ⊓ sTheta :=
      ⟨Subgroup.pow_mem (Subgroup.zpowers t) ha _, hmemS⟩
    exact Subgroup.mem_bot.mp (hht.2.1.le_bot hmem)
  have ha1 : a = 1 := by
    have h1 : orderOf a ∣ orderOf x' := orderOf_dvd_of_pow_eq_one h3ab
    have h2 : orderOf a ∣ 31 := by
      have h := Subgroup.orderOf_dvd_natCard (Subgroup.zpowers t) ha
      rwa [Nat.card_zpowers, ho] at h
    have hg : orderOf a ∣ Nat.gcd (orderOf x') 31 := Nat.dvd_gcd h1 h2
    rw [Nat.Coprime] at hco
    rw [hco] at hg
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hg)
  rw [← hab, ha1, one_mul]
  exact hb

end Model

section STheta

theorem sTheta_eq_zpowers_sup :
    sTheta = Subgroup.zpowers zE ⊔ Subgroup.zpowers (xr (highRoot .E6)) := by
  haveI : Finite EC := finite_EC
  have hle : Subgroup.zpowers zE ⊔ Subgroup.zpowers (xr (highRoot .E6)) ≤ sTheta :=
    sup_le (Subgroup.zpowers_le.mpr zE_mem_sTheta)
      (Subgroup.zpowers_le.mpr xr_highRoot_mem_sTheta)
  have h3 : 3 ∣ Nat.card
      (Subgroup.zpowers zE ⊔ Subgroup.zpowers (xr (highRoot .E6)) : Subgroup EC) := by
    have h := Subgroup.card_dvd_of_le
      (le_sup_left : Subgroup.zpowers zE ≤
        Subgroup.zpowers zE ⊔ Subgroup.zpowers (xr (highRoot .E6)))
    rwa [Nat.card_zpowers, orderOf_zE] at h
  have h2 : 2 ∣ Nat.card
      (Subgroup.zpowers zE ⊔ Subgroup.zpowers (xr (highRoot .E6)) : Subgroup EC) := by
    have h := Subgroup.card_dvd_of_le
      (le_sup_right : Subgroup.zpowers (xr (highRoot .E6)) ≤
        Subgroup.zpowers zE ⊔ Subgroup.zpowers (xr (highRoot .E6)))
    rwa [Nat.card_zpowers, orderOf_xr_highRoot] at h
  have h6 : 6 ∣ Nat.card
      (Subgroup.zpowers zE ⊔ Subgroup.zpowers (xr (highRoot .E6)) : Subgroup EC) := by
    have h := Nat.lcm_dvd h3 h2
    rwa [show Nat.lcm 3 2 = 6 from by norm_num] at h
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [card_sTheta]
  exact Nat.le_of_dvd Nat.card_pos h6

theorem exists_zpow_conj_eq_xr_highRoot {s : EC} (hs : s ∈ sTheta) (h2 : orderOf s = 2) :
    ∃ k : ℤ, zE ^ k * s * (zE ^ k)⁻¹ = xr (highRoot .E6) := by
  have hcl : sTheta = Subgroup.closure ({zE, xr (highRoot .E6)} : Set EC) := by
    rw [sTheta_eq_zpowers_sup, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure,
      ← Subgroup.closure_union]
    rw [show ({zE} ∪ {xr (highRoot .E6)} : Set EC) = {zE, xr (highRoot .E6)} from by
      ext x
      simp [or_comm]]
  rw [hcl] at hs
  have hk2 : xr (highRoot .E6) * xr (highRoot .E6) = 1 := by
    have h := pow_orderOf_eq_one (xr (highRoot .E6))
    rw [orderOf_xr_highRoot] at h
    simpa [pow_two] using h
  obtain ⟨m, hm | hm⟩ :=
    CFSG.GroupTheory.mem_closure_pair_of_conj_eq_inv hk2 xr_highRoot_mul_zE_mul_inv hs
  · exfalso
    have hdiv : orderOf s ∣ 3 := by
      rw [hm]
      have h := Subgroup.orderOf_dvd_natCard (Subgroup.zpowers zE)
        (Subgroup.zpow_mem_zpowers zE m)
      rwa [Nat.card_zpowers, orderOf_zE] at h
    rw [h2] at hdiv
    norm_num at hdiv
  · refine ⟨m, ?_⟩
    rw [hm]
    have hx_inv : (xr (highRoot .E6))⁻¹ = xr (highRoot .E6) :=
      inv_eq_of_mul_eq_one_right hk2
    have hcomm : xr (highRoot .E6) * (zE ^ m)⁻¹ = zE ^ m * xr (highRoot .E6) := by
      have h := sTheta_conj_xr_zpow (-m)
      rw [zpow_neg, hx_inv, inv_inv] at h
      calc xr (highRoot .E6) * (zE ^ m)⁻¹
          = xr (highRoot .E6) * (zE ^ m)⁻¹ *
              (xr (highRoot .E6) * xr (highRoot .E6)) := by rw [hk2, mul_one]
        _ = (xr (highRoot .E6) * (zE ^ m)⁻¹ * xr (highRoot .E6)) *
              xr (highRoot .E6) := by group
        _ = zE ^ m * xr (highRoot .E6) := by rw [h]
    calc zE ^ m * (zE ^ m * xr (highRoot .E6)) * (zE ^ m)⁻¹
        = zE ^ (m + m) * (xr (highRoot .E6) * (zE ^ m)⁻¹) := by
            calc zE ^ m * (zE ^ m * xr (highRoot .E6)) * (zE ^ m)⁻¹
                = (zE ^ m * zE ^ m) * xr (highRoot .E6) * (zE ^ m)⁻¹ := by group
              _ = zE ^ (m + m) * xr (highRoot .E6) * (zE ^ m)⁻¹ := by rw [← zpow_add]
              _ = zE ^ (m + m) * (xr (highRoot .E6) * (zE ^ m)⁻¹) := by group
      _ = zE ^ (m + m) * (zE ^ m * xr (highRoot .E6)) := by rw [hcomm]
      _ = zE ^ (m + m + m) * xr (highRoot .E6) := by
            rw [show m + m + m = (m + m) + m by ring, zpow_add]; group
      _ = xr (highRoot .E6) := by
            have hz3 : zE ^ (3 : ℤ) = 1 := by
              simpa using zE_pow_three
            rw [show m + m + m = 3 * m by ring, zpow_mul, hz3, one_zpow, one_mul]

theorem commute_of_mem_sTheta_of_mem_lE {x y : EC} (hx : x ∈ sTheta) (hy : y ∈ lE) :
    x * y = y * x := by
  have hx' : x ∈ (CFSG.SeitzReduction.EPilot.highRootSL2 .E6
      CFSG.StandardType.GGHalf.F2).subgroupOf
      (CFSG.Blueprint.Chevalley.adjointGroup .E6 CFSG.StandardType.GGHalf.F2) := hx
  have hy' : y ∈ (CFSG.Blueprint.Chevalley.rootSpan .E6 CFSG.StandardType.GGHalf.F2
      (CFSG.SeitzReduction.EPilot.perpRoots .E6)).subgroupOf
      (CFSG.Blueprint.Chevalley.adjointGroup .E6 CFSG.StandardType.GGHalf.F2) := by
    rw [← CFSG.SeitzReduction.E6Pilot.a5Levi_eq_subgroupOf_perpRoots
      CFSG.StandardType.GGHalf.F2]
    exact hy
  exact CFSG.SeitzReduction.E6Pilot.commute_of_mem_subgroupOf_highRootSL2_of_mem_subgroupOf_perpLevi
    (Or.inl rfl) hx' hy'

theorem mem_sTheta_of_commute_lE {x : EC} (hx : ∀ y ∈ lE, x * y = y * x)
    (hco : Nat.Coprime (orderOf x) 31) : x ∈ sTheta := by
  haveI : Finite EC := finite_EC
  haveI : Fact (Nat.Prime 31) := ⟨by norm_num⟩
  have hlE31 : 31 ∣ Nat.card ↥lE := by rw [card_lE]; exact thirtyOne_dvd_ordA
  obtain ⟨y₂, hy₂⟩ := exists_prime_orderOf_dvd_card' 31 hlE31
  let t : EC := y₂
  have htord : orderOf t = 31 := by
    change orderOf (y₂ : EC) = 31
    rw [Subgroup.orderOf_coe, hy₂]
  have htmem : t ∈ lE := y₂.2
  have hx_cent : x ∈ Subgroup.centralizer ({t} : Set EC) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hx t htmem)
  exact sTheta_mem_of_mem_centralizer_coprime e6TwoCentT31_holds htmem htord hx_cent hco

theorem card_lE_eq_card_specialLinearGroup :
    Nat.card ↥lE = Nat.card (Matrix.SpecialLinearGroup (Fin 6) (ZMod 2)) := by
  have hcardF : Nat.card CFSG.StandardType.GGHalf.F2 = 2 := by
    rw [GaloisField.card 2 1 (by norm_num), pow_one]
  have hinj : Function.Injective
      (CFSG.SeitzReduction.E6Pilot.slToAdjointE6 CFSG.StandardType.GGHalf.F2) :=
    CFSG.SeitzReduction.E6Pilot.injective_slToAdjointE6_two hcardF
  have hrange : (CFSG.SeitzReduction.E6Pilot.slToAdjointE6
      CFSG.StandardType.GGHalf.F2).range = lE :=
    CFSG.SeitzReduction.E6Pilot.range_slToAdjointE6
  have h1 : Nat.card (Matrix.SpecialLinearGroup (Fin 6) CFSG.StandardType.GGHalf.F2) =
      Nat.card ↥lE := by
    rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hrange]
  rw [← h1]
  haveI : Fintype CFSG.StandardType.GGHalf.F2 := Fintype.ofFinite _
  haveI : Fintype (ZMod 2) := Fintype.ofFinite _
  have hF2 : Fintype.card CFSG.StandardType.GGHalf.F2 = 2 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 1 (by norm_num), pow_one]
  have hZ2 : Fintype.card (ZMod 2) = 2 := ZMod.card 2
  rw [Matrix.card_SL_field (𝔽 := CFSG.StandardType.GGHalf.F2) 6,
    Matrix.card_SL_field (𝔽 := ZMod 2) 6, hF2, hZ2]

theorem eq_lE_of_le_of_perfect {M : Subgroup EC} (hM : M ≤ Subgroup.zpowers zE ⊔ lE)
    (hperf : commutator ↥M = ⊤) (hcard : Nat.card ↥M = Nat.card ↥lE) : M = lE := by
  haveI : Finite EC := finite_EC
  have hMZ : M ≤ Subgroup.centralizer ({zE} : Set EC) := by
    rw [centralizer_zE.1]
    exact hM
  set Z : Subgroup EC := Subgroup.centralizer ({zE} : Set EC) with hZdef
  have hZ : Z = Subgroup.zpowers zE ⊔ lE := by rw [hZdef]; exact centralizer_zE.1
  have hlE_le_Z : lE ≤ Z := by rw [hZ]; exact le_sup_right
  have hzp_le_Z : Subgroup.zpowers zE ≤ Z := by rw [hZ]; exact le_sup_left
  have hZ_norm : Z ≤ Subgroup.normalizer (lE : Set EC) := by
    rw [hZ]
    exact sup_le
      (centralizer_zE.2.2.trans (Subgroup.centralizer_le_normalizer (lE : Set EC)))
      (Subgroup.le_normalizer (H := lE))
  have hNnormal : (lE.subgroupOf Z).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hlE_le_Z).2 hZ_norm
  have hsup : (lE.subgroupOf Z) ⊔ (Subgroup.zpowers zE).subgroupOf Z = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hlE_le_Z hzp_le_Z, Subgroup.subgroupOf_eq_top]
    simpa [sup_comm] using (le_of_eq hZ)
  haveI : (lE.subgroupOf Z).Normal := hNnormal
  haveI : IsMulCommutative (Subgroup.zpowers zE) := Subgroup.zpowers_isMulCommutative zE
  have hHcomm : IsMulCommutative ((Subgroup.zpowers zE).subgroupOf Z) :=
    Subgroup.subgroupOf_isMulCommutative Z (Subgroup.zpowers zE)
  have hcommZ : _root_.commutator ↥Z ≤ lE.subgroupOf Z :=
    Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup hHcomm
  have hcommZ' : ⁅Z, Z⁆ ≤ lE := by
    have hmap : (_root_.commutator ↥Z).map Z.subtype ≤ (lE.subgroupOf Z).map Z.subtype :=
      Subgroup.map_mono (f := Z.subtype) hcommZ
    rw [Subgroup.map_subtype_commutator Z, Subgroup.map_subgroupOf_eq_of_le hlE_le_Z] at hmap
    exact hmap
  have hMeq : M = ⁅M, M⁆ := by
    refine le_antisymm ?_ (Subgroup.commutator_le_self M)
    rw [← Subgroup.map_subtype_commutator M, hperf, Subgroup.map_top]
    exact le_of_eq (Subgroup.range_subtype M).symm
  exact Subgroup.eq_of_le_of_card_ge
    (hMeq.le.trans ((Subgroup.commutator_mono hMZ hMZ).trans hcommZ')) (by rw [hcard])

end STheta

end CFSG.StandardType.GGSixE6Two

end
