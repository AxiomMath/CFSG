module

public import CFSG.LocalAnalysis.StandardType.GGSporKF1F4At
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON11_13.D13Core
import CFSG.LocalAnalysis.StandardType.GGSporKFGen
import CFSG.LocalAnalysis.StandardType.GGSporKHeis13Conj
import CFSG.LocalAnalysis.StandardType.GGSporKHeis13Facts
import CFSG.LocalAnalysis.StandardType.GGSporKHeis13Irr
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenFinal
import CFSG.HardMathSupport.Dickson.BMRows.M13B
import CFSG.Assembly.LargeEvenGLABridge
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.QuasiAssembly
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BMShape
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterElevenEbarData
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenEbarData
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicHolds
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
public import CFSG.Monster.GMS.Fi23Gen
public import CFSG.Monster.GMS.Fi23GenIso
public import CFSG.Monster.GMS.Fi23GenSix
public import CFSG.Monster.GMS.LeechCoh
public import CFSG.Monster.GMS.LeechCohGroup
public import CFSG.Monster.GMS.S365Center
public import CFSG.Monster.GMS.S37
public import CFSG.Monster.GMS.S4Assembly
public import CFSG.Monster.GMS.S4CohB
public import CFSG.Monster.GMS.S5Inputs
public import CFSG.Perm.ChainByOrder
public import CFSG.Sporadic.Co1.Module.Co2Stab
public import CFSG.Sporadic.Co1Block.Perm
public import CFSG.Sporadic.Fi23.StarKernel
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.Sporadic.Schreier.J1QT
public import CFSG.Sporadic.Schreier.LyFixedSet
public import CFSG.Sporadic.Schreier.RuLocal
public import CFSG.Sporadic.SchreierLemmas.FrattiniProfile
public import CFSG.Sporadic.SmallOddCore.CentSpec
public import CFSG.Sporadic.ThSchreier.ThSchreierCase
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
public import Certificates.Certificate16005
public import Certificates.Certificate2323
public import Certificates.Certificate3044
public import Certificates.Certificate3122
public import Certificates.Certificate3123
public import Certificates.Certificate3130
public import Certificates.Certificate3133
public import Certificates.Certificate3134
public import Certificates.Certificate3136
public import Certificates.Certificate3137
public import Certificates.Certificate3176
public import Certificates.Certificate3179
public import Certificates.Certificate7000
public import Certificates.Certificate7001
public import Certificates.Certificate7002
public import Certificates.Certificate7003
public import Certificates.Certificate7004
public import Certificates.Certificate7005
public import Certificates.Certificate7006
public import Certificates.Certificate7007
public import Certificates.Certificate7008
public import Certificates.Certificate7009
public import Certificates.Certificate7010
public import Certificates.Certificate7011
public import Certificates.Certificate8046
public import Certificates.Certificate8049
public import Certificates.Certificate8052
public import Certificates.Certificate9124
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99
import CFSG.Assembly.OpenBridges
import CFSG.LocalAnalysis.GLTheoremA.CatA.YS10I1416Chev2
import CFSG.LocalAnalysis.GLTheoremA.CatA.YS10I1416Pass

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly
open CFSG.Monster.Generated CFSG.AGLEmbedding.Norton.GenD13 CFSG.AGLEmbedding.Norton.MON5_7
  CFSG.AGLEmbedding.Norton.MON11_13
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteen
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenLocal
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenB
open CFSG.HardMathSupport.Dickson.BMRows

private theorem gkm_F1F4_of_heis {G : Type} [Group G] [Finite G] {x y c u k : G}
    (hcard : (Nat.card G).factorization 13 = 3)
    (hx : x ^ 13 = 1) (hy : y ^ 13 = 1) (hc : c ^ 13 = 1) (hc1 : c ≠ 1)
    (hcx : c * x = x * c) (hcy : c * y = y * c) (hyx : y * x = x * (y * c ^ 4))
    (hkx : k * x = c ^ 11 * (y ^ 10 * (x ^ 6 * k))) (hky : k * y = c ^ 3 * (y ^ 7 * (x ^ 1 * k)))
    (hux : u * x = c ^ 8 * (y ^ 7 * (x ^ 7 * u))) (huy : u * y = c ^ 6 * (y ^ 7 * (x ^ 5 * u)))
    (hg1 : LargeEvenPPrimeCore 13 ↥(Subgroup.centralizer ({c} : Set G)) = ⊥)
    (hno : ∀ C : Subgroup G, ¬ LargeEvenPComponent 13 (Subgroup.centralizer ({c} : Set G)) C) :
    BMPCentralF1At 13 c ∧ BMPCentralF4At 13 c := by
  haveI hp : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have hco : orderOf c = 13 := orderOf_eq_prime hc hc1
  obtain ⟨hSp, hScard, hSc, hSexp, hScomm, hScent⟩ :=
    heis13_sylow_facts hcard hx hy hc hc1 hcx hcy hyx
  have hS : Nat.card (Subgroup.closure ({x, y} : Set G)) = 13 ^ 3 := by rw [hScard, hcard]
  have hu : u * c * u⁻¹ = c := by
    rw [heis13_conj_z hc hcx hcy hyx hux huy, zpow_eq_zpow_emod' _ hc]
    norm_num
  have hk : k * c * k⁻¹ = c ^ 6 := by
    rw [heis13_conj_z hc hcx hcy hyx hkx hky, zpow_eq_zpow_emod' _ hc]
    norm_num
  have hunorm : u ∈ Subgroup.normalizer (↑(Subgroup.closure ({x, y} : Set G)) : Set G) :=
    heis13_mem_normalizer hc hcx hcy hyx hux huy
  have hknorm : k ∈ Subgroup.normalizer (↑(Subgroup.closure ({x, y} : Set G)) : Set G) :=
    heis13_mem_normalizer hc hcx hcy hyx hkx hky
  have hucent : u ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 hu)
  have hw : k⁻¹ * u * k * c * (k⁻¹ * u * k)⁻¹ = c := by
    have h1 : k⁻¹ * u * k * c * (k⁻¹ * u * k)⁻¹ = k⁻¹ * (u * (k * c * k⁻¹) * u⁻¹) * k := by group
    rw [h1, hk, ← conj_pow, hu, ← hk]
    group
  have hwcent : k⁻¹ * u * k ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 hw)
  have hwnorm : k⁻¹ * u * k ∈ Subgroup.normalizer
      (↑(Subgroup.closure ({x, y} : Set G)) : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hknorm) hunorm) hknorm
  have hirr : ∀ R : Subgroup G, Subgroup.zpowers c ≤ R → R ≤ Subgroup.closure ({x, y} : Set G) →
      (∀ h ∈ Subgroup.centralizer ({c} : Set G) ⊓
        Subgroup.normalizer (↑(Subgroup.closure ({x, y} : Set G)) : Set G),
          ∀ r ∈ R, h * r * h⁻¹ ∈ R) →
      R = Subgroup.zpowers c ∨ R = Subgroup.closure ({x, y} : Set G) := by
    intro R hzR hRS hinv
    exact heis13_invariant_dichotomy hx hy hc hc1 hcx hcy hyx hS hux huy hkx hky R hzR hRS
      (fun a ha => hinv _ ⟨hucent, hunorm⟩ a ha) (fun a ha => hinv _ ⟨hwcent, hwnorm⟩ a ha)
  exact bmPCentralF1At_F4At_of_pLocal hp.out hco hSp hScard hSc le_rfl
    Subgroup.le_normalizer hSexp hScomm hScent hScent hirr hg1 hno


theorem gmat_bmPCentralF1At_F4At_c13
    :
    BMPCentralF1At 13 (gw genD13W1) ∧ BMPCentralF4At 13 (gw genD13W1) := by
  haveI : Finite Gmat := generated_rational_group_finite_simple.2.2
  obtain ⟨hx, hy, hc, hcx, hcy, hyx, hc1, -, hkx, hky, hux, huy, -⟩ := d13_gw_facts
  have hg1 : LargeEvenPPrimeCore 13 ↥(Subgroup.centralizer ({gw genD13W1} : Set Gmat)) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp
      (gLAPPrimeCoreOf_c13_eq_bot (odd_card_core_thirteen _ orderOf_c13))
  have hno : ∀ C : Subgroup Gmat,
      ¬ LargeEvenPComponent 13 (Subgroup.centralizer ({gw genD13W1} : Set Gmat)) C :=
    fun C hC => noComp_c13 C
      ((CFSG.Assembly.LargeEven.largeEvenPComponent_iff_glaPComponent 13 _ C).mp hC)
  exact gkm_F1F4_of_heis factorization_Gmat_thirteen hx hy hc hc1 hcx hcy hyx hkx hky hux huy hg1
    hno

end CFSG.StandardType.SporadicShape
