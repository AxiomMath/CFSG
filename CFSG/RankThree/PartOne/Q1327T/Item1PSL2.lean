module

public import CFSG.RankThree.PartOne.Q1327T.ItemBasic
public import CFSG.RankThree.PartOne.K133.Item1
public import CFSG.RankThree.PartOne.K133.MaxItems
import CFSG.Adapters.LinearCatalog
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.LieType.Chevalley.RootCommutatorData
public import CFSG.LieType.Multipliers.ProductKernel
public import CFSG.LieType.Multipliers.U42Bridge
public import CFSG.LieType.Multipliers.U43Action
public import CFSG.LieType.Multipliers.U43BridgeInputs
public import CFSG.LieType.Multipliers.U62Action
public import CFSG.LieType.Multipliers.U62Bridge
public import CFSG.LieType.Multipliers.U62Kernel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsGen
public import CFSG.Milestones.CL_LIT_Griess_Schur_multipliers_Lie_type
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Amalgam.Data
public import CFSG.Monster.B.TwoA.Sp8.Par1
public import CFSG.Monster.B.TwoA.Unitary.LinThree
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.PartOne.K133.SylowKill
public import CFSG.RankThree.PartOne.KF.ClsBasic
public import CFSG.RankThree.PartOne.S11.TwoActionWiring
public import CFSG.RankThree.PartOne.S12.InputsSec15
public import CFSG.RankThree.PartOne.S12.Sec137
public import CFSG.RankThree.PartOne.S12.Sec15FA
public import CFSG.RankThree.PartOne.S12.Sec15Items
public import CFSG.RankThree.PerfectCover.HopfCentralCoversFinite
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CommutatorNormalizer
public import CFSG.YGroups.Y322Central
public import Certificates.Certificate10005
public import Certificates.Certificate10006
public import Certificates.Certificate10007
public import Certificates.Certificate10008
public import Certificates.Certificate10009
public import Certificates.Certificate10010
public import Certificates.Certificate10012
public import Certificates.Certificate10013
public import Certificates.Certificate10014
public import Certificates.Certificate10016
public import Certificates.Certificate10018
public import Certificates.Certificate116
public import Certificates.Certificate119
public import Certificates.Certificate12041
public import Certificates.Certificate12042
public import Certificates.Certificate12043
public import Certificates.Certificate12044
public import Certificates.Certificate12045
public import Certificates.Certificate12046
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate16015
public import Certificates.Certificate16040
public import Certificates.Certificate2154
public import Certificates.Certificate2157
public import Certificates.Certificate2267
public import Certificates.Certificate2326
public import Certificates.Certificate3006
public import Certificates.Certificate3007
public import Certificates.Certificate3008
public import Certificates.Certificate3063
public import Certificates.Certificate3077
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate3951
public import Certificates.Certificate8033
public import Certificates.Certificate9130

public section

namespace CFSG.RankThree.PartOne.Q1327T

open CFSG CFSG.GorensteinWalter CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K
open CFSG.RankThree.PartOne.Census3 (IsoLie)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

theorem row8U3Item_zero : Row8U3Item 0 := by
  classical
  intro Q _ _ p g Ē hX h
  exfalso
  have hp := h.prime
  have hp2 : p ≠ 2 := by have := h.five_le; omega
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨c, x, K, hc1, hcp, hKc, hKmodel, hxK, hxo, hEel, hEcard⟩ := h.exists_T
  obtain ⟨q, hq2, -, hv, ⟨e0⟩⟩ := hX
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have e : (Q ⧸ Subgroup.center Q) ≃* PSL2 (GaloisField q.p q.exponent) :=
    e0.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv)
  by_cases hpr : p = q.p
  ·
    subst hpr
    have hec1 : e c ≠ 1 := fun h1 => hc1 (e.injective (by rw [h1, map_one]))
    have hecp : e c ^ q.p = 1 := by rw [← map_pow, hcp, map_one]
    have hPg : IsPGroup q.p K := by
      intro k
      refine ⟨1, ?_⟩
      have hcomm : e c * e (k : Q ⧸ Subgroup.center Q) = e (k : Q ⧸ Subgroup.center Q) * e c := by
        rw [← map_mul, ← map_mul]
        exact congrArg e (Subgroup.mem_centralizer_singleton_iff.1 (hKc k.2)).symm
      have := K133.psl2_centralizer_pow (F := GaloisField q.p q.exponent) hp2 (e c)
        (e (k : Q ⧸ Subgroup.center Q)) hec1 hecp hcomm
      apply Subtype.ext
      apply e.injective
      simpa [← map_pow] using this
    have : Group.IsNilpotent K := hPg.isNilpotent
    have hsol : Group.IsSolvable K := inferInstance
    obtain ⟨hKs, a, b, hab⟩ := simple_nonab_of_model hKmodel
    have := hKs
    exact hab ((IsSimpleGroup.comm_iff_isSolvable).2 hsol a b)
  · have hne : ((p : ℕ) : GaloisField q.p q.exponent) ≠ 0 := by
      intro h0
      rw [CharP.cast_eq_zero_iff (GaloisField q.p q.exponent) q.p p] at h0
      exact hpr ((Nat.prime_dvd_prime_iff_eq q.prime_p hp).1 h0).symm
    have : NeZero ((p : ℕ) : GaloisField q.p q.exponent) := ⟨hne⟩
    have hA : IsElementaryAbelian p ↥((Subgroup.zpowers c ⊔ Subgroup.zpowers x).map
        e.toMonoidHom) := by
      have := hEel
      exact IsElementaryAbelian.map e.toMonoidHom
    have hcard := K133.psl2_elemAb_card_le hp hp2 _ hA
    rw [Subgroup.card_map_of_injective e.injective, hEcard] at hcard
    have : p < p ^ 2 := by
      calc p = p ^ 1 := (pow_one p).symm
        _ < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega

end CFSG.RankThree.PartOne.Q1327T
