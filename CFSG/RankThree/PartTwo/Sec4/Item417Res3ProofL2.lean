module

public import CFSG.RankThree.PartTwo.Sec4.Item417Res3ProofTools
import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
import CFSG.RankThree.PartTwo.Census.OddClassical.LinearTwo
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2CoprimeSylowCyclic
import CFSG.Dihedral.Glauberman.DicksonMaxUp
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LieType.Multipliers.ProductKernel
public import CFSG.LieType.Multipliers.U42Bridge
public import CFSG.LieType.Multipliers.U43Action
public import CFSG.LieType.Multipliers.U43BridgeInputs
public import CFSG.LieType.Multipliers.U62Action
public import CFSG.LieType.Multipliers.U62Bridge
public import CFSG.LieType.Multipliers.U62Kernel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionQuaternion
public import CFSG.LocalAnalysis.ComponentClassification.TBLitCover
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBFixedLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsGen
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Amalgam.Data
public import CFSG.Monster.B.TwoA.Sp8.Par1
public import CFSG.Monster.B.TwoA.Unitary.LinThree
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec4.Item47
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
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
public import Certificates.Certificate12041
public import Certificates.Certificate12042
public import Certificates.Certificate12043
public import Certificates.Certificate12044
public import Certificates.Certificate12045
public import Certificates.Certificate12046
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

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)

open scoped MatrixGroups

namespace Res417Three

theorem pRank_le_one_of_isCyclic_sylow {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (h : ∀ R : Sylow p X, IsCyclic R) : CFSG.pRank p X ≤ 1 := by
  refine csSup_le' ?_
  rintro r ⟨B, hB, hr⟩
  have hBp : IsPGroup p B := by
    refine IsPGroup.of_card (n := r) hr
  obtain ⟨R, hBR⟩ := hBp.exists_le_sylow
  have hRc := h R
  have hBc : IsCyclic B := Subgroup.isCyclic_of_le hBR
  obtain ⟨x, hx⟩ := hBc.exists_generator
  have hcard : Nat.card B = orderOf x := by
    rw [← Nat.card_zpowers]
    have : Subgroup.zpowers x = ⊤ := by
      rw [eq_top_iff]
      intro y _
      exact hx y
    rw [this, Subgroup.card_top]
  have hxp : x ^ p = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hB.exponent_dvd_p x
  have hle : Nat.card B ≤ p := by
    rw [hcard]
    exact Nat.le_of_dvd (Fact.out : p.Prime).pos (orderOf_dvd_of_pow_eq_one hxp)
  rw [hr] at hle
  by_contra hr1
  have : p ^ 2 ≤ p ^ r := Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by omega)
  have : p < p ^ 2 := by
    have := (Fact.out : p.Prime).one_lt
    nlinarith
  omega

theorem pRank_le_one_of_not_dvd {X : Type*} [Group X] [Finite X] {p : ℕ}
    (h : ¬ p ^ 2 ∣ Nat.card X) : CFSG.pRank p X ≤ 1 := by
  refine csSup_le' ?_
  rintro r ⟨B, -, hr⟩
  by_contra hr1
  exact h ((Nat.pow_dvd_pow p (by omega : 2 ≤ r)).trans
    (hr ▸ Subgroup.card_subgroup_dvd_card B))

theorem pRank_three_PSL2_le_one {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (he : 1 ≤ e) : CFSG.pRank 3 (PSL(2, GaloisField p e)) ≤ 1 := by
  have hp : p.Prime := Fact.out
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e (by omega)
  have hp5 : 5 ≤ p := by
    have := hp.two_le
    rcases (show p = 2 ∨ p = 3 ∨ p = 4 ∨ 5 ≤ p by omega) with h | h | h | h
    · exact absurd h hp2
    · exact absurd h hp3
    · exact absurd (h ▸ hp) (by norm_num)
    · exact h
  by_cases h7 : 7 ≤ p ^ e
  · refine pRank_le_one_of_isCyclic_sylow fun R => ?_
    refine CFSG.GorensteinWalter.psl2_sylow_isCyclic_of_coprime_field_card (GaloisField p e) hK
      (by rw [hK]; exact h7) 3 (by norm_num) ?_ R
    rw [hK]
    refine Nat.Coprime.pow_right e ?_
    exact (Nat.coprime_primes Nat.prime_three hp).mpr (Ne.symm hp3)
  ·
    have hpe : p = 5 ∧ e = 1 := by
      have h1 : p ≤ p ^ e := Nat.le_self_pow (by omega) p
      have h6 : p ≠ 6 := by
        rintro rfl
        exact absurd hp (by norm_num)
      have hp' : p = 5 := by omega
      subst hp'
      refine ⟨rfl, ?_⟩
      by_contra he1
      have : 5 ^ 2 ≤ 5 ^ e := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    obtain ⟨rfl, rfl⟩ := hpe
    refine pRank_le_one_of_not_dvd ?_
    rw [CFSG.Glauberman.Dickson.MaxUp.card_psl2_galoisField (by norm_num) (by norm_num)]
    norm_num

theorem noSix_PSL2_charThree {K : Type} [Field K] [CharP K 3] : NoSix (PSL(2, K)) := by
  intro y t hy ht hyt
  by_contra hne
  obtain ⟨hy1, ht1⟩ := not_or.mp hne
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.RankThree.PartTwo.Census.not_commute_PSL_two_char_three y t
    (orderOf_eq_prime hy hy1) (orderOf_eq_prime ht ht1) hyt

end Res417Three

open Res417Three

section Certs


theorem item417OutL2_holds : Item417OutL2 := by
  intro G _ _ L A E c m hconf ⟨p, e, _, hp2, he, ⟨φ⟩⟩
  exfalso
  set eS : L ⧸ Subgroup.center L ≃* PSL(2, GaloisField p e) :=
    hconf.centerEquiv.trans (φ.trans (projSLEquivPSL _)) with heS
  by_cases hp3 : p = 3
  · subst hp3
    exact hconf.false_of_noSix (noSix_PSL2_charThree.of_mulEquiv eS)
  · have : Finite (PSL(2, GaloisField p e)) := Finite.of_equiv _ eS.toEquiv
    exact hconf.false_of_pRank_le_one eS (pRank_three_PSL2_le_one hp2 hp3 he)

end Certs

end CFSG.RankThree.PartTwo.Sec4
