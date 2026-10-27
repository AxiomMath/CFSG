module

public import CFSG.Quasithin.Recognition.F112Crit.BenderLocalOf

import CFSG.Quasithin.Recognition.SzVBBridgeAux
import CFSG.Certificates.Kernel.LocalCompTits.Span
import CFSG.GH74.Uniqueness.Bender.UnitaryAut
import CFSG.Holt.Centralizer
import CFSG.Holt.Witt
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
import CFSG.Quasithin.Background.D14Normal
import CFSG.Quasithin.Background.E1
import CFSG.Quasithin.Background.E1Sec4
import CFSG.Quasithin.Background.E1Sec5
import CFSG.Quasithin.Background.E1Sec8
import CFSG.Quasithin.Background.E3Cent
import CFSG.Quasithin.Background.F6SolvableQuotient
import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
import CFSG.Quasithin.EmptyFaithful.S1417Sylow
import CFSG.Quasithin.EmptyFaithful.S1421QA19Bend
import CFSG.Quasithin.Recognition.F112J2FamC
import CFSG.Quasithin.Recognition.F112J2Struct
import CFSG.Quasithin.Recognition.F112RGold
import CFSG.Quasithin.Recognition.F112WChief
import CFSG.Quasithin.Recognition.F112WValency
import CFSG.Quasithin.Recognition.ModelBridges
import CFSG.Quasithin.Vol2.Ch1Faithful
import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
import Certificates.Kernel.J4Count.FixCE
import Certificates.Kernel.J4Count.FixCPairBase1
import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.Quasithin.F112Crit.BenderLocalOf

open CFSG.Open CFSG.QuasithinUnique CFSG.GH74.Uniqueness.Bender CFSG.Holt.H78
open CFSG.Quasithin.SzVB

theorem lift_fix_two_elt {G : Type} [Group G] [Finite G]
    {X T : Subgroup G} {n i e : ℕ} (hX : BenderType (oTwoQuot ↥X) n i e) (hi : i ≠ 3)
    (hT : IsSylowTwoOf T X) {d x y : G} (hd : d ∈ X) (hdO : d ∉ pCoreOf 2 X)
    (hdN : d ∈ Subgroup.normalizer (T : Set G)) (hx : x ∈ X)
    (hxN : x ∉ Subgroup.normalizer (T : Set G))
    (hxd : x⁻¹ * d * x ∈ Subgroup.normalizer (T : Set G)) (hy : y ∈ X)
    (hyd : y⁻¹ * d * y ∈ Subgroup.normalizer (T : Set G)) :
    y ∈ Subgroup.normalizer (T : Set G) ∨ x⁻¹ * y ∈ Subgroup.normalizer (T : Set G) := by
  classical
  let K := oTwoQuot ↥X
  let π : ↥X →* K := QuotientGroup.mk' (pCore 2 ↥X)
  obtain ⟨P, hP⟩ := exists_sylow_oTwoQuot hT
  have hmem : ∀ z : ↥X, π z ∈ Subgroup.normalizer ((P : Subgroup K) : Set K) ↔
      (z : G) ∈ Subgroup.normalizer (T : Set G) := fun z => by
    rw [← Subgroup.mem_comap, comap_normalizer_oTwoQuot hT hP, Subgroup.mem_subgroupOf]
  have hA : IsBenderAction K (K ⧸ borel (P : Subgroup K)) n i e :=
    isBenderAction_borelCosets hX P
  have hdN' : π ⟨d, hd⟩ ∈ Subgroup.normalizer ((P : Subgroup K) : Set K) :=
    (hmem ⟨d, hd⟩).mpr hdN
  have hmapx : π (⟨x, hx⟩⁻¹ * ⟨d, hd⟩ * ⟨x, hx⟩) =
      (π ⟨x, hx⟩)⁻¹ * π ⟨d, hd⟩ * π ⟨x, hx⟩ := by
    rw [map_mul, map_mul, map_inv]
  have hxdN : (π ⟨x, hx⟩)⁻¹ * π ⟨d, hd⟩ * π ⟨x, hx⟩ ∈
      Subgroup.normalizer ((P : Subgroup K) : Set K) := by
    rw [← hmapx]
    refine (hmem _).mpr ?_
    change x⁻¹ * d * x ∈ Subgroup.normalizer (T : Set G)
    exact hxd
  have hmapy : π (⟨y, hy⟩⁻¹ * ⟨d, hd⟩ * ⟨y, hy⟩) =
      (π ⟨y, hy⟩)⁻¹ * π ⟨d, hd⟩ * π ⟨y, hy⟩ := by
    rw [map_mul, map_mul, map_inv]
  have hydN : (π ⟨y, hy⟩)⁻¹ * π ⟨d, hd⟩ * π ⟨y, hy⟩ ∈
      Subgroup.normalizer ((P : Subgroup K) : Set K) := by
    rw [← hmapy]
    refine (hmem _).mpr ?_
    change y⁻¹ * d * y ∈ Subgroup.normalizer (T : Set G)
    exact hyd
  have hdα : (π ⟨d, hd⟩ : K) • ((QuotientGroup.mk 1 : K ⧸ borel (P : Subgroup K))) =
      (QuotientGroup.mk 1 : K ⧸ borel (P : Subgroup K)) := by
    rw [MulAction.Quotient.smul_mk, QuotientGroup.eq]
    change ((π ⟨d, hd⟩ * 1)⁻¹ * 1) ∈ Subgroup.normalizer ((P : Subgroup K) : Set K)
    simpa only [mul_one] using
      (Subgroup.normalizer ((P : Subgroup K) : Set K)).inv_mem hdN'
  have hdβ : (π ⟨d, hd⟩ : K) • (QuotientGroup.mk (π ⟨x, hx⟩) :
      K ⧸ borel (P : Subgroup K)) = QuotientGroup.mk (π ⟨x, hx⟩) := by
    rw [MulAction.Quotient.smul_mk, QuotientGroup.eq]
    change ((π ⟨d, hd⟩ * π ⟨x, hx⟩)⁻¹ * π ⟨x, hx⟩) ∈
      Subgroup.normalizer ((P : Subgroup K) : Set K)
    have e : ((π ⟨d, hd⟩ * π ⟨x, hx⟩)⁻¹ * π ⟨x, hx⟩) =
        ((π ⟨x, hx⟩)⁻¹ * π ⟨d, hd⟩ * π ⟨x, hx⟩)⁻¹ := by
      group
    rw [e]
    exact (Subgroup.normalizer ((P : Subgroup K) : Set K)).inv_mem hxdN
  have hdinf : (π ⟨d, hd⟩ : K) ∈
      MulAction.stabilizer K (QuotientGroup.mk (1 : K) : K ⧸ borel (P : Subgroup K)) ⊓
        MulAction.stabilizer K (QuotientGroup.mk (π ⟨x, hx⟩) :
          K ⧸ borel (P : Subgroup K)) :=
    Subgroup.mem_inf.mpr ⟨MulAction.mem_stabilizer_iff.mpr hdα,
      MulAction.mem_stabilizer_iff.mpr hdβ⟩
  by_cases hya : y ∈ Subgroup.normalizer (T : Set G)
  · exact Or.inl hya
  by_cases hxy : x⁻¹ * y ∈ Subgroup.normalizer (T : Set G)
  · exact Or.inr hxy
  have hαβ : (QuotientGroup.mk (1 : K) : K ⧸ borel (P : Subgroup K)) ≠
      QuotientGroup.mk (π ⟨x, hx⟩) := by
    intro h
    rw [QuotientGroup.eq] at h
    change ((1 : K)⁻¹ * π ⟨x, hx⟩) ∈ Subgroup.normalizer
      ((P : Subgroup K) : Set K) at h
    rw [inv_one, one_mul] at h
    exact hxN ((hmem ⟨x, hx⟩).mp h)
  have hγα : (QuotientGroup.mk (π ⟨y, hy⟩) : K ⧸ borel (P : Subgroup K)) ≠
      QuotientGroup.mk (1 : K) := by
    intro h
    rw [QuotientGroup.eq] at h
    change ((π ⟨y, hy⟩)⁻¹ * (1 : K)) ∈ Subgroup.normalizer
      ((P : Subgroup K) : Set K) at h
    rw [mul_one] at h
    exact hya ((hmem ⟨y, hy⟩).mp (inv_mem_iff.mp h))
  have hγβ : (QuotientGroup.mk (π ⟨y, hy⟩) : K ⧸ borel (P : Subgroup K)) ≠
      QuotientGroup.mk (π ⟨x, hx⟩) := by
    intro h
    rw [QuotientGroup.eq] at h
    change ((π ⟨y, hy⟩)⁻¹ * π ⟨x, hx⟩) ∈ Subgroup.normalizer
      ((P : Subgroup K) : Set K) at h
    have h2 : π (⟨y, hy⟩⁻¹ * ⟨x, hx⟩) ∈
        Subgroup.normalizer ((P : Subgroup K) : Set K) := by
      rw [map_mul, map_inv]
      exact h
    have h3 : ((⟨y, hy⟩⁻¹ * ⟨x, hx⟩ : ↥X) : G) ∈
        Subgroup.normalizer (T : Set G) := (hmem _).mp h2
    change y⁻¹ * x ∈ Subgroup.normalizer (T : Set G) at h3
    refine hxy ?_
    have h4 := (Subgroup.normalizer (T : Set G)).inv_mem h3
    have e : (y⁻¹ * x)⁻¹ = x⁻¹ * y := by group
    rwa [e] at h4
  have hdγ : (π ⟨d, hd⟩ : K) • (QuotientGroup.mk (π ⟨y, hy⟩) :
      K ⧸ borel (P : Subgroup K)) = QuotientGroup.mk (π ⟨y, hy⟩) := by
    rw [MulAction.Quotient.smul_mk, QuotientGroup.eq]
    change ((π ⟨d, hd⟩ * π ⟨y, hy⟩)⁻¹ * π ⟨y, hy⟩) ∈
      Subgroup.normalizer ((P : Subgroup K) : Set K)
    have e : ((π ⟨d, hd⟩ * π ⟨y, hy⟩)⁻¹ * π ⟨y, hy⟩) =
        ((π ⟨y, hy⟩)⁻¹ * π ⟨d, hd⟩ * π ⟨y, hy⟩)⁻¹ := by
      group
    rw [e]
    exact (Subgroup.normalizer ((P : Subgroup K) : Set K)).inv_mem hydN
  have hd1 : (π ⟨d, hd⟩ : K) = 1 :=
    hA.eq_one_of_mem_stabilizer_inf_of_smul_eq hi hαβ hdinf hγα hγβ hdγ
  have hd1' : QuotientGroup.mk' (pCore 2 ↥X) ⟨d, hd⟩ = 1 := hd1
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hd1'
  exact absurd ((F1.mem_pCore_iff_coe ⟨d, hd⟩).mp hd1') hdO

end CFSG.Quasithin.F112Crit.BenderLocalOf

