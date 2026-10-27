module

public import CFSG.RankThree.PartTwo.Sec15.Ronan155RDiamond
public import CFSG.RankThree.PartTwo.Sec15.Ronan155RKFact
public import CFSG.RankThree.PartTwo.Sec15.Item155w2ProofCases
public import CFSG.RankThree.PartTwo.Sec15.Item155wProofCorr
import CFSG.RankThree.PartTwo.Sec15.Ronan155RQ
import CFSG.RankThree.PartTwo.Sec15.Ronan155RAut
import CFSG.RankThree.PartTwo.Sec15.Item155wProof
import CFSG.RankThree.PartTwo.Sec15.Item155Proof
import CFSG.RankThree.PartTwo.Sec15.Item153Claims
import CFSG.RankThree.PartTwo.Sec15.Item152Proof
import CFSG.RankThree.PartTwo.Sec15.Item1424Proof
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec13.Item13Models
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.CharTwo
import CFSG.GroupTheory.PCore.OpenTransport
import CFSG.Models.PGLSimple
import CFSG.GroupTheory.PCore.Transport
import CFSG.RankThree.PartTwo.Sec15.Item1424ProofFive
import CFSG.RankThree.PartTwo.Sec15.Item1424ProofNotHJ

public section

namespace CFSG.RankThree.PartTwo.Sec15.Ronan155R

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec15

theorem two_le_of_isoLThreePi {Q : Type} [Group Q] (hq : CFSG.IsQuasisimple Q) {n : ℕ}
    (hn : 1 ≤ n) (hπ : haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩; Sec4.IsoLThreePi Q 2 n) :
    2 ≤ n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hlt
  have hn1 : n = 1 := by omega
  subst hn1
  obtain ⟨hperf, -, a, b, hab⟩ := hq
  rcases hπ with ⟨h3, -⟩ | ⟨-, ⟨ψ⟩⟩
  · norm_num at h3
  · have hsol : Group.IsSolvable (CFSG.Assembly.RankThreeEven.projSU 3 2 1) :=
      Sec13.isSolvable_projSU_two
    have : Group.IsSolvable Q :=
      Group.isSolvable_of_isSolvable_injective (f := ψ.toMonoidHom) ψ.injective
    by_cases hnt : Nontrivial Q
    · exact Group.IsPerfect.not_isSolvable Q inferInstance
    · rw [not_nontrivial_iff_subsingleton] at hnt
      exact hab (Subsingleton.elim _ _)

theorem diamondCharR_of_kf (hY4 : Y4LThreePiNHJR) (h152 : Item152R) (h153 : Item153MainR)
    (hgrow : Step155GrowWR) (h146 : Item146S14) (h1444 : Item1444S14) (hbot : Item145BotS14)
    (hYQ : Step155YQ0WR) (hPJQ : Step155PJQ0WR) (hkf : KFSubL3) : DiamondCharR := by
  intro G _ _ A c L hR hNHJ X K Y M T hC hmax hab hcl hK J hJM hJ0 hXJ n m hn hm hφ hXε
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ⟩ := hφ
  have hS : Sec14Std G A c L := hR.toSec14Std
  have hX4 : X ∈ scriptY4 A (lB A) := hC.res ▸ hC.isY.2.1
  have hY3 : Y ∈ scriptY3 A (lB A) := hC.isY.1
  have hXp : Group.IsPerfect ↥X := isPerfect_of_mem_scriptY4 hX4
  have hn2 : 2 ≤ n :=
    two_le_of_isoLThreePi hX4.2.2.2 hn (hY4 G A c L hR hNHJ X hX4 n hn hXε)
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY3.1.1.2
  have hAR : A ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) :=
    hAY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)
  have hclaim : Claim155 A K Y := by
    by_cases hKR : K ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G)
    · exact claim155_of_le_normalizer (h153 G A c L hR) hC.mem_k hKR hAR
    · exact hgrow G A c L hR hS X K Y M T hC hmax hab hKR
  obtain ⟨P, -, -, -, -, hQR, hVQ⟩ := exists_p_of_ctx155 hS (h152 G A c L hR) (h153 G A c L hR)
    (h1444 G A c L hS) (h146 G A c L hS) (hbot G A c L hS) (hYQ G A c L hR) (hPJQ G A c L hR)
    hC hmax hab hclaim hJM hJ0 hXJ
  set R := CFSG.Open.pCoreOf 2 Y with hRdef
  set V := CFSG.Open.pCoreOf 2 J with hVdef
  have hVR : V ≤ R := hVQ.trans hQR
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y
  have hR1 : R ≠ ⊥ := hY3.1.2
  have hV2 : IsPGroup 2 V := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) J
  have hVJ : V ≤ J := CFSG.LieType.BorelTits.pCoreOf_le 2 J
  have hJV : J ≤ Subgroup.normalizer (V : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 J
  have hYX : Y ≤ Subgroup.normalizer (X : Set G) := by
    rw [← hC.res]
    exact le_normalizer_oPrimeResidualOf Subgroup.le_normalizer
  have hXY : X ≤ Y := by
    rw [← hC.res]
    exact Sec14.oPrimeResidualOf_le_self 3 Y
  have hM' : M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G) := by
    rw [sup_comm]
    exact hC.mem_m
  obtain ⟨hYM, -, -, hF⟩ := facts_of_mem_maximalTwoLocalsContaining hS hM'
  have hYJ : Y ≤ Subgroup.normalizer (J : Set G) :=
    le_normalizer_of_mem_thetaComponentsIn (hYM.trans Subgroup.le_normalizer) hJM hXJ
      (isPerfect_of_mem_scriptY4 hX4) (ne_bot_of_mem_scriptY4 hX4) hYX
  have hRY : R ≤ Y := CFSG.LieType.BorelTits.pCoreOf_le 2 Y
  have hRJ : R ≤ Subgroup.normalizer (J : Set G) := hRY.trans hYJ
  have hRV : R ≤ Subgroup.normalizer (V : Set G) :=
    hRJ.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 J)
  have hXR : X ≤ Subgroup.normalizer (R : Set G) :=
    hXY.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)
  have hMchar : CFSG.QuasithinUnique.CharTwo M := inf_centralizer_le_pCoreOf_of_fitting hF
  have hJsn : (J.subgroupOf M).IsSubnormal := ((mem_thetaComponentsIn_iff.mp hJM).2).2.1
  have hCV : J ⊓ Subgroup.centralizer (V : Set G) ≤ V :=
    CFSG.QuasithinUnique.CharTwo.of_isSubnormal hMchar (le_of_mem_thetaComponentsIn hJM) hJsn
  have hJp : Group.IsPerfect ↥J := isPerfect_of_mem_thetaComponentsIn hJM
  have hVsub : V.subgroupOf J = CFSG.pCore 2 ↥J := CFSG.openPCoreOf_subgroupOf 2 J
  haveI : (V.subgroupOf J).Normal := hVsub ▸ inferInstance
  set φ' : ↥J ⧸ V.subgroupOf J ≃*
      CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 (2 * n * m)) :=
    (QuotientGroup.quotientMulEquivOfEq hVsub).trans φ with hφ'
  haveI hsS : IsSimpleGroup (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 (2 * n * m))) :=
    CFSG.PGLModel.isSimpleGroup_projSL_of_two_le _ (by norm_num) (Or.inl (by norm_num))
      (Or.inl (by norm_num))
  have hsJ : IsSimpleGroup (↥J ⧸ V.subgroupOf J) := φ'.isSimpleGroup
  have hdich : ∀ W : Subgroup G, W ≤ J → J ≤ Subgroup.normalizer (W : Set G) →
      W ≤ V ∨ W = J := fun W hWJ hJW => le_or_eq_of_normal hJp hsJ hVJ hV2 hWJ hJW
  have hXV : X ⊓ V ≤ CFSG.Open.pCoreOf 2 X :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
      (le_normalizer_inf' Subgroup.le_normalizer (hXJ.trans hJV)) (hV2.to_le inf_le_right)
  set g := secHom hXJ φ' with hg
  have hHp : ⁅g.range, g.range⁆ = g.range := commutator_range_secHom hXJ φ' hXp
  have hNH : (CFSG.pCore 2 ↥X).map g ≤ g.range := Subgroup.map_le_range _ _
  have hN2 : IsPGroup 2 ((CFSG.pCore 2 ↥X).map g) := CFSG.pCore_isPGroup.map g
  have hHε : IsLThreeEpsAt (↥g.range ⧸ ((CFSG.pCore 2 ↥X).map g).subgroupOf g.range) 2 n := by
    obtain ⟨e⟩ := nonempty_mulEquiv_secHom hXJ φ' hXV
    rcases hXε with ⟨⟨ψ⟩⟩ | ⟨hq, ⟨ψ⟩⟩
    · exact Or.inl ⟨e.symm.trans ψ⟩
    · exact Or.inr ⟨hq, ⟨e.symm.trans ψ⟩⟩
  obtain ⟨hi, -, hiii, hiv⟩ := hkf n m hn2 hm g.range ((CFSG.pCore 2 ↥X).map g) hHp hNH hN2 hHε
  have hNbot : (CFSG.pCore 2 ↥X).map g = ⊥ :=
    hi _ hN2 ((Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mp inferInstance)
  have hO2V : CFSG.Open.pCoreOf 2 X ≤ V := by
    intro x hx
    have hxX : x ∈ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X hx
    have hx' : (⟨x, hxX⟩ : ↥X) ∈ CFSG.pCore 2 ↥X := (CFSG.mem_openPCoreOf_iff _).mp hx
    have h1 : g ⟨x, hxX⟩ ∈ (CFSG.pCore 2 ↥X).map g := Subgroup.mem_map_of_mem g hx'
    rw [hNbot, Subgroup.mem_bot] at h1
    exact (mem_ker_secHom hXJ φ' ⟨x, hxX⟩).mp h1
  have hRXO : X ⊓ R ≤ CFSG.Open.pCoreOf 2 X :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
      (le_normalizer_inf' Subgroup.le_normalizer hXR) (hR2.to_le inf_le_right)
  have hRX : ∀ r ∈ R, ∀ x ∈ X, r * x * r⁻¹ * x⁻¹ ∈ V := by
    intro r hr x hx
    have h1 : r * x * r⁻¹ * x⁻¹ ∈ X :=
      X.mul_mem ((Subgroup.mem_normalizer_iff.mp (hYX (hRY hr)) x).mp hx) (X.inv_mem hx)
    have h2 : r * x * r⁻¹ * x⁻¹ ∈ R := by
      have e : r * x * r⁻¹ * x⁻¹ = r * (x * r⁻¹ * x⁻¹) := by group
      rw [e]
      exact R.mul_mem hr ((Subgroup.mem_normalizer_iff.mp (hXR hx) _).mp (R.inv_mem hr))
    exact hO2V (hRXO (Subgroup.mem_inf.mpr ⟨h1, h2⟩))
  have hH : ∀ h ∈ g.range, ∃ x : ↥J, (x : G) ∈ X ∧ φ' (x : ↥J ⧸ V.subgroupOf J) = h :=
    fun h hh => exists_of_mem_range_secHom hXJ φ' hh
  exact exists_char_of_secCent hR2 hR1 hVR hJV hRJ hRV hCV hdich
    (h3_of_iii φ' hJV hRJ hRV hRX hH hiii) (h4_of_iv φ' hJV hRJ hRV hRX hH hiv)

theorem step155CasesTwoNHJWR_of_kf (hY4 : Y4LThreePiNHJR) (h152 : Item152R)
    (h153 : Item153MainR) (hgrow : Step155GrowWR) (h146 : Item146S14) (h1444 : Item1444S14)
    (hbot : Item145BotS14) (hYQ : Step155YQ0WR) (hPJQ : Step155PJQ0WR) (hkf : KFSubL3) :
    Step155CasesTwoNHJWR :=
  step155CasesTwoNHJWR_of_char hY4 h152 h153 hgrow
    (diamondCharR_of_kf hY4 h152 h153 hgrow h146 h1444 hbot hYQ hPJQ hkf)

end CFSG.RankThree.PartTwo.Sec15.Ronan155R
