module

public import CFSG.RankThree.PartTwo.Sec15.Notation
public import CFSG.RankThree.PartTwo.Sec14.Item14ListStatements
import CFSG.RankThree.PartTwo.Sec16.Item163ResProofMeets
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofKTypeTheta
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.RankThree.GroupTheory.SteinbergBMVanishingFullPerfectSupplement
import CFSG.RankThree.PartTwo.Sec8.HeringD4Tools
public import CFSG.RankThree.PartTwo.Sec14.Std
import CFSG.RankThree.PartTwo.Sec14.Item148StepOne

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof1511Field

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem isSolvable_ker_phi148 {A Y K : Subgroup G} [(ker148 A Y).Normal]
    (hY : Y ∈ scriptY4 A (lB A)) (hKY : K ≤ Y) (hKM : K ≤ Y ⊔ A) :
    Group.IsSolvable ↥(Main148.phi148 hKM).ker := by
  have hcomm : ⁅(Main148.phi148 hKM).ker, (Main148.phi148 hKM).ker⁆ ≤ CFSG.pCore 2 ↥K := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have hbY : (b : G) ∈ pPrimeCoreOf 3 Y :=
      (Main148.phi148_eq_one_iff hKM b).mp (MonoidHom.mem_ker.mp hb)
    have hb' : (⟨(b : G), hKY b.2⟩ : ↥Y) ∈ CFSG.pPrimeCore 3 ↥Y := by
      have h : (b : G) ∈ (CFSG.pPrimeCore 3 ↥Y).map Y.subtype := hbY
      obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.mp h
      rwa [show y = (⟨(b : G), hKY b.2⟩ : ↥Y) from Subtype.ext hyb] at hy
    have hc := Sec16.Res163.commutator_mem_pCore_two_of_mem_scriptY4 hY
      ⟨(a : G), hKY a.2⟩ ⟨(b : G), hKY b.2⟩ hb'
    have hmem : ((⁅a, b⁆ : ↥K) : G) ∈ CFSG.Open.pCoreOf 2 Y := by
      have hcG : ((⁅(⟨(a : G), hKY a.2⟩ : ↥Y), ⟨(b : G), hKY b.2⟩⁆ : ↥Y) : G) ∈
          CFSG.Open.pCoreOf 2 Y := Subgroup.mem_map_of_mem Y.subtype hc
      rwa [show ((⁅(⟨(a : G), hKY a.2⟩ : ↥Y), ⟨(b : G), hKY b.2⟩⁆ : ↥Y) : G) =
        ((⁅a, b⁆ : ↥K) : G) by
          simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]] at hcG
    exact Sec16.Res163.mem_pCore_two_of_mem_inf (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y)
      (hKY.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)) hmem
  have hsolP : Group.IsSolvable ↥(CFSG.pCore 2 ↥K) := by
    haveI : Group.IsNilpotent ↥(CFSG.pCore 2 ↥K) := CFSG.pCore_isPGroup.isNilpotent
    infer_instance
  exact CFSG.RankThree.PartTwo.Sec8.HeringD4.isSolvable_of_commutator_le
    (Main148.phi148 hKM).ker (CFSG.pCore 2 ↥K) hcomm hsolP

private theorem theta_le_ker_phi148 {A Y K : Subgroup G} [(ker148 A Y).Normal]
    (hKM : K ≤ Y ⊔ A) (hs : IsSimpleGroup ↥(img148 A Y K))
    (hnc : ∃ a b : ↥(img148 A Y K), a * b ≠ b * a) :
    aschbacherSolvableCore 3 ↥K ≤ (Main148.phi148 hKM).ker := by
  have hθsolv : Group.IsSolvable ↥(aschbacherSolvableCore 3 ↥K) :=
    (solvable_prime_complement_core_characterization (H := ↥K) Nat.prime_three).1
  haveI : (aschbacherSolvableCore 3 ↥K).Characteristic :=
    (solvable_prime_complement_core_characterization (H := ↥K) Nat.prime_three).2.1
  have hθn : (aschbacherSolvableCore 3 ↥K).Normal :=
    Subgroup.normal_of_characteristic _
  let eα : ↥(Main148.phi148 hKM).range ≃* ↥(img148 A Y K) :=
    MulEquiv.subgroupCongr (Main148.range_phi148 hKM)
  haveI : IsSimpleGroup ↥(Main148.phi148 hKM).range := by
    rw [Main148.range_phi148 hKM]
    exact hs
  have hncR : ∃ a b : ↥(Main148.phi148 hKM).range, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnc
    refine ⟨eα.symm a, eα.symm b, fun h => hab ?_⟩
    have h' := congrArg eα h
    simpa only [map_mul, MulEquiv.apply_symm_apply] using h'
  haveI : (aschbacherSolvableCore 3 ↥K).Normal := hθn
  have h := CFSG.RankThree.GroupTheory.SteinbergBM.le_ker_of_normal_of_isSolvable_of_isSimpleGroup
    hncR (Main148.phi148 hKM).rangeRestrict (Main148.phi148 hKM).rangeRestrict_surjective
    (aschbacherSolvableCore 3 ↥K) hθsolv
  rwa [MonoidHom.ker_rangeRestrict] at h

theorem mem_scriptY4_of_isoLThreePi_img148 {A Y K : Subgroup G} [(ker148 A Y).Normal]
    (hY : Y ∈ scriptY4 A (lB A)) (hKY : K ≤ Y) (hKp : Group.IsPerfect ↥K)
    (hKΔ : K = deltaZero A (lB A) K) {n : ℕ} (hn : 1 ≤ n)
    (hKn : Sec4.IsoLThreePi ↥(img148 A Y K) 2 n) : K ∈ scriptY4 A (lB A) := by
  have hKM : K ≤ Y ⊔ A := hKY.trans le_sup_left
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsPerfect ↥K := hKp
  have hperfα : Group.IsPerfect ↥(img148 A Y K) := isPerfect_img148 hKM
  haveI : Group.IsPerfect ↥(img148 A Y K) := hperfα
  have hsα := Sec19.Step1914TriProof.isSimpleGroup_of_isoLThreePi hn hKn
  have h3α : 3 ∣ Nat.card ↥(img148 A Y K) := Sec19.Step1914TriProof.three_dvd_card_of_isoLThreePi hn hKn
  haveI : IsSimpleGroup ↥(img148 A Y K) := hsα.1
  have hnc : ∃ a b : ↥(img148 A Y K), a * b ≠ b * a := by
    by_contra h
    push Not at h
    exact Group.IsPerfect.not_isSolvable _ (IsSimpleGroup.comm_iff_isSolvable.mp h)
  have hNs : Group.IsSolvable ↥(Main148.phi148 hKM).ker := isSolvable_ker_phi148 hY hKY hKM
  have hN3 : ¬ 3 ∣ Nat.card ↥(Main148.phi148 hKM).ker :=
    Main148.not_three_dvd_card_ker_phi148 hKM
  have hNleθ : (Main148.phi148 hKM).ker ≤ aschbacherSolvableCore 3 ↥K :=
    (solvable_prime_complement_core_characterization (H := ↥K) Nat.prime_three).2.2.2.1 _
      (MonoidHom.normal_ker _) hNs hN3
  have hθleN : aschbacherSolvableCore 3 ↥K ≤ (Main148.phi148 hKM).ker :=
    theta_le_ker_phi148 hKM hsα.1 hnc
  have hker : (Main148.phi148 hKM).ker = aschbacherSolvableCore 3 ↥K :=
    le_antisymm hNleθ hθleN
  have hθ : inSubgroup (aschbacherSolvableCore 3) K ≤ pPrimeCoreOf 3 Y := by
    rintro x ⟨k, hk, rfl⟩
    exact (Main148.phi148_eq_one_iff hKM k).mp (MonoidHom.mem_ker.mp (hθleN hk))
  let e : ↥K ⧸ aschbacherSolvableCore 3 ↥K ≃* ↥(img148 A Y K) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      ((QuotientGroup.quotientKerEquivRange (Main148.phi148 hKM)).trans
        (MulEquiv.subgroupCongr (Main148.range_phi148 hKM)))
  have hs : IsSimpleGroup (↥K ⧸ aschbacherSolvableCore 3 ↥K) := e.isSimpleGroup
  haveI : IsSimpleGroup (↥K ⧸ aschbacherSolvableCore 3 ↥K) := hs
  have hncθ : ∃ a b : ↥K ⧸ aschbacherSolvableCore 3 ↥K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnc
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    have h' := congrArg e h
    simpa only [map_mul, MulEquiv.apply_symm_apply] using h'
  have hKq : IsQuasisimple (↥K ⧸ aschbacherSolvableCore 3 ↥K) :=
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hncθ).1
  have h3 : 3 ∣ Nat.card K := h3α.trans (Main148.card_img148_dvd hKM)
  exact Sec16.Res163.mem_scriptY4_of_theta_le hY hKY hKp hKq hKΔ hθ hs h3

end CFSG.RankThree.PartTwo.Sec15.Proof1511Field

end
