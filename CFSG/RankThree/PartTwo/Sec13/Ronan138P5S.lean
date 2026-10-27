module

public import CFSG.RankThree.PartTwo.Sec13.Ronan138P5Res
import CFSG.RankThree.PartTwo.Sec13.Ronan138P5Elem
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
import CFSG.RankThree.PartTwo.Sec13.Item13Models
import CFSG.RankThree.PartTwo.Sec6.Item65Tools
import CFSG.RankThree.GF2n.Basic
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration

public section

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138P5

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSU)
open Matrix (ProjGenLinGroup)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem exists_involution_projSU (n : ℕ) (hn : 1 ≤ n) :
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    ∃ t : projSU 3 2 n, t ≠ 1 ∧ t ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hπ : false = false → CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n
      (GaloisField 2 (2 * n)) := fun _ => (Sec13.piField_galoisField_two 2 n hn).unitary
  have hmem : ProjGenLinGroup.mk (negSwap01 : GL (Fin 3) (GaloisField 2 (2 * n))) ∈
      projSU 3 2 n := by
    rw [projSU_eq_projImage]
    exact ⟨_, negSwap01_mem_slPi hπ, rfl⟩
  refine ⟨⟨_, hmem⟩, fun h => ?_, Subtype.ext ?_⟩
  · have h' := congrArg Subtype.val h
    simp only [OneMemClass.coe_one] at h'
    exact mk_ne_one_of_offdiag_ne (i := 0) (k := 1) (by decide) (by simp [coe_negSwap01]) h'
  · rw [SubgroupClass.coe_pow, ← map_pow, negSwap01_sq, map_one]
    rfl

theorem step13PZeroS_holds : Step13PZeroS := by
  intro G _ _ A c L P₀ n hU
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := hU.sec13
  have hc := h.orderOf_eq
  have hc3 : c ^ 3 = 1 := hc ▸ pow_orderOf_eq_one c
  have hc1 : c ≠ 1 := h.ne_one
  have hLc := h.le_centralizer
  have hL := h.mem_thetaComponentsAt
  have hLp : Group.IsPerfect L := Sec6.isPerfect_of_mem_thetaComponentsAt hL
  have hP₀3 : IsPGroup 3 P₀ := CFSG.Open.IsElemAbelian.isPGroup hU.elem
  set J := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer (P₀ : Set G)) with hJdef
  set θL := inSubgroup (aschbacherSolvableCore 3) L with hθL
  have hcov : L ≤ J ⊔ θL := Sec6.le_residual_inf_centralizer_sup_theta hLp hP₀3 hU.le
  have hJL : J ≤ L := (Sec6.inSubgroup_perfectResidual_le _).trans inf_le_left
  have hJP : J ≤ Subgroup.centralizer (P₀ : Set G) :=
    (Sec6.inSubgroup_perfectResidual_le _).trans inf_le_right
  obtain ⟨φ⟩ := hU.iso
  obtain ⟨t₀, ht₀1, ht₀2⟩ := exists_involution_projSU n (by have := hU.one_lt; omega)
  set tb := φ.symm t₀ with htb
  have htb1 : tb ≠ 1 := fun h1 => ht₀1 (by simpa [htb] using congrArg φ h1)
  have htb2 : tb ^ 2 = 1 := by rw [htb, ← map_pow, ht₀2, map_one]
  obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective tb
  have hlJ : (l : G) ∈ (J : Set G) * (θL : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right J θL
      (hJL.trans (Sec6.le_normalizer_theta L))]
    exact hcov l.2
  obtain ⟨j, hj, k, hk, hjk⟩ := hlJ
  have hjLm : j ∈ L := hJL hj
  have hkL : k ∈ L := Sec6.theta_le L hk
  have hjimg : ((⟨j, hjLm⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) = tb := by
    rw [← hl]
    apply QuotientGroup.eq.mpr
    obtain ⟨k', hk', rfl⟩ := hk
    have : (⟨j, hjLm⟩ : L)⁻¹ * l = k' := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← hjk]
      simp
    rw [this]
    exact hk'
  set m := orderOf (⟨j, hjLm⟩ : L) with hm
  have hm0 : m ≠ 0 := (orderOf_pos _).ne'
  have hmab : 2 ^ m.factorization 2 * (m / 2 ^ m.factorization 2) = m :=
    Nat.ordProj_mul_ordCompl_eq_self m 2
  have hbodd : ¬ 2 ∣ m / 2 ^ m.factorization 2 :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp (Nat.coprime_ordCompl Nat.prime_two hm0)
  set b := m / 2 ^ m.factorization 2 with hb
  set wL : L := (⟨j, hjLm⟩ : L) ^ b with hwL
  have hwimg : (wL : L ⧸ aschbacherSolvableCore 3 L) = tb := by
    rw [hwL, QuotientGroup.mk_pow, hjimg]
    obtain ⟨r, hr⟩ : ∃ r, b = 2 * r + 1 := ⟨b / 2, by omega⟩
    rw [hr, pow_succ, pow_mul, htb2, one_pow, one_mul]
  have hw2 : wL ^ (2 ^ m.factorization 2) = 1 := by
    rw [hwL, ← pow_mul, mul_comm, hmab, hm, pow_orderOf_eq_one]
  set w : G := (wL : G) with hw
  have hwJ : w ∈ J := by
    rw [hw, hwL, Subgroup.coe_pow]
    exact J.pow_mem hj b
  have hwθ : w ∉ θL := by
    intro hwθ
    apply htb1
    rw [← hwimg, QuotientGroup.eq_one_iff]
    obtain ⟨k', hk', hk'e⟩ := hwθ
    have : wL = k' := Subtype.ext hk'e.symm
    rw [this]
    exact hk'
  set S₀ : Subgroup G := Subgroup.zpowers w with hS₀
  have hS₀2 : IsPGroup 2 S₀ := by
    intro v
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp v.2
    refine ⟨m.factorization 2, Subtype.ext ?_⟩
    rw [SubgroupClass.coe_pow, ← hi, OneMemClass.coe_one, ← zpow_natCast, ← _root_.zpow_mul,
      mul_comm, _root_.zpow_mul, zpow_natCast, hw, ← Subgroup.coe_pow, hw2, Subgroup.coe_one,
      _root_.one_zpow]
  have hS₀1 : S₀ ≠ ⊥ := by
    intro hbot
    apply hwθ
    have : w ∈ S₀ := Subgroup.mem_zpowers w
    rw [hbot, Subgroup.mem_bot] at this
    rw [this]
    exact θL.one_mem
  have hS₀J : S₀ ≤ J := Subgroup.zpowers_le.mpr hwJ
  refine ⟨S₀, hS₀1, hS₀2, hS₀J, fun hle => hwθ (hle (Subgroup.mem_zpowers w)), ?_⟩
  set M := Subgroup.normalizer (S₀ : Set G) with hMdef
  set T := CFSG.Open.pCoreOf 2 M with hTdef
  obtain ⟨hT2', -, hMT'⟩ := CFSG.RankThree.GF2n.inSubgroup_pCore_two M
  have hT2 : IsPGroup 2 T := hT2'
  have hMT : M ≤ Subgroup.normalizer (T : Set G) := hMT'
  have hM2 : CFSG.Open.IsTwoLocal M := ⟨S₀, hS₀1, hS₀2, rfl⟩
  have hchar := h.charTwoType M hM2
  have hcM : c ∈ M := by
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun s hs => ?_)
    exact Subgroup.mem_centralizer_singleton_iff.mp (hLc (hJL (hS₀J hs)))
  have hcT : c ∉ Subgroup.centralizer (T : Set G) := by
    intro hcC
    have hcT : c ∈ T := hchar ⟨hcM, hcC⟩
    obtain ⟨k, hk⟩ := hT2 ⟨c, hcT⟩
    have hk' : c ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have h1 := orderOf_dvd_of_pow_eq_one hk'
    rw [hc] at h1
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h1)
    omega
  have hP₀M : P₀ ≤ M := by
    intro p hp
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun s hs => ?_)
    exact (Subgroup.mem_centralizer_iff.mp (hJP (hS₀J hs)) p hp).symm
  have hP₀T : P₀ ≤ Subgroup.normalizer (T : Set G) := hP₀M.trans hMT
  have hT3 : ¬ 3 ∣ Nat.card T := by
    obtain ⟨k, hk⟩ := hT2.exists_card_eq
    rw [hk]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
    omega
  have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane
    3 Nat.prime_three P₀ T (fun m => Subtype.ext (by simpa using hU.elem.2 m m.2))
    (by rw [hU.card]; norm_num) hT3 hP₀T
  by_contra hall
  simp only [not_exists, not_and, not_not] at hall
  apply hcT
  have hTc : T ≤ Subgroup.centralizer ({c} : Set G) := by
    rw [hgen]
    refine iSup_le fun x => iSup_le fun hx1 => ?_
    by_cases hxc : (x : G) ∈ Subgroup.zpowers c
    · have hx1' : (x : G) ≠ 1 := fun h => hx1 (Subtype.ext h)
      have hx3 : (x : G) ^ 3 = 1 := hU.elem.2 x x.2
      have heq : Subgroup.zpowers (x : G) = Subgroup.zpowers c :=
        Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxc) (by
          rw [Nat.card_zpowers, Nat.card_zpowers, hc, orderOf_eq_prime hx3 hx1'])
      rw [← centralizer_singleton_eq_of_zpowers_eq heq]
      exact inf_le_right
    · have := hall x x.2 hxc
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at this
      rwa [Sec6.centralizer_zpowers_eq] at this
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hTc ht))

end CFSG.RankThree.PartTwo.Sec13.Ronan138P5
