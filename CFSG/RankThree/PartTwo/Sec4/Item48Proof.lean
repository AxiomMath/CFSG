module

public import CFSG.RankThree.PartTwo.Sec4.Statements
public import CFSG.RankThree.PartOne.TCB.SchreierFinal
import CFSG.RankThree.PartOne.S10.LocalThetaQuotientNormalizationEmbedding
import CFSG.RankThree.PartOne.S10.EmbeddingTransport
import CFSG.RankThree.PartOne.S10.AmbientTheta
import CFSG.RankThree.PartOne.S8.QuotientTransfer
import CFSG.RankThree.GroupTheory.SteinbergBMLargePrimeNormalizeComponents
import CFSG.RankThree.GroupTheory.SteinbergBYHighTwoRankCover
import CFSG.RankThree.OddKernel.ThreeComplementQuotient

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartOne
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

namespace Item48Proof

theorem le_of_large_prime_power_mem {G : Type*} [Group G] [Finite G] {K : Subgroup G}
    (hK : Group.IsPerfect K) {M : Subgroup G}
    (hM : ∀ y ∈ K, ∀ r : ℕ, r.Prime → 3 < r → (∃ k : ℕ, orderOf y = r ^ k) → y ∈ M) :
    K ≤ M := by
  classical
  have : Group.IsPerfect K := hK
  set N : Subgroup G :=
    Subgroup.closure {y : G | y ∈ K ∧ ∃ r : ℕ, r.Prime ∧ 3 < r ∧ ∃ k : ℕ, orderOf y = r ^ k}
    with hN
  have hNM : N ≤ M := (Subgroup.closure_le _).mpr fun y hy => by
    obtain ⟨hyK, r, hr, hr3, k, hk⟩ := hy
    exact hM y hyK r hr hr3 ⟨k, hk⟩
  have hconj : ∀ g ∈ K, ∀ n ∈ N, g * n * g⁻¹ ∈ N := by
    intro g hg n hn
    induction hn using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨hyK, r, hr, hr3, k, hk⟩ := hy
      refine Subgroup.subset_closure ⟨K.mul_mem (K.mul_mem hg hyK) (K.inv_mem hg), r, hr, hr3, k,
        ?_⟩
      rw [← hk]
      exact (SemiconjBy.orderOf_eq g (by simp [SemiconjBy, mul_assoc])).symm
    | one => simp [N.one_mem]
    | mul a b _ _ ha hb =>
      have e : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
      rw [e]
      exact N.mul_mem ha hb
    | inv a _ ha =>
      have e : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
      rw [e]
      exact N.inv_mem ha
  have hnormal : (N.subgroupOf K).Normal :=
    ⟨fun n hn g => Subgroup.mem_subgroupOf.mpr (hconj g g.2 n (Subgroup.mem_subgroupOf.mp hn))⟩
  have hsolv : Group.IsSolvable (K ⧸ N.subgroupOf K) := by
    refine SignalizerFunctor.Helpers.two_prime_order_solvable _ 2 3 Nat.prime_two Nat.prime_three
      fun r hr hdvd => ?_
    by_contra hne
    rw [not_or] at hne
    have hr3 : 3 < r := by
      have := hr.two_le
      omega
    have : Fact r.Prime := ⟨hr⟩
    obtain ⟨e, he⟩ := exists_prime_orderOf_dvd_card' r hdvd
    obtain ⟨y, hy, k, hk⟩ := S8.exists_lift_orderOf_pow hr (N.subgroupOf K) ⟨1, by rw [he, pow_one]⟩
    have hyN : y ∈ N.subgroupOf K :=
      Subgroup.mem_subgroupOf.mpr (Subgroup.subset_closure
        ⟨y.2, r, hr, hr3, k, (Subgroup.orderOf_coe y).trans hk⟩)
    have he1 : e = 1 := by
      rw [← hy]
      exact (QuotientGroup.eq_one_iff y).mpr hyN
    rw [he1, orderOf_one] at he
    exact hr.one_lt.ne he
  have hsub : Subsingleton (K ⧸ N.subgroupOf K) := by
    by_contra hns
    have : Nontrivial (K ⧸ N.subgroupOf K) := not_subsingleton_iff_nontrivial.mp hns
    exact Group.IsPerfect.not_isSolvable (K ⧸ N.subgroupOf K) hsolv
  intro y hy
  have h1 : ((⟨y, hy⟩ : K) : K ⧸ N.subgroupOf K) = 1 := Subsingleton.elim _ _
  exact hNM (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1))

end Item48Proof

theorem rank3II_4_8_of_schreier (hS : SchreierFor Assembly.InCatalog) (h45 : Item4_5) :
    Item4_8 := by
  intro G _ _ hG A hA hn x hxA _ Y hY
  obtain ⟨n, hn3, hcard⟩ := hn
  have hx3 : ∃ k : ℕ, orderOf x = 3 ^ k := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
      (by rw [pow_one]; exact orderOf_dvd_of_pow_eq_one (hA.2 x hxA) : orderOf x ∣ 3 ^ 1)
    exact ⟨j, hj⟩
  have hAp : IsPGroup 3 A := fun g =>
    ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]; exact hA.2 g g.2)⟩
  have hAL := h45 G hG A hAp (Or.inr ⟨hA, n, hn3, hcard⟩)
  have he : CFSG.twoLocalOddRank G ≤ 3 := by
    rw [GroupTheory.SteinbergBY.twoLocalOddRank_eq_evenRank]
    exact hG.evenRank_le
  have hq : ∀ r : ℕ, r.Prime → 3 < r → localRank r G ≤ 2 := fun r hr hr3 => by
    have := hG.localRank_lt r hr hr3
    omega
  obtain ⟨-, -, he', -⟩ :=
    OddKernel.rank_three_three_complement_quotient_sharp_local_bounds_theta he hq
  refine local_theta_component_quotient_normalization_embedding hS G hG.kGroup 3 Nat.prime_three
    x hx3 Y hY fun L hL => ⟨?_, ?_⟩
  · exact EmbeddingTransport.mk_mem_normalizer_of_mem_normalizer_thetaComponents
      Nat.prime_three (fun L' hL' => hAL L' hL' hxA) hL
  · rw [Subgroup.map_le_iff_le_comap]
    refine Item48Proof.le_of_large_prime_power_mem (isPerfect_of_mem_thetaComponentsAt hY) ?_
    rintro y - r hr hr3 ⟨k, hk⟩
    rw [Subgroup.mem_comap]
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hr).mp
      (hk ▸ orderOf_map_dvd (QuotientGroup.mk' (aschbacherSolvableCore 3 G)) y)
    exact GroupTheory.SteinbergBM.large_prime_elements_normalize_components he' hr hr3 ⟨j, hj⟩ hL

theorem rank3II_4_8_of
    (h45 : Item4_5) : Item4_8 :=
  rank3II_4_8_of_schreier TCB.schreierFor_inCatalog_holds h45

end CFSG.RankThree.PartTwo.Sec4
