module


import CFSG.Adapters.StatedPSLTwo
import CFSG.GroupTheory.CommutingConjugatePair
import CFSG.GroupTheory.PGroup.RankTwoCommute
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFactsThreeDvd
import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2TypeDet
import CFSG.LocalAnalysis.UniquenessCase.UC6ProjFive
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.R8106K

open CFSG.Open Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {Y : Type} [Group Y] [Finite Y]

theorem not_dvd_card_center_of_isStronglyPEmbedded {p : ℕ} {H : Subgroup Y}
    (hH : IsStronglyPEmbedded p H) (hZH : center Y ≤ H) : ¬ p ∣ Nat.card (center Y) := by
  obtain ⟨g, hg⟩ := SetLike.exists_not_mem_of_ne_top H hH.1 rfl
  have hle : center Y ≤ H ⊓ H.map (MulAut.conj g).toMonoidHom := by
    refine le_inf hZH fun z hz => ?_
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    have hcomm := Subgroup.mem_center_iff.mp hz g
    rw [mul_assoc, ← hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
    exact hZH hz
  exact fun hp => hH.2.2 g hg (hp.trans (Subgroup.card_dvd_of_le hle))

theorem inf_center_eq_bot_of_isL2 {K : Subgroup Y} {m : ℕ} (hL2 : IsL2 (Bar2 K) m)
    (hZ : Odd (Nat.card (center Y))) : K ⊓ center Y = ⊥ := by
  haveI : IsSimpleGroup (Bar2 K) := CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hL2
  let π : ↥K →* Bar2 K := QuotientGroup.mk' (CFSG.pCore 2 ↥K)
  let C : Subgroup ↥K := (center Y).subgroupOf K
  have hCcenter : C ≤ Subgroup.center ↥K := by
    intro c hc
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (Subgroup.mem_subgroupOf.mp hc) (x : Y)
  have hCodd : Odd (Nat.card C) := by
    rw [← Subgroup.card_map_of_injective (K := C) K.subtype_injective]
    refine hZ.of_dvd_nat (Subgroup.card_dvd_of_le ?_)
    intro y hy
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hy
    exact Subgroup.mem_subgroupOf.mp hc
  have hCnormal : (C.map π).Normal := by
    refine Subgroup.normal_of_le_center ?_
    intro y hy
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hy
    rw [Subgroup.mem_center_iff]
    intro x
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K) x
    rw [← map_mul, ← map_mul]
    exact congrArg π (Subgroup.mem_center_iff.mp (hCcenter hc) k)
  haveI := hCnormal
  rcases Subgroup.Normal.eq_bot_or_eq_top (C.map π) with hbot | htop
  · have hCker : C ≤ CFSG.pCore 2 ↥K := by
      intro c hc
      have hmem : π c ∈ C.map π := Subgroup.mem_map_of_mem π hc
      rw [hbot] at hmem
      have h1 : π c = 1 := by simpa using hmem
      have h2 : c ∈ π.ker := MonoidHom.mem_ker.mpr h1
      rwa [QuotientGroup.ker_mk'] at h2
    have hCbot : C = ⊥ := by
      have h := CFSG.GroupTheory.inf_eq_bot_of_isPGroup_two_of_odd (H := CFSG.pCore 2 ↥K)
        (K := C) (CFSG.pCore_isPGroup (p := 2) (G := ↥K)) hCodd
      rwa [inf_eq_right.mpr hCker] at h
    have hdisj : Disjoint (center Y) K := Subgroup.subgroupOf_eq_bot.mp hCbot
    rw [inf_comm]
    exact disjoint_iff.mp hdisj
  · have hoddBar : Odd (Nat.card (Bar2 K)) := by
      have h := hCodd.of_dvd_nat (Subgroup.card_map_dvd C π)
      rwa [htop, Subgroup.card_top] at h
    have hm : 1 ≤ m := hL2.admissible.2.1
    have hevenBar : Even (Nat.card (Bar2 K)) := by
      rw [CFSG.SeitzReduction.RankOne.card_of_lieModel_PSL_two_two hL2,
        CFSG.RankThree.PartOne.S12K.ordA_one_eq hm]
      exact even_iff_two_dvd.mpr (dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) _)
    exact absurd hevenBar (Nat.not_even_iff_odd.mpr hoddBar)

theorem three_dvd_card_of_isL2_bar2 {K : Subgroup Y} {m : ℕ} (hL2 : IsL2 (Bar2 K) m) :
    3 ∣ Nat.card K := by
  have h3bar : 3 ∣ Nat.card (Bar2 K) := by
    rw [CFSG.SeitzReduction.RankOne.card_of_lieModel_PSL_two_two hL2]
    exact CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.three_dvd_ordA (k := 1) (by norm_num)
  exact h3bar.trans (Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥K))

theorem exists_card_eq_of_isL2 {K : Subgroup Y} {n p : ℕ} (hp : p.Prime) (hpn : p ∣ 2 ^ n + 1)
    (hL2 : IsL2 (Bar2 K) (2 * n)) : ∃ D₀ : Subgroup Y, D₀ ≤ K ∧ Nat.card D₀ = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hm : 1 ≤ 2 * n := hL2.admissible.2.1
  have hdvd : p ∣ (2 ^ (2 * n)) ^ 2 - 1 := by
    have h1 := CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.succ_dvd_sq_sub_one (2 ^ n)
    have hsq : (2 ^ n) ^ 2 = 2 ^ (2 * n) := by rw [← pow_mul, Nat.mul_comm]
    have h2 : 2 ^ n + 1 ∣ 2 ^ (2 * n) - 1 := hsq ▸ h1
    have h3 : 2 ^ (2 * n) - 1 ∣ (2 ^ (2 * n)) ^ 2 - 1 :=
      CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.pred_dvd_sq_sub_one (2 ^ (2 * n))
    exact hpn.trans (h2.trans h3)
  have hpbar : p ∣ Nat.card (Bar2 K) := by
    rw [CFSG.SeitzReduction.RankOne.card_of_lieModel_PSL_two_two hL2,
      CFSG.RankThree.PartOne.S12K.ordA_one_eq hm]
    obtain ⟨d, hd⟩ := hdvd
    exact ⟨2 ^ (2 * n) * d, by rw [hd]; ring⟩
  have hpK : p ∣ Nat.card K :=
    hpbar.trans (Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥K))
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := K) p hpK
  refine ⟨(Subgroup.zpowers x).map K.subtype, Subgroup.map_subtype_le _, ?_⟩
  rw [Subgroup.card_map_of_injective K.subtype_injective, Nat.card_zpowers, hx]

theorem not_three_dvd_card_center {K : Subgroup Y} (hKZ : K ⊓ center Y = ⊥)
    (h3 : 3 ∣ Nat.card K) (hY3 : Open.pRank 3 (⊤ : Subgroup Y) ≤ 1) :
    ¬ 3 ∣ Nat.card (center Y) := by
  intro h3Z
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨z, hzord⟩ := exists_prime_orderOf_dvd_card' (G := center Y) 3 h3Z
  obtain ⟨k, hkord⟩ := exists_prime_orderOf_dvd_card' (G := K) 3 h3
  have hzZ : (z : Y) ∈ center Y := z.2
  have hzord' : orderOf (z : Y) = 3 := by rwa [Subgroup.orderOf_coe]
  have hkord' : orderOf (k : Y) = 3 := by rwa [Subgroup.orderOf_coe]
  have hcomm : Commute (z : Y) (k : Y) :=
    (Subgroup.mem_center_iff.mp hzZ (k : Y)).symm
  have hnotmem : (k : Y) ∉ Subgroup.zpowers (z : Y) := by
    intro hk
    have hkZ : (k : Y) ∈ center Y := Subgroup.zpowers_le.mpr hzZ hk
    have hkbot : (k : Y) ∈ K ⊓ center Y := ⟨k.2, hkZ⟩
    rw [hKZ] at hkbot
    have hk1 : (k : Y) = 1 := by simpa using hkbot
    have h1 : orderOf (k : Y) = 1 := by rw [hk1]; simp
    omega
  have h2 := CFSG.GroupTheory.two_le_pRank_of_commute (H := ⊤) (p := 3)
    (x := (z : Y)) (y := (k : Y)) trivial trivial hzord' hkord' hcomm hnotmem
  omega

theorem closure_pow_three_eq_top (hYq : CFSG.Open.IsQuasisimple Y)
    (h3Z : ¬ 3 ∣ Nat.card (center Y)) (h3 : 3 ∣ Nat.card Y) :
    Subgroup.closure {x : Y | x ^ 3 = 1} = ⊤ := by
  let S : Set Y := {x : Y | x ^ 3 = 1}
  let N : Subgroup Y := Subgroup.closure S
  have hconj : ∀ (g x : Y), x ∈ S → g * x * g⁻¹ ∈ S := by
    intro g x hx
    simp only [S, Set.mem_setOf_eq] at hx ⊢
    rw [show (g * x * g⁻¹) ^ 3 = g * x ^ 3 * g⁻¹ by
      simpa [MulAut.conj_apply] using (map_pow (MulAut.conj g) x 3).symm, hx]
    simp
  have hNnormal : N.Normal := by
    refine Subgroup.Normal.mk fun n hn g => ?_
    change n ∈ Subgroup.closure S at hn
    induction hn using Subgroup.closure_induction with
    | mem x hx => exact Subgroup.subset_closure (hconj g x hx)
    | one => simp
    | mul x y hx hy ihx ihy =>
        rw [show g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) by
          simpa [MulAut.conj_apply] using (map_mul (MulAut.conj g) x y).symm]
        exact mul_mem ihx ihy
    | inv x hx ih =>
        rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ by
          simpa [MulAut.conj_apply, mul_assoc] using (map_inv (MulAut.conj g) x).symm]
        exact inv_mem ih
  rcases CFSG.LocalAnalysis.UniquenessCase.UC6.ProjFive.normal_eq_top_or_le_center hYq hNnormal
    with htop | hle
  · simpa [S, N] using htop
  · exfalso
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' (G := Y) 3 h3
    have hxS : x ∈ S := by
      simp only [S, Set.mem_setOf_eq]
      rw [← hxord]
      exact pow_orderOf_eq_one x
    have hxN : x ∈ N := Subgroup.subset_closure hxS
    have hxZ : x ∈ center Y := hle hxN
    exact h3Z (hxord ▸ Subgroup.orderOf_dvd_natCard (center Y) hxZ)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.R8106K
