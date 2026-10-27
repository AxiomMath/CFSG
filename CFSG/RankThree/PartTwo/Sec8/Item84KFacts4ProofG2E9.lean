module

public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts3ProofPairRee
import CFSG.RankThree.PartTwo.Sec8.Item84KFacts4ProofG2

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item84KFacts4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem three_dvd_card_sq_sub_one {K : Type} [Field K] [Finite K] (hK2 : ringChar K = 2) :
    3 ∣ Nat.card K ^ 2 - 1 := by
  have : CharP K 2 := ringChar.of_eq hK2
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  rw [Nat.card_eq_fintype_card, hn, ← pow_mul, mul_comm, pow_mul]
  simpa using Nat.sub_dvd_pow_sub_pow 4 1 n


theorem kF84G2E9_holds : Item8KFacts3.KF84G2E9 := by
  intro K _ _ hK2 _ u v hu3 hv3 huv hu1 hvu
  obtain ⟨K₂, _, _, _, -, hdeg, -⟩ := Sec11.KS11Lie4Proof.exists_quadratic_ext' K
  have h31 : 3 ∣ Nat.card K₂ - 1 := by
    rw [Sec11.KS11Lie4Proof.natCard_quadratic hdeg]
    exact three_dvd_card_sq_sub_one hK2
  set ι := Sec11.KS11Lie4Proof.bcG2 K K₂ with hιdef
  have hι : Function.Injective ι := Sec11.KS11Lie4Proof.bcG2_injective
  have hu3' : ι u ^ 3 = 1 := by rw [← map_pow, hu3, map_one]
  have hv3' : ι v ^ 3 = 1 := by rw [← map_pow, hv3, map_one]
  have huv' : ι u * ι v = ι v * ι u := by rw [← map_mul, huv, map_mul]
  have hu1' : ι u ≠ 1 := fun h => hu1 (hι (h.trans (map_one ι).symm))
  have hvu' : ι v ∉ Subgroup.zpowers (ι u) := by
    rintro hk
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hk
    apply hvu
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, hι (by rw [map_zpow]; exact hk)⟩
  have hv1 : v ≠ 1 := fun h => hvu (h ▸ Subgroup.one_mem _)
  obtain ⟨z', hz', g, hg⟩ := exists_mem_pair_conj_long h31 hu3' hv3' huv' hu1' hvu'
  obtain ⟨z, hz, hz3, hz1, rfl⟩ : ∃ z, z ∈ ({u, v} : Set (adjointGroup .G2 K)) ∧ z ^ 3 = 1 ∧
      z ≠ 1 ∧ ι z = z' := by
    rcases hz' with rfl | rfl
    · exact ⟨u, by simp, hu3, hu1, rfl⟩
    · exact ⟨v, by simp, hv3, hv1, rfl⟩
  refine ⟨z, Subgroup.subset_closure hz, hz1, fun h hh => ?_⟩
  have hh' := Sec11.KS11Lie4Proof.bcG2_mem_g2ShortSL2 (K₂ := K₂) hh
  rw [map_mul, map_mul, map_inv] at hh'
  exact false_of_conj_long_short h31 (by rw [← map_pow, hz3, map_one])
    (fun h1 => hz1 (hι (h1.trans (map_one ι).symm))) hg hh'

end CFSG.RankThree.PartTwo.Sec8.Item84KFacts4
