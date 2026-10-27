module

public import CFSG.CharacterTheory.TwoRankLowerBound.CommutingInvolutions

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open

theorem s16c1_odd_orderOf_mul_of_twoRank {X : Type*} [Group X] [Finite X]
    (hX : CFSG.Open.twoRank X ≤ 1) {a b : X} (ha : a * a = 1) (hb : b * b = 1) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) : Odd (orderOf (a * b)) := by
  by_contra hodd
  have heven : Even (orderOf (a * b)) := Nat.not_odd_iff_even.1 hodd
  obtain ⟨k, hk⟩ := even_iff_exists_two_mul.mp heven
  have hpos : 0 < orderOf (a * b) := orderOf_pos _
  have hkpos : 0 < k := by omega
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hz2 : (a * b) ^ k * (a * b) ^ k = 1 := by
    rw [← pow_add, ← two_mul, ← hk, pow_orderOf_eq_one]
  have hzne : (a * b) ^ k ≠ 1 := pow_ne_one_of_lt_orderOf hkpos.ne' (by omega)
  have hzi : ((a * b) ^ k)⁻¹ = (a * b) ^ k := inv_eq_of_mul_eq_one_right hz2
  have hacb : a * (a * b) * a = (a * b)⁻¹ := by
    rw [mul_inv_rev, hai, hbi, ← mul_assoc, ha, one_mul]
  have hconj : a * (a * b) ^ k * a = ((a * b) ^ k)⁻¹ := by
    have h1 : (a * (a * b) * a⁻¹) ^ k = a * (a * b) ^ k * a⁻¹ := conj_pow
    rw [hai] at h1
    rw [← h1, hacb, inv_pow]
  have hacz : a * (a * b) ^ k = (a * b) ^ k * a := by
    have h2 : a * (a * b) ^ k * a = (a * b) ^ k := by rw [hconj, hzi]
    calc a * (a * b) ^ k = a * (a * b) ^ k * a * a := by rw [mul_assoc _ a a, ha, mul_one]
      _ = (a * b) ^ k * a := by rw [h2]
  have hane : a ≠ (a * b) ^ k := by
    intro h
    have key : (a * b) ^ k * (a * b) = (a * b) * (a * b) ^ k :=
      ((Commute.refl (a * b)).pow_left k).eq
    have hcomm : a * (a * b) = (a * b) * a :=
      calc a * (a * b) = (a * b) ^ k * (a * b) := congrArg (fun x => x * (a * b)) h
        _ = (a * b) * (a * b) ^ k := key
        _ = (a * b) * a := by rw [← h]
    have hba : b = a * b * a :=
      calc b = a * (a * b) := by rw [← mul_assoc, ha, one_mul]
        _ = a * b * a := hcomm
    have hab : a * b = b * a := by
      have h1 : b * a = a * b * a * a := congrArg (fun x => x * a) hba
      rw [h1, mul_assoc (a * b) a a, ha, mul_one]
    have hc2 : (a * b) * (a * b) = 1 := by
      calc (a * b) * (a * b) = a * (b * a) * b := by simp only [mul_assoc]
        _ = a * (a * b) * b := by rw [← hab]
        _ = (a * a) * (b * b) := by simp only [mul_assoc]
        _ = 1 := by rw [ha, hb, one_mul]
    have hdvd : orderOf (a * b) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hc2)
    have hk1 : k = 1 := by
      have := Nat.le_of_dvd (by norm_num) hdvd
      omega
    subst hk1
    rw [pow_one] at h
    have h3 : a * b = a * 1 := by rw [mul_one]; exact h.symm
    exact hb1 (mul_left_cancel h3)
  have hao : orderOf a = 2 := orderOf_eq_prime (by rw [pow_two]; exact ha) ha1
  have hzo : orderOf ((a * b) ^ k) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hz2) hzne
  have h2 := CFSG.TwoRankLowerBound.Helpers.two_le_twoRank_of_commuting_involutions X a
    ((a * b) ^ k) hao hzo hane hacz
  omega

section Quot

variable {G : Type} [Group G] [Finite G]

theorem s16c1_G47_order_data {L K : Subgroup G} [(K.subgroupOf L).Normal]
    (hr : CFSG.Open.twoRank (↥L ⧸ K.subgroupOf L) ≤ 1) {w w' : G} (hw : w ∈ L) (hw' : w' ∈ L)
    (hww : w * w = 1) (hw'w' : w' * w' = 1) (hwK : w ∉ K) (hw'K : w' ∉ K) :
    ∃ n : ℕ, Odd n ∧ ∀ j : ℕ, (w * w') ^ j ∈ K ↔ n ∣ j := by
  classical
  have hπ1 : ∀ x : ↥L, (QuotientGroup.mk' (K.subgroupOf L) x = 1 ↔ (x : G) ∈ K) := fun x => by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  set π := QuotientGroup.mk' (K.subgroupOf L) with hπ
  set a : ↥L := ⟨w, hw⟩ with ha
  set b : ↥L := ⟨w', hw'⟩ with hb
  have haa : a * a = 1 := Subtype.ext (by simpa [ha] using hww)
  have hbb : b * b = 1 := Subtype.ext (by simpa [hb] using hw'w')
  have hs : π a * π a = 1 := by rw [← map_mul, haa, map_one]
  have ht : π b * π b = 1 := by rw [← map_mul, hbb, map_one]
  have hs1 : π a ≠ 1 := fun h => hwK ((hπ1 a).1 h)
  have ht1 : π b ≠ 1 := fun h => hw'K ((hπ1 b).1 h)
  have hodd : Odd (orderOf (π a * π b)) := s16c1_odd_orderOf_mul_of_twoRank hr hs ht hs1 ht1
  refine ⟨orderOf (π a * π b), hodd, fun j => ?_⟩
  rw [orderOf_dvd_iff_pow_eq_one, ← map_mul, ← map_pow]
  have hmem : (w * w') ^ j ∈ L := L.pow_mem (L.mul_mem hw hw') j
  have hcoe : (((a * b) ^ j : ↥L) : G) = (w * w') ^ j := by simp [ha, hb]
  rw [hπ1 ((a * b) ^ j), hcoe]

end Quot

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
