module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartTwo.Sec12.Item123

public section

namespace CFSG.RankThree.PartTwo.KFacts

variable {G : Type*} [Group G]

theorem conj_pow_eq_mul_pow {c d x : G} (hx : x * c * x⁻¹ = c * d) (hxd : x * d = d * x)
    (k : ℕ) : x ^ k * c * (x ^ k)⁻¹ = c * d ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hxd' : Commute x d := hxd
    have e1 : x ^ (k + 1) * c * (x ^ (k + 1))⁻¹ = x * (x ^ k * c * (x ^ k)⁻¹) * x⁻¹ := by
      rw [pow_succ', mul_inv_rev]
      group
    rw [e1, ih]
    have e2 : x * (c * d ^ k) * x⁻¹ = (x * c * x⁻¹) * (x * d ^ k * x⁻¹) := by group
    rw [e2, hx, (hxd'.pow_right k).eq, mul_inv_cancel_right, mul_assoc, ← pow_succ']

theorem zpowers_sq_eq {f : G} (hf : f ^ 3 = 1) : Subgroup.zpowers (f ^ 2) = Subgroup.zpowers f := by
  apply le_antisymm
  · exact Subgroup.zpowers_le.mpr ((Subgroup.zpowers f).pow_mem (Subgroup.mem_zpowers f) 2)
  · rw [Subgroup.zpowers_le]
    have h : (f ^ 2) ^ 2 = f := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_add, hf, one_mul, pow_one]
    have h2 : (f ^ 2) ^ 2 ∈ Subgroup.zpowers (f ^ 2) :=
      (Subgroup.zpowers (f ^ 2)).pow_mem (Subgroup.mem_zpowers _) 2
    rwa [h] at h2

theorem exists_pow_mul_pow_of_mem_closure_pair {c d z : G} (hcd : c * d = d * c)
    (hc3 : c ^ 3 = 1) (hd3 : d ^ 3 = 1) (hz : z ∈ Subgroup.closure ({c, d} : Set G)) :
    ∃ i j : ℕ, i < 3 ∧ j < 3 ∧ z = c ^ i * d ^ j := by
  obtain ⟨i, j, rfl⟩ := Sec12.exists_zpow_mul_zpow_of_mem_closure_pair hcd hz
  have hc3' : c ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, hc3]
  have hd3' : d ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, hd3]
  have hi0 : 0 ≤ i % 3 := Int.emod_nonneg _ (by norm_num)
  have hj0 : 0 ≤ j % 3 := Int.emod_nonneg _ (by norm_num)
  refine ⟨(i % 3).toNat, (j % 3).toNat, by omega, by omega, ?_⟩
  rw [zpow_eq_zpow_emod i hc3', zpow_eq_zpow_emod j hd3', ← zpow_natCast, ← zpow_natCast,
    Int.toNat_of_nonneg hi0, Int.toNat_of_nonneg hj0]

theorem eq_zpowers_mul_pow_of_card_three [Finite G] {c d : G} (hcd : c * d = d * c)
    (hc3 : c ^ 3 = 1) (hd3 : d ^ 3 = 1) {F : Subgroup G}
    (hF : F ≤ Subgroup.closure {c, d}) (h3 : Nat.card F = 3) (hFd : F ≠ Subgroup.zpowers d) :
    ∃ k : ℕ, k < 3 ∧ F = Subgroup.zpowers (c * d ^ k) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Nontrivial F := Finite.one_lt_card_iff_nontrivial.mp (by rw [h3]; norm_num)
  obtain ⟨⟨f, hfF⟩, hf1⟩ := exists_ne (1 : F)
  have hf1' : f ≠ 1 := fun h => hf1 (Subtype.ext h)
  have hFf : F = Subgroup.zpowers f := by
    have hle : Subgroup.zpowers f ≤ F := Subgroup.zpowers_le.mpr hfF
    have hcard : Nat.card (Subgroup.zpowers f) = 3 := by
      rw [Nat.card_zpowers]
      have h := orderOf_dvd_natCard (⟨f, hfF⟩ : F)
      rw [h3, Nat.dvd_prime Nat.prime_three, Subgroup.orderOf_mk] at h
      rcases h with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hf1'
      · exact h
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h3, hcard])).symm
  have hcd' : Commute c d := hcd
  obtain ⟨i, j, hi, hj, rfl⟩ := exists_pow_mul_pow_of_mem_closure_pair hcd hc3 hd3 (hF hfF)
  have hf3 : (c ^ i * d ^ j) ^ 3 = 1 := by
    rw [(hcd'.pow_pow i j).mul_pow, ← pow_mul, ← pow_mul, mul_comm i, mul_comm j, pow_mul,
      pow_mul, hc3, hd3, one_pow, one_pow, one_mul]
  have hsq : (c ^ 2 * d ^ j) ^ 2 = c ^ 4 * d ^ (2 * j) := by
    rw [(hcd'.pow_pow 2 j).mul_pow, ← pow_mul, ← pow_mul, mul_comm j]
  have hc4 : c ^ 4 = c := by rw [show 4 = 3 + 1 from rfl, pow_add, hc3, one_mul, pow_one]
  have hd4 : d ^ 4 = d := by rw [show 4 = 3 + 1 from rfl, pow_add, hd3, one_mul, pow_one]
  interval_cases i <;> interval_cases j
  · exact absurd (by simp) hf1'
  · exact absurd (by simpa using hFf) hFd
  · exact absurd (by rw [hFf, pow_zero, one_mul, zpowers_sq_eq hd3]) hFd
  · exact ⟨0, by norm_num, by simpa using hFf⟩
  · exact ⟨1, by norm_num, by simpa using hFf⟩
  · exact ⟨2, by norm_num, by simpa using hFf⟩
  · refine ⟨0, by norm_num, ?_⟩
    rw [hFf, ← zpowers_sq_eq hf3, hsq, hc4]
  · refine ⟨2, by norm_num, ?_⟩
    rw [hFf, ← zpowers_sq_eq hf3, hsq, hc4]
  · refine ⟨1, by norm_num, ?_⟩
    rw [hFf, ← zpowers_sq_eq hf3, hsq, hc4, show 2 * 2 = 4 from rfl, hd4, pow_one]

theorem exists_conj_eq_of_conj_eq_mul [Finite G] {c d x : G} {X : Subgroup G} (hxX : x ∈ X)
    (hcd : c * d = d * c) (hc3 : c ^ 3 = 1) (hd3 : d ^ 3 = 1) (hx : x * c * x⁻¹ = c * d)
    (hxd : x * d = d * x) :
    ∀ F : Subgroup G, F ≤ Subgroup.closure {c, d} → Nat.card F = 3 →
      F ≠ Subgroup.zpowers d →
        ∃ y ∈ X, F = (Subgroup.zpowers c).map (MulAut.conj y).toMonoidHom := by
  intro F hF h3 hFd
  obtain ⟨k, -, rfl⟩ := eq_zpowers_mul_pow_of_card_three hcd hc3 hd3 hF h3 hFd
  refine ⟨x ^ k, Subgroup.pow_mem _ hxX k, ?_⟩
  rw [MonoidHom.map_zpowers]
  congr 1
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact (conj_pow_eq_mul_pow hx hxd k).symm

end CFSG.RankThree.PartTwo.KFacts
