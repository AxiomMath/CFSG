module

public import CFSG.Quasithin.EmptyFaithful.S1421QA24Sl2
public import CFSG.Foundations.Basic

public section

namespace CFSG.Quasithin.QA24

open scoped MatrixGroups

variable {L : Type*} [Group L]

theorem false_of_injOn_three {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (Φ : L →* SL(2, ZMod p))
    (hΦ : ∀ x : L, (∃ k : ℕ, x ^ 3 ^ k = 1) → Φ x = 1 → x = 1) {a b : L} (ha1 : a ≠ 1)
    (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1) (hab : a * b = b * a)
    (hb : b ∉ Subgroup.zpowers a) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have hb1 : b ≠ 1 := fun h => hb (h ▸ Subgroup.one_mem _)
  have hba : b ≠ a := fun h => hb (h ▸ Subgroup.mem_zpowers b)
  have hba2 : b ≠ a ^ 2 := fun h => hb (h ▸ (Subgroup.pow_mem _ (Subgroup.mem_zpowers a) 2))
  have hcomm : Commute a b := hab
  have h3a : (b * a⁻¹) ^ 3 = 1 := by
    rw [hcomm.symm.inv_right.mul_pow, hb3, inv_pow, ha3, inv_one, mul_one]
  have h3b : (b * a) ^ 3 = 1 := by
    rw [hcomm.symm.mul_pow, hb3, ha3, mul_one]
  have hΦa : Φ a ≠ 1 := fun h => ha1 (hΦ a ⟨1, by rw [pow_one, ha3]⟩ h)
  have hΦb : Φ b ≠ 1 := fun h => hb1 (hΦ b ⟨1, by rw [pow_one, hb3]⟩ h)
  have hΦba : Φ b ≠ Φ a := by
    intro h
    apply hba
    have h1 : Φ (b * a⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
    exact mul_inv_eq_one.mp (hΦ _ ⟨1, by rw [pow_one, h3a]⟩ h1)
  have hΦba2 : Φ b ≠ Φ a ^ 2 := by
    intro h
    apply hba2
    have h1 : Φ (b * a) = 1 := by
      rw [map_mul, h, ← pow_succ, ← map_pow, ha3, map_one]
    have h2 := hΦ _ ⟨1, by rw [pow_one, h3b]⟩ h1
    have h4 : a⁻¹ = a ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact ha3)
    rw [← h4]
    exact eq_inv_of_mul_eq_one_left h2
  have h3 : (3 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  have e1 : Φ a ^ 3 = 1 := by rw [← map_pow, ha3, map_one]
  have e2 : Φ b ^ 3 = 1 := by rw [← map_pow, hb3, map_one]
  have e3 : Φ a * Φ b = Φ b * Φ a := by rw [← map_mul, hab, map_mul]
  exact false_of_commuting_order_three h3 (Φ a) (Φ b) hΦa hΦb e1 e2 e3 hΦba hΦba2

variable [Finite L]

theorem pRank_three_le_one {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (Φ : L →* SL(2, ZMod p))
    (hΦ : ∀ x : L, (∃ k : ℕ, x ^ 3 ^ k = 1) → Φ x = 1 → x = 1) : CFSG.pRank 3 L ≤ 1 := by
  refine csSup_le' ?_
  rintro r ⟨A, hA, hcard⟩
  by_contra hr
  have hr2 : 2 ≤ r := by omega
  have h9 : 9 ≤ Nat.card A := by
    rw [hcard]
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ r := Nat.pow_le_pow_right (by norm_num) hr2
  have hnt : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨a, ha1⟩ := exists_ne (1 : A)
  have hA3 : ∀ x : A, x ^ 3 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 3 A)
  have hz : Nat.card (Subgroup.zpowers a) ≤ 3 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hA3 a))
  have hex : ∃ b : A, b ∉ Subgroup.zpowers a := by
    by_contra hall
    push Not at hall
    have htop : Subgroup.zpowers a = ⊤ := (Subgroup.eq_top_iff' _).mpr hall
    have : Nat.card (Subgroup.zpowers a) = Nat.card A := by rw [htop, Subgroup.card_top]
    omega
  obtain ⟨b, hb⟩ := hex
  have hcomm : (a : A) * b = b * a := hA.toIsMulCommutative.is_comm.comm a b
  refine false_of_injOn_three hp hp3 Φ hΦ (a := ((a : A) : L)) (b := ((b : A) : L))
    (fun h => ha1 (Subtype.ext h)) ?_ ?_ ?_ ?_
  · exact congrArg Subtype.val (hA3 a)
  · exact congrArg Subtype.val (hA3 b)
  · exact congrArg Subtype.val hcomm
  · intro hmem
    apply hb
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext (by simpa using hk)⟩

end CFSG.Quasithin.QA24
