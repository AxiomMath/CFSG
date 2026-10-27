module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P3Lines2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace E9P2.Lines

variable {Y : Type*} [Group Y] [Finite Y]

theorem odd_order_eq_one {K T0 T N : Subgroup Y} (h9 : Nat.card K = 9)
    (hexp : ∀ k ∈ K, k ^ 3 = 1) (hcomm : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a)
    (hKN : N ≤ Subgroup.normalizer (K : Set Y)) (hT : IsSylowTwoOf T N) {σ : Y} (hσ : σ ∈ T)
    (hσ2 : ∀ k ∈ K, σ ^ 2 * k * σ⁻¹ ^ 2 = k⁻¹)
    (hTK : ∀ t ∈ T, ∃ i : ℕ, ∀ k ∈ K, t * k * t⁻¹ = σ ^ i * k * σ⁻¹ ^ i)
    (hT0N : N ≤ Subgroup.normalizer (T0 : Set Y)) (hT0T : T0 ≤ T) {t0 : Y} (ht0 : t0 ∈ T0)
    (ht0inv : ∀ k ∈ K, t0 * k * t0⁻¹ = k⁻¹)
    (hr : ∀ r : ℕ, r.Prime → r ∣ Nat.card Y → r = 2 ∨ r = 3)
    (h3 : ∀ E : Subgroup Y, IsElemAbelian 3 E → Nat.card E ≤ 9) :
    ∀ x ∈ N, ¬ 2 ∣ orderOf x → x = 1 := by
  intro x hxN hx
  by_contra hx1
  have hcent := odd_order_centralizes_of_lines h9 hexp hKN hT hσ hσ2 hTK
  have hord : orderOf x ≠ 1 := fun h => hx1 (orderOf_eq_one_iff.mp h)
  obtain ⟨r, hrp, hrd⟩ := Nat.exists_prime_and_dvd hord
  have hr3 : r = 3 := by
    rcases hr r hrp (hrd.trans (orderOf_dvd_natCard x)) with h | h
    · exact absurd (h ▸ hrd) hx
    · exact h
  subst hr3
  have hy3 : orderOf (x ^ (orderOf x / 3)) = 3 := orderOf_pow_orderOf_div (orderOf_pos x).ne' hrd
  have hyN : x ^ (orderOf x / 3) ∈ N := N.pow_mem hxN _
  generalize x ^ (orderOf x / 3) = y at hy3 hyN
  have hy3' : y ^ 3 = 1 := hy3 ▸ pow_orderOf_eq_one y
  have hy1 : y ≠ 1 := fun h => by rw [h, orderOf_one] at hy3; omega
  have hycent : ∀ k ∈ K, y * k * y⁻¹ = k := hcent y hyN (by rw [hy3]; omega)
  by_cases hyK : y ∈ K
  ·
    have hconj : y * t0 * y⁻¹ ∈ T0 := (Subgroup.mem_normalizer_iff.mp (hT0N hyN) t0).mp ht0
    have hmem : y * t0 * y⁻¹ * t0⁻¹ ∈ T0 := T0.mul_mem hconj (T0.inv_mem ht0)
    have h1 : t0 * y⁻¹ * t0⁻¹ = y := by
      calc t0 * y⁻¹ * t0⁻¹ = (t0 * y * t0⁻¹)⁻¹ := by group
        _ = y := by rw [ht0inv y hyK, inv_inv]
    have hzeq : y * t0 * y⁻¹ * t0⁻¹ = y * y := by
      calc y * t0 * y⁻¹ * t0⁻¹ = y * (t0 * y⁻¹ * t0⁻¹) := by simp only [mul_assoc]
        _ = y * y := by rw [h1]
    rw [hzeq] at hmem
    obtain ⟨k, hk⟩ := hT.2.1 ⟨y * y, hT0T hmem⟩
    have hk' : (y * y) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hz3 : (y * y) ^ 3 = 1 := by
      calc (y * y) ^ 3 = (y ^ 3) ^ 2 := by rw [← pow_two, ← pow_mul, ← pow_mul, mul_comm]
        _ = 1 := by rw [hy3', one_pow]
    have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
    have hz1 : y * y = 1 := by
      simpa [hcop.gcd_eq_one] using pow_gcd_eq_one.mpr ⟨hk', hz3⟩
    exact hy1 (eq_one_of_eq_inv hy3' (mul_eq_one_iff_eq_inv.mp hz1))
  ·
    let E : Subgroup Y := Subgroup.closure ((K : Set Y) ∪ {y})
    have hEc : IsMulCommutative E := Subgroup.isMulCommutative_closure (by
      intro u hu v hv _
      rcases hu with hu | hu <;> rcases hv with hv | hv
      · exact hcomm u hu v hv
      · rw [Set.mem_singleton_iff.mp hv]
        have := hycent u hu
        exact (mul_inv_eq_iff_eq_mul.mp this).symm
      · rw [Set.mem_singleton_iff.mp hu]
        have := hycent v hv
        exact mul_inv_eq_iff_eq_mul.mp this
      · rw [Set.mem_singleton_iff.mp hu, Set.mem_singleton_iff.mp hv])
    have hE3 : ∀ u ∈ E, u ^ 3 = 1 := by
      intro u hu
      induction hu using Subgroup.closure_induction with
      | mem u hu =>
        rcases hu with hu | hu
        · exact hexp u hu
        · rw [Set.mem_singleton_iff.mp hu]
          exact hy3'
      | one => simp
      | mul u v hu hv ihu ihv =>
        have huv : Commute u v := setLike_mul_comm (s := E) hu hv
        rw [huv.mul_pow, ihu, ihv, one_mul]
      | inv u hu ihu => rw [inv_pow, ihu, inv_one]
    have hEel : IsElemAbelian 3 E := F7.isElemAbelian_iff.mpr
      ⟨fun u hu v hv => setLike_mul_comm (s := E) hu hv, hE3⟩
    have hKE : K ≤ E := fun k hk => Subgroup.subset_closure (Or.inl hk)
    have hyE : y ∈ E := Subgroup.subset_closure (Or.inr rfl)
    exact hyK ((Subgroup.eq_of_le_of_card_ge hKE (by rw [h9]; exact h3 E hEel)) ▸ hyE)

end E9P2.Lines

end CFSG.Quasithin
