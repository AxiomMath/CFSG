module

public import CFSG.Walter.J1.SylowOdd

public section

namespace CFSG.Walter.J1

namespace JankoHyp

variable {G : Type} [Group G] [Finite G] (h : JankoHyp G)

include h in
theorem card_centralizer_involution {u : G} (hu : orderOf u = 2) :
    Nat.card (Subgroup.centralizer ({u} : Set G)) = 120 := by
  obtain ⟨g, hg⟩ := h.exists_conj_t_eq hu
  rw [← hg]
  exact (h.conj g).card_centralizer

include h in
theorem orderOf_dvd_of_commute_involution {u x : G} (hu : orderOf u = 2) (hxu : x * u = u * x) :
    orderOf x ∣ 120 := by
  have hx : x ∈ Subgroup.centralizer ({u} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hxu
  rw [← h.card_centralizer_involution hu, ← Subgroup.orderOf_mk x hx]
  exact orderOf_dvd_natCard _

include h in
theorem card_centralizer_odd {p : ℕ} (hp : p = 3 ∨ p = 5) {X : Subgroup G}
    (hX : Nat.card X = p) :
    Nat.card (Subgroup.centralizer (X : Set G)) = 2 * p ∨
      Nat.card (Subgroup.centralizer (X : Set G)) = 30 := by
  obtain ⟨x, hx, hXx⟩ := h.exists_involution_of_card hp hX
  obtain ⟨-, A, -, -, -, -, -, -, hA2, -, -, hAcard⟩ := h.bender_4_1_of_centralizer hp hX hx hXx
  rcases hAcard with h0 | h0
  · left; rw [← hA2, h0, mul_comm]
  · right; rw [← hA2, h0]

include h in
theorem orderOf_dvd_of_commute_odd {p : ℕ} (hp : p = 3 ∨ p = 5) {x y : G} (hx : orderOf x = p)
    (hxy : y * x = x * y) : orderOf y ∣ 30 := by
  set X := Subgroup.zpowers x
  have hX : Nat.card X = p := by rw [Nat.card_zpowers, hx]
  have hy : y ∈ Subgroup.centralizer (X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨k, rfl⟩
    exact (Commute.zpow_left (Commute.symm hxy) k).eq
  have hdvd : orderOf y ∣ Nat.card (Subgroup.centralizer (X : Set G)) := by
    rw [← Subgroup.orderOf_mk y hy]
    exact orderOf_dvd_natCard _
  rcases h.card_centralizer_odd hp hX with h0 | h0 <;> rw [h0] at hdvd
  · rcases hp with rfl | rfl
    · exact hdvd.trans (by norm_num)
    · exact hdvd.trans (by norm_num)
  · exact hdvd

include h in
theorem eq_one_of_coprime_of_commute {x y : G} (hy : Nat.Coprime (orderOf y) 30)
    (hx : orderOf x = 2 ∨ orderOf x = 3 ∨ orderOf x = 5) (hxy : y * x = x * y) : y = 1 := by
  rw [← orderOf_eq_one_iff]
  have h120 : Nat.Coprime (orderOf y) 120 := by
    have : (120 : ℕ) = 30 * 4 := by norm_num
    rw [this]
    refine Nat.Coprime.mul_right hy ?_
    exact Nat.Coprime.coprime_dvd_right (by norm_num : 4 ∣ 30 * 2) (Nat.Coprime.mul_right hy
      (Nat.Coprime.coprime_dvd_right (by norm_num : 2 ∣ 30) hy))
  rcases hx with hx | hx | hx
  · exact Nat.Coprime.eq_one_of_dvd h120 (h.orderOf_dvd_of_commute_involution hx hxy)
  · exact Nat.Coprime.eq_one_of_dvd hy (h.orderOf_dvd_of_commute_odd (Or.inl rfl) hx hxy)
  · exact Nat.Coprime.eq_one_of_dvd hy (h.orderOf_dvd_of_commute_odd (Or.inr rfl) hx hxy)

end JankoHyp

end CFSG.Walter.J1
