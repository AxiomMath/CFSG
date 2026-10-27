module

public import CFSG.Quasithin.Background.B4L3FactA
public import Certificates.Data.CFSGNative.H13.J4Chain

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative

theorem four_le_card_of_three {W : Type*} [Group W] [Finite W] (hcard : Nat.card W = 8)
    {S : Subgroup W} {a b : W} (ha : a ∈ S) (hb : b ∈ S) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hab : a ≠ b) : 4 ≤ Nat.card S := by
  have h3 : 3 ≤ Nat.card S := by
    rw [show Nat.card S = (S : Set W).ncard from Nat.card_coe_set_eq (S : Set W)]
    have hsub : ({1, a, b} : Set W) ⊆ (S : Set W) := by
      intro y hy
      rcases hy with rfl | rfl | rfl
      · exact S.one_mem
      · exact ha
      · exact hb
    have h1 : ({1, a, b} : Set W).ncard = 3 := by
      rw [Set.ncard_insert_of_notMem, Set.ncard_pair hab]
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨ha1.symm, hb1.symm⟩
    rw [← h1]
    exact Set.ncard_le_ncard hsub (Set.toFinite _)
  have hdvd : Nat.card S ∣ 8 := hcard ▸ Subgroup.card_subgroup_dvd_card S
  have : Nat.card S ≠ 3 := fun h => by rw [h] at hdvd; norm_num at hdvd
  rcases Nat.lt_or_ge (Nat.card S) 4 with hlt | hge
  · omega
  · exact hge

theorem eq_one_of_odd_of_fix {W : Type*} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    (hcard : Nat.card W = 8) {c : MulAut W} (hodd : Odd (orderOf c)) {a b : W} (ha : c a = a)
    (hb : c b = b) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) : c = 1 := by
  have hF := four_le_card_of_three hcard ((mem_fixV_zpowers_iff).mpr ha)
    ((mem_fixV_zpowers_iff).mpr hb) ha1 hb1 hab
  have h1 := card_commV_mul_card_fixV hW c
  have hC2 : Nat.card (commV (Subgroup.zpowers c)) ≤ 2 := by
    by_contra hlt
    push Not at hlt
    have : 3 * 4 ≤ Nat.card (commV (Subgroup.zpowers c)) * Nat.card (fixV (Subgroup.zpowers c)) :=
      Nat.mul_le_mul hlt hF
    omega
  have hfix : ∀ y ∈ commV (Subgroup.zpowers c), c y = y := by
    intro y hy
    by_contra hne
    have hcy := commV_invariant _ c (Subgroup.mem_zpowers c) y hy
    have hy1 : y ≠ 1 := by
      rintro rfl
      exact hne (map_one c)
    have hcy1 : c y ≠ 1 := fun h1 => hy1 (by
      rw [← map_one c] at h1
      exact c.injective h1)
    have := four_le_card_of_three hcard hy hcy hy1 hcy1 (Ne.symm hne)
    omega
  have hc2 : c ^ 2 = 1 := by
    ext w
    have hy : c w * w⁻¹ ∈ commV (Subgroup.zpowers c) := by
      rw [commV_zpowers_eq_map]
      exact ⟨w, trivial, rfl⟩
    have h2 := hfix _ hy
    rw [map_mul, map_inv] at h2
    have hw : w⁻¹ = w := inv_eq_self_of_sq hW w
    rw [hw] at h2
    show c (c w) = w
    calc c (c w) = c (c w) * (c w)⁻¹ * c w := by group
      _ = c w * w * c w := by rw [h2]
      _ = w * (c w * c w) := by rw [mul_comm (c w) w, mul_assoc]
      _ = w := by rw [← pow_two, hW, mul_one]
  have hdvd : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one hc2
  have h3 : orderOf c ∣ Nat.gcd (orderOf c) 2 := Nat.dvd_gcd dvd_rfl hdvd
  rw [Nat.Coprime.gcd_eq_one ((Nat.coprime_two_right).mpr hodd)] at h3
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

end CFSG.Quasithin.Vol2.Ch10.SecD
