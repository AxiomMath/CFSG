module

public import CFSG.RankThree.GF2n.Stroth80.Sec84CaseOnePrep

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75
open scoped commutatorElement

theorem not_central_of_irred {G : Type} [Group G] [Finite G] {R N Z0 : Subgroup G}
    (hirr : IsIrredModule R N Z0) (hNR : N ≤ R) (hZR : ∀ r ∈ R, conjSubgroup r Z0 = Z0)
    (hbig : 2 * Nat.card ↥Z0 < Nat.card ↥N) :
    ¬ ∀ r ∈ R, ∀ n ∈ N, ⁅n, r⁆ ∈ Z0 := by
  intro hall
  obtain ⟨-, hsq, hlt, hmin⟩ := hirr
  obtain ⟨n, hnN, hnZ⟩ := SetLike.exists_of_lt hlt
  have hZN : Z0 ≤ N := hlt.le
  have hAN : Z0 ⊔ Subgroup.zpowers n ≤ N := sup_le hZN (Subgroup.zpowers_le.mpr hnN)
  have hnorm : n ∈ Subgroup.normalizer (Z0 : Set G) :=
    (CFSG.RankThree.GF2n.conjSubgroup_eq_self_iff).mp (hZR n (hNR hnN))
  have hinv : ∀ r ∈ R, conjSubgroup r (Z0 ⊔ Subgroup.zpowers n) = Z0 ⊔ Subgroup.zpowers n := by
    intro r hr
    have hcomm : r * n * r⁻¹ = (⁅n, r⁆)⁻¹ * n := by
      simp only [commutatorElement_def]
      group
    have hmem : r * n * r⁻¹ ∈ Z0 ⊔ Subgroup.zpowers n := by
      rw [hcomm]
      exact mul_mem (Subgroup.mem_sup_left (inv_mem (hall r hr n hnN)))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers n))
    have h0 : Subgroup.map (MulAut.conj r).toMonoidHom Z0 = Z0 := hZR r hr
    have hle : conjSubgroup r (Z0 ⊔ Subgroup.zpowers n) ≤ Z0 ⊔ Subgroup.zpowers n := by
      unfold conjSubgroup
      rw [Subgroup.map_sup, h0, MonoidHom.map_zpowers]
      exact sup_le le_sup_left (Subgroup.zpowers_le.mpr hmem)
    exact Subgroup.eq_of_le_of_card_ge hle
      (CFSG.RankThree.GF2n.card_conjSubgroup r (Z0 ⊔ Subgroup.zpowers n)).ge
  have hbound : Nat.card ↥(Z0 ⊔ Subgroup.zpowers n) ≤ 2 * Nat.card ↥Z0 := by
    have hD : Subgroup.zpowers (n ^ 2) ≤ Z0 := Subgroup.zpowers_le.mpr (hsq n hnN)
    have hDC : Subgroup.zpowers (n ^ 2) ≤ Subgroup.zpowers n :=
      Subgroup.zpowers_le.mpr (pow_mem (Subgroup.mem_zpowers n) 2)
    have hnorm' : Subgroup.zpowers n ≤ Subgroup.normalizer (Z0 : Set G) :=
      Subgroup.zpowers_le.mpr hnorm
    have hCZ : ∀ a ∈ Subgroup.zpowers n, ∀ b ∈ Z0, a * b * a⁻¹ ∈ Z0 := fun a ha b hb =>
      (Subgroup.mem_normalizer_iff.mp (hnorm' ha) b).mp hb
    have h1 := card_sup_mul_card_le_of_normalizes (Subgroup.zpowers n) Z0
      (Subgroup.zpowers (n ^ 2)) hDC hD hCZ
    simp only [Nat.card_zpowers] at h1
    rw [sup_comm] at h1
    have hord : orderOf n ≤ 2 * orderOf (n ^ 2) := by
      refine Nat.le_of_dvd (Nat.mul_pos (by norm_num) (orderOf_pos _)) ?_
      apply orderOf_dvd_of_pow_eq_one
      rw [pow_mul]
      exact pow_orderOf_eq_one _
    have hpos : 0 < orderOf (n ^ 2) := orderOf_pos _
    have h2 : Nat.card ↥(Z0 ⊔ Subgroup.zpowers n) * orderOf (n ^ 2) ≤
        (2 * Nat.card ↥Z0) * orderOf (n ^ 2) := by
      calc Nat.card ↥(Z0 ⊔ Subgroup.zpowers n) * orderOf (n ^ 2)
          ≤ orderOf n * Nat.card ↥Z0 := h1
        _ ≤ (2 * orderOf (n ^ 2)) * Nat.card ↥Z0 := Nat.mul_le_mul hord le_rfl
        _ = (2 * Nat.card ↥Z0) * orderOf (n ^ 2) := by ring
    exact Nat.le_of_mul_le_mul_right h2 hpos
  rcases hmin (Z0 ⊔ Subgroup.zpowers n) le_sup_left hAN hinv with heq | heq
  · have hn' : n ∈ Z0 ⊔ Subgroup.zpowers n := Subgroup.mem_sup_right (Subgroup.mem_zpowers n)
    rw [heq] at hn'
    exact hnZ hn'
  · have hb := hbound
    rw [heq] at hb
    omega

end CFSG.RankThree.GF2n.Stroth80
