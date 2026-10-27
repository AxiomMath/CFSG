module

public import CFSG.OddTranspositions.HalphaQuotient
import CFSG.OddTranspositions.SevenThreeConclusion
import CFSG.OddTranspositions.SevenFourEight.PrimeOrder
import CFSG.Quasithin.Background.A3Structure36AQuasi
import CFSG.GroupTheory.Fitting.LayerTopBot

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld.Bridge Asc72 CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem exists_DalphaStar_commute_AalphaStar (hC : HypothesisC D)
    (hA : (AalphaStar D hC.alpha).Nonempty) :
    ∃ b ∈ DalphaStar D hC.alpha, ∃ w ∈ AalphaStar D hC.alpha, Commute b w := by
  by_contra hno
  push Not at hno
  obtain ⟨w, hw⟩ := hA
  have hAu : ∀ y ∈ AalphaStar D hC.alpha, ¬ Commute y hC.d := fun y hy => by
    rw [hC.AalphaStar_eq_diff_alpha] at hy
    exact hy.1.2
  have hAα : ∀ y ∈ AalphaStar D hC.alpha, y ∉ hC.alpha := fun y hy hyα =>
    Set.disjoint_left.mp (disjoint_alpha_AalphaStar hC.isBlock_alpha) hyα hy
  have hS : ∀ x ∈ hC.alpha ∪ DalphaStar D hC.alpha, ∀ y ∈ D, Commute x y →
      y ∈ hC.alpha ∪ DalphaStar D hC.alpha := by
    intro x hx y hy hxy
    rcases (Set.ext_iff.mp hC.eq_alpha_union y).mp hy with hy' | hyA
    · exact hy'
    · exfalso
      rcases hx with hxα | hxD
      · exact hAu y hyA (commute_of_mem_block hC.setup.normal hC.setup.oddT hC.isBlock_alpha
          hxα hy (hAα y hyA) hxy hC.d hC.d_mem_alpha)
      · exact hno x hxD y hyA hxy
  have hwD : w ∈ D := AalphaStar_subset hC.setup.normal hC.isBlock_alpha hw
  rcases mem_of_reach hS (Or.inl hC.d_mem_alpha) (reach_of_not_disconnected hC.conn hC.hd hwD)
    with hwα | hwD'
  · exact hAα w hw hwα
  · exact hAu w hw (hC.DalphaStar_subset_commute hwD').2

theorem orderOf_mul_dvd_three_of_le_center {X : Type} [Group X] {N : Subgroup X} [N.Normal]
    (hN : N ≤ Subgroup.center X) {x y : X} (hx : x * x = 1) (hy : y * y = 1)
    (hodd : Odd (orderOf (x * y)))
    (h3 : orderOf (QuotientGroup.mk' N x * QuotientGroup.mk' N y) ∈ ({1, 2, 3} : Set ℕ)) :
    orderOf (x * y) ∣ 3 := by
  have hjdvd : orderOf (QuotientGroup.mk' N x * QuotientGroup.mk' N y) ∣ orderOf (x * y) := by
    rw [← map_mul]
    exact orderOf_map_dvd _ _
  have hj3 : orderOf (QuotientGroup.mk' N x * QuotientGroup.mk' N y) ∣ 3 := by
    rcases h3 with h | h | h
    · rw [h]
      exact one_dvd 3
    · rw [h] at hjdvd
      exact absurd (even_iff_two_dvd.mpr hjdvd) (Nat.not_even_iff_odd.mpr hodd)
    · rw [h]
  have hzN : (x * y) ^ 3 ∈ N := by
    have h1 := orderOf_dvd_iff_pow_eq_one.mp hj3
    rw [← map_mul, ← map_pow] at h1
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hinv : x * (x * y) * x⁻¹ = (x * y)⁻¹ := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hx, inv_eq_of_mul_eq_one_right hy, ← mul_assoc,
      hx, one_mul]
  have hzinv : x * (x * y) ^ 3 * x⁻¹ = ((x * y) ^ 3)⁻¹ := by
    rw [← conj_pow, hinv, inv_pow]
  have hzc : x * (x * y) ^ 3 * x⁻¹ = (x * y) ^ 3 := by
    rw [Subgroup.mem_center_iff.mp (hN hzN) x, mul_inv_cancel_right]
  have hzz : (x * y) ^ 3 * (x * y) ^ 3 = 1 :=
    mul_eq_one_iff_eq_inv.mpr (hzc.symm.trans hzinv)
  have hz1 : (x * y) ^ 3 = 1 :=
    OddTransp.eq_one_of_mul_self_of_odd hzz (hodd.of_dvd_nat (orderOf_pow_dvd 3))
  exact orderOf_dvd_of_pow_eq_one hz1

theorem pCore_two_not_le_center_Halpha_of_oddCore_le
    (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hsecond : ∀ u w v : G, IsTriangle D u w v → orderOf (u * v * w) = 4)
    (hnot3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hK : CFSG.oddCore ↥(Halpha D hC.alpha) ≤ Subgroup.center ↥(Halpha D hC.alpha))
    (h10 : ∀ x ∈ imageClass hC, ∀ y ∈ imageClass hC, orderOf (x * y) ∈ ({1, 2, 3} : Set ℕ)) :
    ¬ CFSG.pCore 2 ↥(Halpha D hC.alpha) ≤ Subgroup.center ↥(Halpha D hC.alpha) := by
  classical
  intro hQ
  have hD := hC.setup.oddT
  have hL : LocalSecond D := fun _ _ x y t _ _ _ h => hsecond x y t h
  have hW1 : ∀ a ∈ hC.alpha, ∀ c ∈ hC.alpha, Commute a c → a = c :=
    sixSeven hC (QZ.faithfulOnBlocks_of_localSecond hC hrad hL)
      (fun u _ v _ w h => hsecond u w v h)
  have hMZ : CFSG.solvableRadical ↥(Halpha D hC.alpha) ≤ Subgroup.center ↥(Halpha D hC.alpha) :=
    CFSG.Quasithin.A36A.solvableRadical_le_center
      (CFSG.WholeGroup.fittingSubgroup_le_pCore_two_sup_oddCore.trans (sup_le hQ hK))
  have h3H : ∀ x ∈ DalphaStar D hC.alpha, ∀ y ∈ DalphaStar D hC.alpha, ¬ Commute x y →
      orderOf (x * y) = 3 := by
    intro x hx y hy hxy
    have hxD : x ∈ D := DalphaStar_subset hC.isBlock_alpha hx
    have hyD : y ∈ D := DalphaStar_subset hC.isBlock_alpha hy
    let x' : Halpha D hC.alpha := ⟨x, Subgroup.subset_closure hx⟩
    let y' : Halpha D hC.alpha := ⟨y, Subgroup.subset_closure hy⟩
    have hord : orderOf (x' * y') = orderOf (x * y) := (Subgroup.orderOf_coe (x' * y')).symm
    have hdvd : orderOf (x' * y') ∣ 3 :=
      orderOf_mul_dvd_three_of_le_center hMZ (Subtype.ext (hD.mul_self_eq_one hxD))
        (Subtype.ext (hD.mul_self_eq_one hyD)) (hord ▸ hD.odd_of_not_commute hxD hyD hxy)
        (h10 _ ⟨x', hx, rfl⟩ _ ⟨y', hy, rfl⟩)
    rw [hord] at hdvd
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact absurd (hD.eq_of_mul_eq_one hxD (orderOf_eq_one_iff.mp h1) ▸ Commute.refl x) hxy
    · exact h3
  have hAu : ∀ y ∈ AalphaStar D hC.alpha, ¬ Commute y hC.d := fun y hy => by
    rw [hC.AalphaStar_eq_diff_alpha] at hy
    exact hy.1.2
  obtain ⟨p, -, hpA⟩ := exists_prime_orderOf_eq_AalphaStar hC hsecond
  have hall3 : ∀ w ∈ AalphaStar D hC.alpha, orderOf (hC.d * w) = 3 := by
    intro w hw
    obtain ⟨b, hb, w', hw', hbw'⟩ := exists_DalphaStar_commute_AalphaStar hC ⟨w, hw⟩
    have hbD : b ∈ D := DalphaStar_subset hC.isBlock_alpha hb
    have hbu : Commute b hC.d := (hC.DalphaStar_subset_commute hb).2
    have hbne : b ≠ hC.d := by
      rw [hC.DalphaStar_alpha] at hb
      exact (OddLocal.subset_commSet hC.setup.normal hC.hE hb).2.2
    obtain ⟨k, hk⟩ := isConj_iff.mp (hC.setup.isConj hC.hd hbD)
    have hkb : k⁻¹ * b * k = hC.d := by
      rw [← hk]
      group
    have hmem : ∀ z ∈ D, Commute z b → z ≠ b → k⁻¹ * z * k ∈ DalphaStar D hC.alpha := by
      intro z hz hzb hzne
      have hzc : Commute (k⁻¹ * z * k) hC.d := by
        have h' := (Commute.conj_iff k⁻¹).mpr hzb
        rwa [inv_inv, hkb] at h'
      have hzD : k⁻¹ * z * k ∈ D := by
        simpa using hC.setup.normal k⁻¹ z hz
      have hzne' : k⁻¹ * z * k ≠ hC.d := fun h => hzne (by rw [← hk, ← h]; group)
      rcases (Set.ext_iff.mp hC.eq_alpha_union _).mp hzD with (h | h) | h
      · exact absurd (hW1 _ h _ hC.d_mem_alpha hzc) hzne'
      · exact h
      · exact absurd hzc (hAu _ h)
    have hx := hmem hC.d hC.hd hbu.symm hbne.symm
    have hy := hmem w' (AalphaStar_subset hC.setup.normal hC.isBlock_alpha hw') hbw'.symm
      (fun h => hAu w' hw' (h ▸ hbu))
    have hxy : ¬ Commute (k⁻¹ * hC.d * k) (k⁻¹ * w' * k) := fun h => by
      have h' := (Commute.conj_iff k).mpr h
      simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] at h'
      exact hAu w' hw' h'.symm
    have h3 : orderOf (hC.d * w') = 3 := by
      rw [← h3H _ hx _ hy hxy]
      refine SemiconjBy.orderOf_eq k⁻¹ ?_
      unfold SemiconjBy
      group
    rw [hpA w hw, ← hpA w' hw', h3]
  obtain ⟨w, hw, hw3⟩ := sevenThree hC hrad hL hall3 hnot3
  exact hw3 (hall3 w hw)

end CFSG.OddTranspositions

end
