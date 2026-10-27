module

public import CFSG.Quasithin.Vol2.Ch11SecO7b

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Open CFSG.Blueprint
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp specialLinearGroupEquivStatedSL)

namespace C10KH

theorem fam_ne_of_bound {N A k : ℕ} (hA : ¬ 2 ^ (A + 1) ∣ N) (hk : 1 ≤ k) {f : ℕ → ℕ}
    (hf : ∀ m, 2 ^ (k * m) ∣ f m) (hchk : ∀ m ≤ A, f m ≠ N) : ∀ m, f m ≠ N := by
  intro m hm
  by_cases hmA : m ≤ A
  · exact hchk m hmA hm
  · apply hA
    rw [← hm]
    exact (Nat.pow_dvd_pow 2 (by nlinarith)).trans (hf m)


theorem not_list701Excl_of {Y : Type} [Group Y] {N : ℕ} (hY : Nat.card Y = N)
    (hL2 : ∀ m, 2 ^ m * ((2 ^ m) ^ 2 - 1) ≠ N)
    (hSL3 : ∀ m, (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1)) ≠ N)
    (hSp4 : ∀ m, (2 ^ m) ^ 4 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 4 - 1)) ≠ N)
    (hG2 : ∀ m, (2 ^ m) ^ 6 * (((2 ^ m) ^ 6 - 1) * ((2 ^ m) ^ 2 - 1)) ≠ N)
    (hG22 : ¬ N ∣ 12096) (h6 : 6 < N)
    (hfix : N ≠ 60 ∧ N ≠ 360 ∧ N ≠ 2520 ∧ N ≠ 1080 ∧ N ≠ 20160 ∧ N ≠ 9999360 ∧
      N ≠ 244823040) : ¬ List701Excl Y := by
  classical
  obtain ⟨hf60, hf360, hf2520, hf1080, hf20160, hf9999360, hfM24⟩ := hfix
  intro h
  rcases h with ⟨m, hm⟩ | ⟨K, _, _, m, hK, h⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨-, hZ, ⟨e⟩⟩ | ⟨⟨e⟩⟩ |
    ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · rcases hm with ⟨-, hm⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact hL2 m ((SecA.C10KH.card_of_isPSL_two_two hm).2.symm.trans hY)
    all_goals exact absurd h0 (by norm_num)
  · have hm1 : 1 ≤ m := by
      have := Finite.one_lt_card (α := K)
      rw [hK] at this
      by_contra h0
      simp [show m = 0 by omega] at this
    have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two hm1 hK
    have := Fintype.ofFinite K
    rcases h with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨π, hπ⟩
    · refine hSL3 m ?_
      rw [← hY, Nat.card_congr e.toEquiv,
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), hK,
        show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num)]
    · refine hSp4 m ?_
      rw [← hY, Nat.card_congr e.toEquiv,
        CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hK,
        show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair (by norm_num)]
      norm_num
    · rw [Nat.card_congr e.toEquiv] at hY
      by_cases hm2 : 2 ≤ m
      · obtain ⟨c, hc0, hc1⟩ := C10KH.exists_ne_zero_ne_one (K := K) (by
          rw [hK]
          calc 2 < 2 ^ 2 := by norm_num
            _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2)
        refine hG2 m ?_
        rw [← hY, KGNat.commutator_quasithinG2_eq hc0 hc1, KGNat.card_cayleyGroup, hK]
      · have hdvd := Subgroup.card_dvd_of_le (KGNat.commutator_quasithinG2_le (K := K))
        rw [KGNat.card_cayleyGroup, hK, hY, show m = 1 by omega] at hdvd
        exact hG22 hdvd
    · let π' := π.comp (specialLinearGroupEquivStatedSL 2 K).toMonoidHom
      have hπ' : Function.Surjective π' := hπ.comp (specialLinearGroupEquivStatedSL 2 K).surjective
      have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) = 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
        rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hK]
      by_cases hm2 : 2 ≤ m
      · have := SecA.isSimpleGroup_SL2 hm2 hK
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π'.ker with hb | ht
        · have hc := Nat.card_eq_of_bijective π' ⟨(MonoidHom.ker_eq_bot_iff π').mp hb, hπ'⟩
          exact hL2 m (hSL.symm.trans (hc.trans hY))
        · have h1 : ∀ y : Y, y = 1 := fun y => by
            obtain ⟨x, rfl⟩ := hπ' y
            exact (MonoidHom.mem_ker).mp (ht ▸ Subgroup.mem_top x)
          have : Subsingleton Y := ⟨fun a b => (h1 a).trans (h1 b).symm⟩
          rw [Nat.card_unique] at hY
          omega
      · have hle := Nat.card_le_card_of_surjective π' hπ'
        rw [hSL, hY, show m = 1 by omega] at hle
        norm_num at hle
        omega
  · rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin] at hY
    exact hf60 (hY.symm.trans (by decide))
  · rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin] at hY
    exact hf360 (hY.symm.trans (by decide))
  · rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin] at hY
    exact hf2520 (hY.symm.trans (by decide))
  · rw [(Subgroup.center Y).card_eq_card_quotient_mul_card_subgroup, Nat.card_congr e.toEquiv,
      nat_card_alternatingGroup, Nat.card_fin, hZ] at hY
    exact hf1080 (hY.symm.trans (by decide))
  · rw [Nat.card_congr e.toEquiv,
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), Nat.card_zmod]
      at hY
    exact hf20160 (hY.symm.trans (by decide))
  · rw [Nat.card_congr e.toEquiv,
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), Nat.card_zmod]
      at hY
    exact hf9999360 (hY.symm.trans (by decide))
  · rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.Mathieu.card_M24] at hY
    exact hfM24 hY.symm

theorem not_list701Excl_of_fixed {Y : Type} [Group Y] {N A : ℕ} (hY : Nat.card Y = N)
    (hA : ¬ 2 ^ (A + 1) ∣ N)
    (hchk : ∀ m ≤ A, 2 ^ m * ((2 ^ m) ^ 2 - 1) ≠ N ∧
      (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1)) ≠ N ∧
      (2 ^ m) ^ 4 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 4 - 1)) ≠ N ∧
      (2 ^ m) ^ 6 * (((2 ^ m) ^ 6 - 1) * ((2 ^ m) ^ 2 - 1)) ≠ N)
    (hG22 : ¬ N ∣ 12096) (h6 : 6 < N)
    (hfix : N ≠ 60 ∧ N ≠ 360 ∧ N ≠ 2520 ∧ N ≠ 1080 ∧ N ≠ 20160 ∧ N ≠ 9999360 ∧
      N ≠ 244823040) : ¬ List701Excl Y :=
  not_list701Excl_of hY
    (fam_ne_of_bound hA le_rfl (fun m => by rw [one_mul]; exact dvd_mul_right _ _)
      fun m hm => (hchk m hm).1)
    (fam_ne_of_bound hA (by norm_num : 1 ≤ 3) (fun m => by rw [pow_mul']; exact dvd_mul_right _ _)
      fun m hm => (hchk m hm).2.1)
    (fam_ne_of_bound hA (by norm_num : 1 ≤ 4) (fun m => by rw [pow_mul']; exact dvd_mul_right _ _)
      fun m hm => (hchk m hm).2.2.1)
    (fam_ne_of_bound hA (by norm_num : 1 ≤ 6) (fun m => by rw [pow_mul']; exact dvd_mul_right _ _)
      fun m hm => (hchk m hm).2.2.2)
    hG22 h6 hfix

end C10KH

end CFSG.Quasithin.Vol2.Ch11.SecE
