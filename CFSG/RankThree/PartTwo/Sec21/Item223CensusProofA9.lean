module

public import CFSG.RankThree.PartTwo.Sec21.Item223CensusProofSporadic

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)

namespace Item223CensusProof

theorem orderOf_ne_twentyOne (σ : Equiv.Perm (Fin 9)) : orderOf σ ≠ 21 := by
  intro h21
  set s := σ.cycleType with hs
  have hsum : s.sum ≤ 9 := by
    rw [hs, Equiv.Perm.sum_cycleType]
    exact (Finset.card_le_univ _).trans (by simp)
  have hmem : ∀ x ∈ s, x = 3 ∨ x = 7 := by
    intro x hx
    have h1 : x ∣ 21 := h21 ▸ Equiv.Perm.dvd_of_mem_cycleType hx
    have h2 : 2 ≤ x := Equiv.Perm.two_le_of_mem_cycleType hx
    have h3 : x ≤ 9 := (Multiset.le_sum_of_mem hx).trans hsum
    interval_cases x <;> simp_all
  have hlcm : s.lcm = 21 := by rw [hs, Equiv.Perm.lcm_cycleType, h21]
  have h3 : 3 ∈ s := by
    by_contra h3
    have hdvd : s.lcm ∣ 7 := Multiset.lcm_dvd.mpr fun x hx => by
      rcases hmem x hx with rfl | rfl
      · exact absurd hx h3
      · exact dvd_rfl
    rw [hlcm] at hdvd
    norm_num at hdvd
  have h7 : 7 ∈ s := by
    by_contra h7
    have hdvd : s.lcm ∣ 3 := Multiset.lcm_dvd.mpr fun x hx => by
      rcases hmem x hx with rfl | rfl
      · exact dvd_rfl
      · exact absurd hx h7
    rw [hlcm] at hdvd
    norm_num at hdvd
  obtain ⟨t, ht⟩ := Multiset.exists_cons_of_mem h3
  have h7t : 7 ∈ t := by
    rw [ht, Multiset.mem_cons] at h7
    rcases h7 with h | h
    · norm_num at h
    · exact h
  obtain ⟨u, hu⟩ := Multiset.exists_cons_of_mem h7t
  rw [ht, hu, Multiset.sum_cons, Multiset.sum_cons] at hsum
  omega

theorem center_eq_bot_of_isSimpleGroup {S : Type*} [Group S] [IsSimpleGroup S]
    (hnp : ¬ (Nat.card S).Prime) : Subgroup.center S = ⊥ := by
  refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S)).resolve_right
    fun htop => hnp ?_
  have : IsMulCommutative S := ⟨⟨fun a b =>
    Subgroup.mem_center_iff.mp (htop ▸ Subgroup.mem_top b) a⟩⟩
  exact Group.is_simple_iff_prime_card.mp inferInstance

theorem card_alternatingGroup_nine : Nat.card (alternatingGroup (Fin 9)) = 181440 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  decide

theorem noL2Inner223_alternatingGroup_nine : NoL2Inner223 (alternatingGroup (Fin 9)) := by
  intro Kb m a ⟨eK⟩ hm1 hmo haZ ha3 hcomm
  have : IsSimpleGroup (alternatingGroup (Fin 9)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; norm_num)
  have hZ : Subgroup.center (alternatingGroup (Fin 9)) = ⊥ :=
    center_eq_bot_of_isSimpleGroup (by rw [card_alternatingGroup_nine]; norm_num)
  rw [hZ, Subgroup.mem_bot] at haZ ha3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have ha : orderOf a = 3 := orderOf_eq_prime ha3 haZ
  have hdvd := two_pow_sub_one_dvd_card (by omega) eK
  rw [card_alternatingGroup_nine] at hdvd
  have hm3 : m = 3 := by
    by_contra hm3
    have hcheck : ∀ m < 18, 1 < m → Odd m → m ≠ 3 → ¬ 2 ^ m - 1 ∣ 181440 := by decide
    by_cases hmb : m < 18
    · exact hcheck m hmb hm1 hmo hm3 hdvd
    · have h1 : 2 ^ 18 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 := Nat.le_of_dvd (by norm_num) hdvd
      omega
  subst hm3
  have hK : Nat.card Kb = 504 := by
    rw [Nat.card_congr eK.toEquiv, card_projSL_two 3 (by norm_num)]
    norm_num
  have : Finite Kb := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 7 (by rw [hK]; norm_num)
  have hc' : orderOf (c : alternatingGroup (Fin 9)) = 7 := by rwa [Subgroup.orderOf_coe]
  have hac : Commute a (c : alternatingGroup (Fin 9)) := hcomm c c.2
  have h21 : orderOf (a * c) = 21 := by
    rw [hac.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [ha, hc']; norm_num), ha, hc']
  exact orderOf_ne_twentyOne _ (by rwa [Subgroup.orderOf_coe])

end Item223CensusProof

open Item223CensusProof

theorem census223A9_holds : Census223A9 :=
  Or.inr noL2Inner223_alternatingGroup_nine

end CFSG.RankThree.PartTwo.Sec21
