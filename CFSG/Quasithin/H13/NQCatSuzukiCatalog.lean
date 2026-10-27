module

public import CFSG.RankThree.Chevalley.ExceptionalModelOrderThree
public import CFSG.RankThree.PartTwo.KFacts.KS14SzRee
public import CFSG.RankThree.PartTwo.KFacts.KS14SzClassical
public import CFSG.RankThree.OddKernel.SporadicKernelTh
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelOrders

public section

namespace CFSG.Quasithin.H13.NQCat

open CFSG.Blueprint

theorem three_dvd_card_alternatingGroup_fin {n : ℕ} (hn : 3 ≤ n) :
    3 ∣ Nat.card (alternatingGroup (Fin n)) := by
  have h3 : (Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ *
      Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨2, by omega⟩).IsThreeCycle :=
    Equiv.Perm.isThreeCycle_swap_mul_swap_same (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
      (by simp [Fin.ext_iff])
  have ho : orderOf (⟨_, h3.mem_alternatingGroup⟩ : alternatingGroup (Fin n)) = 3 := by
    rw [Subgroup.orderOf_mk, h3.orderOf]
  rw [← ho]
  exact orderOf_dvd_natCard _

theorem sporadic_models_order_divisible_by_three
    {T : Type} [Group T] [Finite T] [Nontrivial T] (h : NativeSporadic.SporadicRep T) :
    3 ∣ Nat.card T := by
  obtain ⟨s, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv]
  by_cases hTh : s = .Th
  · subst hTh
    change 3 ∣ Nat.card NativeSporadic.Th
    rw [RankThree.OddKernel.card_Th_eq]
    norm_num
  by_cases hM : s = .M
  · subst hM
    change 3 ∣ Nat.card NativeSporadic.M
    have : Nontrivial NativeSporadic.M := e.symm.toEquiv.nontrivial
    obtain ⟨E, -, hE⟩ := SectionRank.M_nontrivial_elementary_three_rank_four
    have hdvd := Subgroup.card_subgroup_dvd_card E
    rw [hE] at hdvd
    exact (dvd_pow_self 3 (by norm_num)).trans hdvd
  rw [EvenSmallLie.Child3.card_carrier s hTh hM]
  cases s <;> first
    | exact absurd rfl hTh
    | exact absurd rfl hM
    | norm_num [EvenSmallLie.Child3.sporadicCard, CFSG.Open.monsterBabyOrder]

theorem catalog_prime_to_three_simple_groups_are_exact_Suzuki_models
    (J : Type) [Group J] [Finite J] [IsSimpleGroup J] (hnab : ∃ a b : J, a * b ≠ b * a)
    (hcat : Catalog J) (h3 : ¬ 3 ∣ Nat.card J) :
    ∃ a : ℕ, 1 ≤ a ∧ (∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ (2 * a + 1) ∧
      Nonempty (J ≃* suzukiGroup a k)) ∧ SuzukiModel J 2 (2 * a + 1) := by
  rcases hcat with ⟨p, -, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨t, n, p, f, hm⟩ |
      (⟨t, p, f, -, hm⟩ | ⟨t, p, f, -, hm⟩ | ⟨p, f, -, a, ha, k, hk, hkf, rfl, hcard, ⟨e⟩⟩) | hs
  · obtain ⟨x, y, hxy⟩ := hnab
    exact absurd (e.injective (by rw [map_mul, map_mul, mul_comm])) hxy
  · refine absurd ?_ h3
    rw [Nat.card_congr e.toEquiv]
    exact three_dvd_card_alternatingGroup_fin (by omega)
  · exact absurd (RankThree.PartTwo.KFacts.KS14.classicalModel_exists_orderOf_eq_three hm).2 h3
  · exact absurd (RankThree.Chevalley.Chevalley_exceptional_models_order_divisible_by_three J t p f
      hm) h3
  · exact absurd (RankThree.PartTwo.KFacts.KS14.three_dvd_card_of_reeTitsModel hm) h3
  · exact ⟨a, ha, ⟨k, hk, hkf, hcard, ⟨e⟩⟩, rfl, a, ha, k, hk, hkf, rfl, hcard, ⟨e⟩⟩
  · exact absurd (sporadic_models_order_divisible_by_three hs) h3

end CFSG.Quasithin.H13.NQCat
