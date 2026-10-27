module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148WA5Normal
import CFSG.RankThree.PartTwo.Sec14.Ronan148VDelta
import CFSG.RankThree.PartTwo.Sec14.Ronan148JNA6

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155NO

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14
open scoped commutatorElement

private theorem prime_eq_two_three_five_of_dvd {p n a b c : ℕ} (hp : p.Prime)
    (hn : n = 2 ^ a * 3 ^ b * 5 ^ c) (h : p ∣ n) : p = 2 ∨ p = 3 ∨ p = 5 := by
  subst hn
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
        (hp.dvd_of_dvd_pow h)))
  · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp
      (hp.dvd_of_dvd_pow h)))

private theorem card_of_isA6CoverTimesA5 {W : Type*} [Group W] [Finite W]
    (h : IsA6CoverTimesA5 W) : Nat.card W = 64800 := by
  obtain ⟨U, V, -, hVn, hint, hUV, hU, ⟨φ⟩⟩ := h
  have hN : U ≤ Subgroup.normalizer (V : Set W) := by
    rw [@Subgroup.normalizer_eq_top _ _ V hVn]
    exact le_top
  have key := Ronan148V.card_sup_mul_card_inf hN
  rw [hUV, hint, Subgroup.card_top, Subgroup.card_bot, HJRes2.card_of_isTripleCover_six hU,
    Nat.card_congr φ.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.1] at key
  omega

private theorem noNormal3_of_isA6CoverTimesA5 {W : Type*} [Group W] [Finite W]
    (h : IsA6CoverTimesA5 W) : Ronan148W.NoNormal3 W := by
  obtain ⟨U, V, hUn, hVn, hint, hUV, hU, ⟨φ⟩⟩ := h
  have hcomm : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u := fun u hu v hv => by
    have hmem : ⁅u, v⁆ ∈ U ⊓ V :=
      Subgroup.commutator_le_inf U V (Subgroup.commutator_mem_commutator hu hv)
    rw [hint, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmem
  have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hA6 : 3 ∣ Nat.card (alternatingGroup (Fin 6)) := by
    rw [Ronan148W.card_alternatingGroup_six]
    norm_num
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hA5 : 3 ∣ Nat.card (alternatingGroup (Fin 5)) := by
    rw [KFacts.KS14.card_alternatingGroup_five_seven_ten.1]
    norm_num
  have hV3 : Ronan148W.NoNormal3 ↥V :=
    Ronan148W.noNormal3_congr φ.symm (Ronan148W.noNormal3_of_isSimpleGroup hA5)
  have hzV : ∀ z ∈ Subgroup.center ↥V, z ^ 3 = 1 := by
    intro z hz
    have hcen : Subgroup.center ↥V = ⊥ := by
      have hmap := Subgroup.map_center_eq φ
      rw [Ronan148J.center_alternatingGroup_five_eq_bot] at hmap
      exact (Subgroup.map_eq_bot_iff_of_injective _ φ.injective).mp hmap
    rw [hcen, Subgroup.mem_bot] at hz
    rw [hz, one_pow]
  exact Ronan148W.noNormal3_of_commute_sup hUn hVn hUV hcomm
    (Ronan148W.noNormal3_of_isTripleCover hA6 hU) hV3
    (fun z hz => Ronan148W.pow_three_eq_one_of_mem_center hU.1 hz) hzV

theorem typeFacts_of_prod148 {T : Type*} [Group T] [Finite T]
    (hT : IsCentralProductA6Covers T ∨ IsA6CoverTimesA5 T ∨
      Nonempty (T ≃* alternatingGroup (Fin 5) × alternatingGroup (Fin 5))) :
    25 ∣ Nat.card T ∧ (∀ p : ℕ, p.Prime → p ∣ Nat.card T → p = 2 ∨ p = 3 ∨ p = 5) ∧
      Ronan148W.NoNormal3 T := by
  have hcard : Nat.card T = 388800 ∨ Nat.card T = 64800 ∨ Nat.card T = 3600 := by
    rcases hT with hcp | ha5 | hne
    · exact Or.inl (Ronan148V.card_of_isCentralProductA6Covers hcp)
    · exact Or.inr (Or.inl (card_of_isA6CoverTimesA5 ha5))
    · obtain ⟨e⟩ := hne
      refine Or.inr (Or.inr ?_)
      rw [Nat.card_congr e.toEquiv, Nat.card_prod,
        KFacts.KS14.card_alternatingGroup_five_seven_ten.1] <;> norm_num
  refine ⟨?_, ?_, ?_⟩
  · rcases hcard with h | h | h <;> rw [h] <;> norm_num
  · intro p hp hdvd
    rcases hcard with h | h | h <;> rw [h] at hdvd
    · exact prime_eq_two_three_five_of_dvd (a := 6) (b := 5) (c := 2) hp (by norm_num) hdvd
    · exact prime_eq_two_three_five_of_dvd (a := 5) (b := 4) (c := 2) hp (by norm_num) hdvd
    · exact prime_eq_two_three_five_of_dvd (a := 4) (b := 2) (c := 2) hp (by norm_num) hdvd
  · rcases hT with hcp | ha5 | hne
    · exact Ronan148W.noNormal3_of_isCentralProductA6Covers hcp
    · exact noNormal3_of_isA6CoverTimesA5 ha5
    · obtain ⟨e⟩ := hne
      exact Ronan148W.noNormal3_congr e.symm Ronan148W.noNormal3_alternating_five_sq

end CFSG.RankThree.PartTwo.Sec15.Sylow155NO
