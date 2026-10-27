module

public import CFSG.Quasithin.Background.B6Defs

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique

namespace B6

private theorem card_zpowers_swap :
    Nat.card (Subgroup.zpowers (Equiv.swap (0 : Fin 3) 1)) = 2 := by
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime (by ext x; fin_cases x <;> decide) (by
    intro h
    have := congrArg (fun f : Equiv.Perm (Fin 3) => f 0) h
    simp at this)

private theorem card_perm_three : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
  simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]

private theorem mem_zpowers_swap {x : Equiv.Perm (Fin 3)}
    (hx : x ∈ Subgroup.zpowers (Equiv.swap (0 : Fin 3) 1)) : x = 1 ∨ x = Equiv.swap 0 1 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hord : orderOf (Equiv.swap (0 : Fin 3) 1) = 2 :=
    orderOf_eq_prime (by ext x; fin_cases x <;> decide) (by
      intro h
      have := congrArg (fun f : Equiv.Perm (Fin 3) => f 0) h
      simp at this)
  rw [← zpow_mod_orderOf, hord]
  rcases Int.emod_two_eq_zero_or_one k with h | h <;> simp [h]

private theorem eq_or_eq_top {K : Subgroup (Equiv.Perm (Fin 3))}
    (h : Subgroup.zpowers (Equiv.swap (0 : Fin 3) 1) ≤ K) :
    K = Subgroup.zpowers (Equiv.swap (0 : Fin 3) 1) ∨ K = ⊤ := by
  have h1 : Nat.card K ∣ 6 := card_perm_three ▸ Subgroup.card_subgroup_dvd_card K
  have h2 : 2 ∣ Nat.card K := card_zpowers_swap ▸ Subgroup.card_dvd_of_le h
  have h3 : Nat.card K = 2 ∨ Nat.card K = 6 := by
    obtain ⟨k, hk⟩ := h2
    have h4 : 2 * k ∣ 2 * 3 := by rw [← hk]; exact h1
    have : k ∣ 3 := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h4
    have hk3 : k = 1 ∨ k = 3 := by
      have := Nat.le_of_dvd (by norm_num) this
      interval_cases k <;> simp_all
    omega
  rcases h3 with h3 | h3
  · left
    exact (Subgroup.eq_of_le_of_card_ge h (by rw [card_zpowers_swap, h3])).symm
  · right
    rw [← Subgroup.card_eq_iff_eq_top, h3, card_perm_three]

end B6

theorem minParabolic_perm_three :
    MinParabolic (⊤ : Subgroup (Equiv.Perm (Fin 3)))
      (Subgroup.zpowers (Equiv.swap 0 1)) (Subgroup.zpowers (Equiv.swap 0 1)) := by
  refine ⟨⟨le_top, ?_, ?_⟩, ?_, ?_⟩
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact IsPGroup.of_card (n := 1) (by simpa using B6.card_zpowers_swap)
  · have e : (((Subgroup.zpowers (Equiv.swap (0 : Fin 3) 1)).subgroupOf ⊤).index) =
        (Subgroup.zpowers (Equiv.swap (0 : Fin 3) 1)).index :=
      Subgroup.relIndex_top_right _
    have h := Subgroup.index_mul_card (Subgroup.zpowers (Equiv.swap (0 : Fin 3) 1))
    rw [B6.card_zpowers_swap, B6.card_perm_three] at h
    rw [e]
    have : (Subgroup.zpowers (Equiv.swap (0 : Fin 3) 1)).index = 3 := by omega
    rw [this]
    decide
  · intro h
    have hc := Subgroup.mem_normalizer_iff.mp (h (Subgroup.mem_top (Equiv.swap 1 2)))
      (Equiv.swap 0 1)
    have h1 : Equiv.swap (1 : Fin 3) 2 * Equiv.swap 0 1 * (Equiv.swap (1 : Fin 3) 2)⁻¹ ∈
        Subgroup.zpowers (Equiv.swap (0 : Fin 3) 1) :=
      hc.mp (Subgroup.mem_zpowers _)
    have h2 := B6.mem_zpowers_swap h1
    revert h2
    decide
  · have hlt : Subgroup.zpowers (Equiv.swap (0 : Fin 3) 1) < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro h
      have h2 := B6.card_zpowers_swap
      rw [h, Subgroup.card_top, B6.card_perm_three] at h2
      omega
    rw [isUniqueMaxOver_iff]
    refine ⟨⟨hlt, fun K hK _ => ?_⟩, le_rfl, fun N hN hTN => ?_⟩
    · rcases B6.eq_or_eq_top hK.le with h | h
      · exact absurd h (ne_of_gt hK)
      · exact h
    · rcases B6.eq_or_eq_top hTN with h | h
      · exact h
      · exact absurd h (ne_of_lt hN.1)

end CFSG.Quasithin
