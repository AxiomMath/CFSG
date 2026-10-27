module

public import CFSG.Quasithin.Vol2.Ch10SecK2To
public import CFSG.Quasithin.Vol2.Ch11SecCB51Ord
public import CFSG.Quasithin.Background.SmithB42G2Id

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique


theorem type_of_list {Y X : Type} [Group Y] [Finite Y] [Group X] [Finite X] (hY : GoodLie Y)
    {π : Y →* X} (hπ : Function.Surjective π)
    (hcard : Nat.card Y = Nat.card X ∨ Nat.card Y = 3 * Nat.card X)
    (hB : ∃ q : ℕ, 4 ≤ q ∧ (∃ n, q = 2 ^ n) ∧ q * (q ^ 2 - 1) ∣ Nat.card Y)
    (hlist : B56QuasisimpleList X) :
    ∃ (m : ℕ) (K : Type) (_ : Field K) (_ : Finite K), 2 ≤ m ∧ Nat.card K = 2 ^ m ∧
      (Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 3) K) ∨
        Nonempty (X ≃* ↥(Assembly.LowTwoRank.StatedSp 2 K)) ∨
        Nonempty (X ≃* ↥⁅quasithinG2 K, quasithinG2 K⁆)) := by
  have hN : ∀ N, Nat.card X = N → Nat.card Y = N ∨ Nat.card Y = 3 * N := fun N h => h ▸ hcard
  rcases hlist with ⟨n, K, _, _, hK, ⟨e⟩⟩ | ⟨n, K, _, _, hK, ⟨e⟩⟩ | ⟨n, K, _, _, hK, ⟨e⟩⟩ |
      ⟨n, K, _, _, hK, ⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | h6 | ⟨K, _, _, hK, ⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  ·
    refine (false_of_sl2_order hY (one_le_of_card_field hK) (hN _ ?_)).elim
    rw [Nat.card_congr e.toEquiv, card_statedSL_two1527d, hK]
  ·
    have hn := one_le_of_card_field hK
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · obtain rfl : n = 1 := by omega
      refine (false_of_sl32 hY (hN _ ?_) hB).elim
      rw [Nat.card_congr e.toEquiv, card_statedSL_three1527d, hK]
      norm_num
    · exact ⟨n, K, inferInstance, inferInstance, h2, hK,
        Or.inl ⟨e.trans (Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).symm⟩⟩
  ·
    have hn := one_le_of_card_field hK
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · obtain rfl : n = 1 := by omega
      have hX : Nat.card X = 720 := by
        rw [Nat.card_congr e.toEquiv, Ch11.SecC.B51.card_Sp4_eq_pow hK]
        norm_num
      exact (false_of_two_adic hY (hN _ hX) (v := 4) (u₀ := 45) (by norm_num) (by decide)
        (fun f _ hv => by omega) (fun f hf hv => by omega) (fun f _ hv => by omega)).elim
    · exact ⟨n, K, inferInstance, inferInstance, h2, hK, Or.inr (Or.inl ⟨e⟩)⟩
  ·
    have hn := one_le_of_card_field hK
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · obtain rfl : n = 1 := by omega
      have hX : Nat.card X = 12096 := by
        rw [Nat.card_congr e.toEquiv, card_quasithinG2_1527d hK, hK]
        norm_num
      refine (false_of_two_adic hY (hN _ hX) (v := 6) (u₀ := 189) (by norm_num) (by decide)
        (fun f _ hv => ?_) (fun f hf hv => by omega) (fun f hf hv => by omega)).elim
      obtain rfl : f = 2 := by omega
      decide
    · have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
      obtain ⟨c, hc0, hc1⟩ :=
        B42G2Id.exists_ne_zero_ne_one_of_three_le (K := K) (hK ▸ B42G2Id.three_le_two_pow h2)
      have hc : quasithinG2 K = ⁅quasithinG2 K, quasithinG2 K⁆ := by
        rw [CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup,
          JonesParshall.cayley_commutator_eq hc0 hc1]
      exact ⟨n, K, inferInstance, inferInstance, h2, hK,
        Or.inr (Or.inr ⟨e.trans (MulEquiv.subgroupCongr hc)⟩)⟩
  ·
    have hX : Nat.card X = 360 := by
      rw [Nat.card_congr e.toEquiv, card_alternatingGroup1527d 6 (by norm_num)]
      decide
    refine (false_of_two_adic hY (hN _ hX) (v := 3) (u₀ := 45) (by norm_num) (by decide)
      (fun f _ hv => ?_) (fun f hf hv => by omega) (fun f hf hv => by omega)).elim
    obtain rfl : f = 1 := by omega
    decide
  ·
    have hX : Nat.card X = 2520 := by
      rw [Nat.card_congr e.toEquiv, card_alternatingGroup1527d 7 (by norm_num)]
      decide
    refine (false_of_two_adic hY (hN _ hX) (v := 3) (u₀ := 315) (by norm_num) (by decide)
      (fun f _ hv => ?_) (fun f hf hv => by omega) (fun f hf hv => by omega)).elim
    obtain rfl : f = 1 := by omega
    decide
  ·
    have hX : Nat.card X = 1080 :=
      card_of_isHat1527d h6 (by rw [card_alternatingGroup1527d 6 (by norm_num)]; decide)
    refine (false_of_two_adic hY (hN _ hX) (v := 3) (u₀ := 135) (by norm_num) (by decide)
      (fun f _ hv => ?_) (fun f hf hv => by omega) (fun f hf hv => by omega)).elim
    obtain rfl : f = 1 := by omega
    decide
  ·
    have hX : Nat.card X = 6048 := by
      rw [Nat.card_congr e.toEquiv, SecA.C10P01.card_g2Two_commutator hK]
    exact (false_of_two_adic hY (hN _ hX) (v := 5) (u₀ := 189) (by norm_num) (by decide)
      (fun f _ hv => by omega) (fun f hf hv => by omega) (fun f hf hv => by omega)).elim
  ·
    have hX : Nat.card X = 20160 := by
      rw [Nat.card_congr e.toEquiv, card_statedSL_four_zmod1527d]
    exact (false_of_l42 hY (hN _ hX)
      (f := (Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 4 (ZMod 2)).symm.toMonoidHom.comp
        (e.toMonoidHom.comp π))
      ((Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 4 (ZMod 2)).symm.surjective.comp
        (e.surjective.comp hπ))).elim
  ·
    have hX : Nat.card X = 9999360 := by
      rw [Nat.card_congr e.toEquiv, card_statedSL_five_zmod1527d]
    exact (false_of_two_adic hY (hN _ hX) (v := 10) (u₀ := 9765) (by norm_num) (by decide)
      (fun f _ hv => by omega) (fun f hf hv => by omega) (fun f hf hv => by omega)).elim

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH
