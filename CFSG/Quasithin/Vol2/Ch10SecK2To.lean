module

public import CFSG.Quasithin.Vol2.Ch10SecK2Tn
public import CFSG.Quasithin.Vol2.Ch11SecQ9aL34B

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

section Excl


variable {Y : Type} [Group Y]

theorem false_of_l42 (hY : GoodLie Y) (hc : Nat.card Y = 20160 ∨ Nat.card Y = 3 * 20160)
    {f : Y →* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)} (hf : Function.Surjective f) :
    False := by
  have h2 : ∀ k u, Odd u → Nat.card Y = 2 ^ k * u → k = 6 := by
    intro k u hu h
    rcases hc with hc | hc
    · exact (eq_and_eq_of_two_pow_mul hu (by decide : Odd 315)
        (h.symm.trans (hc.trans (by norm_num)))).1
    · exact (eq_and_eq_of_two_pow_mul hu (by decide : Odd 945)
        (h.symm.trans (hc.trans (by norm_num)))).1
  obtain ⟨g, ⟨hg, h⟩ | ⟨hg, h⟩ | ⟨hg, h⟩ | ⟨hg, h⟩⟩ := hY
  · obtain ⟨u, hu, hcu, -⟩ := card_of_isPSL3 hg h
    obtain rfl : g = 2 := by have := h2 _ u hu hcu; omega
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
    have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
    refine Ch11.SecS.factL34_holds K hK4 (f.comp (e.symm.toMonoidHom.comp
      ((Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K).toMonoidHom.comp
        (QuotientGroup.mk' _)))) ?_
    exact hf.comp (e.symm.surjective.comp
      ((Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K).surjective.comp
        (QuotientGroup.mk'_surjective _)))
  · have hcu := card_of_isSL3 h
    obtain rfl : g = 2 := by
      have := h2 _ _ ((odd_pow_sub_one' hg (by norm_num)).mul
        (odd_pow_sub_one' hg (by norm_num))) hcu
      omega
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
    have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
    exact Ch11.SecS.factL34_holds K hK4 (f.comp (e.symm.toMonoidHom.comp
      (Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).toMonoidHom))
      (hf.comp (e.symm.surjective.comp (MulEquiv.surjective _)))
  · have := h2 _ _ ((odd_pow_sub_one' (by omega) (by norm_num)).mul
      (odd_pow_sub_one' (by omega) (by norm_num))) (card_of_isPSp4 (by omega) h)
    omega
  · have := h2 _ _ ((odd_pow_sub_one' (by omega) (by norm_num)).mul
      (odd_pow_sub_one' (by omega) (by norm_num))) (card_of_isG2 h)
    omega

theorem false_of_sl32 (hY : GoodLie Y) (hc : Nat.card Y = 168 ∨ Nat.card Y = 3 * 168)
    (hB : ∃ q : ℕ, 4 ≤ q ∧ (∃ n, q = 2 ^ n) ∧ q * (q ^ 2 - 1) ∣ Nat.card Y) : False := by
  obtain ⟨f, u, hu, h⟩ := goodLie_two_adic hY
  have key : ∀ k, Nat.card Y = 2 ^ k * u → k = 3 ∧ (u = 21 ∨ u = 63) := by
    intro k hk
    rcases hc with hc | hc
    · obtain ⟨h1, h2⟩ := eq_and_eq_of_two_pow_mul hu (by decide : Odd 21)
        (hk.symm.trans (hc.trans (show (168 : ℕ) = 2 ^ 3 * 21 by norm_num)))
      exact ⟨h1, Or.inl h2⟩
    · obtain ⟨h1, h2⟩ := eq_and_eq_of_two_pow_mul hu (by decide : Odd 63)
        (hk.symm.trans (hc.trans (show (3 * 168 : ℕ) = 2 ^ 3 * 63 by norm_num)))
      exact ⟨h1, Or.inr h2⟩
  have h168 : Nat.card Y = 168 := by
    rcases h with ⟨hf, hcu, hA⟩ | ⟨hf, hcu, -⟩ | ⟨hf, hcu, -⟩
    · obtain ⟨hk, hu'⟩ := key _ hcu
      obtain rfl : f = 1 := by omega
      rcases hu' with rfl | rfl
      · rw [hcu]
        norm_num
      · exfalso
        rcases hA with hA | hA <;> norm_num at hA
    · have := (key _ hcu).1
      omega
    · have := (key _ hcu).1
      omega
  obtain ⟨q, hq, ⟨n, rfl⟩, hdvd⟩ := hB
  rw [h168] at hdvd
  have hn : 2 ≤ n := by
    by_contra hn
    interval_cases n <;> norm_num at hq
  rcases Nat.lt_or_ge n 3 with h3 | h3
  · obtain rfl : n = 2 := by omega
    norm_num at hdvd
  · have h8 : 8 ≤ 2 ^ n := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h3
    have h64 : 64 ≤ (2 ^ n) ^ 2 := by nlinarith
    have := Nat.le_of_dvd (by norm_num) hdvd
    have : 8 * 63 ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) :=
      Nat.mul_le_mul h8 (by omega)
    omega

end Excl

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH
