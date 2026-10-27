module

public import CFSG.Quasithin.Vol2.Ch11SecAKE9
public import CFSG.Quasithin.Vol2.Ch11SecAKE10
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5112NotLie

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA.C10KH

open CFSG.Open CFSG.Blueprint

theorem nonabelian_of_simple {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (h : ¬ (Nat.card X).Prime) : ∃ a b : X, a * b ≠ b * a := by
  by_contra hab
  push Not at hab
  have h1 : Nat.card X ≠ 1 := fun h1 => by
    have := Finite.one_lt_card (α := X)
    omega
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd h1
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := X) p hpd
  have hN : (Subgroup.zpowers g).Normal := ⟨fun n hn x => by rwa [hab x n, mul_inv_cancel_right]⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers g) with hb | ht
  · have : g = 1 := by
      rw [← Subgroup.mem_bot, ← hb]
      exact Subgroup.mem_zpowers g
    rw [this, orderOf_one] at hg
    exact hp.one_lt.ne' hg.symm
  · apply h
    rw [← Subgroup.card_top (G := X), ← ht, Nat.card_zpowers, hg]
    exact hp

theorem list3One_of_simple {X : Type} [Group X] [Finite X] [IsSimpleGroup X] {N : ℕ}
    (hN : Nat.card X = N) (hNp : ¬ N.Prime) (hr : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X))
    (hd : ∀ {s : Bool} {p e : ℕ}, p.Prime → IsPSLEps3 s p e X → s = false ∧ p = 5 ∧ e = 1) :
    CFSG.IsQuasisimple X ∧ Nat.card (Subgroup.center X) ∣ 3 ∧
      2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) ∧
      ∀ (s : Bool) (p e : ℕ), p.Prime → 1 ≤ e → IsPSLEps3 s p e X →
        s = false ∧ p = 5 ∧ e = 1 := by
  obtain ⟨hq, hZ⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup
    (nonabelian_of_simple (X := X) (by rwa [hN]))
  refine ⟨hq, ?_, hr, fun s p e hp _ h => hd hp h⟩
  rw [hZ, Subgroup.card_bot]
  exact one_dvd 3

theorem card_of_isHat {X S : Type} [Group X] [Group S] (h : IsHat X S) :
    Nat.card X = Nat.card S * 3 := by
  obtain ⟨-, h3, ⟨e⟩⟩ := h
  rw [(Subgroup.center X).card_eq_card_quotient_mul_card_subgroup, h3, Nat.card_congr e.toEquiv]

theorem list3One_of_hat {X S : Type} [Group X] [Finite X] [Group S] [Finite S] (h : IsHat X S)
    (hr : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S))
    (hd : ∀ {s : Bool} {p e : ℕ}, p.Prime → IsPSLEps3 s p e X → s = false ∧ p = 5 ∧ e = 1) :
    CFSG.IsQuasisimple X ∧ Nat.card (Subgroup.center X) ∣ 3 ∧
      2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) ∧
      ∀ (s : Bool) (p e : ℕ), p.Prime → 1 ≤ e → IsPSLEps3 s p e X →
        s = false ∧ p = 5 ∧ e = 1 := by
  obtain ⟨hq, h3, ⟨e⟩⟩ := h
  refine ⟨hq, by rw [h3], ?_, fun s p e hp _ h => hd hp h⟩
  exact CFSG.Quasithin.H13.L128P.two_le_pRank_of_surjective' Nat.prime_three (by norm_num)
    (e.toMonoidHom.comp (QuotientGroup.mk' _))
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) hr

theorem list3One_su35 {X : Type} [Group X] [Finite X] (h : IsSU3 5 X) :
    CFSG.IsQuasisimple X ∧ Nat.card (Subgroup.center X) ∣ 3 ∧
      2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) ∧
      ∀ (s : Bool) (p e : ℕ), p.Prime → 1 ≤ e → IsPSLEps3 s p e X →
        s = false ∧ p = 5 ∧ e = 1 := by
  have hN : Nat.card X = 378000 := by
    rw [C11P9B.card_of_isSU3 h]
    norm_num
  refine ⟨?_, ?_, two_le_pRank_su35 h, fun s p e hp _ h' => psleps3_of_card_378000 hN hp h'⟩
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm
      (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (p := 5) (f := 1)
        (by rw [hK]; norm_num) le_rfl (by norm_num)).1
  · have h1 := (Subgroup.center X).card_eq_card_quotient_mul_card_subgroup
    rw [hN, H13.NotLie.card_su35_quot h] at h1
    have h3 : Nat.card (Subgroup.center X) = 3 := by omega
    rw [h3]

end CFSG.Quasithin.Vol2.Ch11.SecA.C10KH
