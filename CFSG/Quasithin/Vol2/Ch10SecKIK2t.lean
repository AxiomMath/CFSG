module

public import CFSG.Quasithin.Vol2.Ch10SecKIK2s
public import CFSG.Quasithin.Vol2.Ch10SecC9S5e
public import CFSG.Quasithin.Vol2.Ch10SecKIK2m

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {Y X : Type} [Group Y] [Group X]

theorem isAlt_of_top {n : ℕ} (h : IsAlt n ↥(⊤ : Subgroup Y)) : IsAlt n Y := by
  obtain ⟨e⟩ := h
  exact ⟨Subgroup.topEquiv.symm.trans e⟩

theorem isHat_of_top {S : Type} [Group S] (h : IsHat ↥(⊤ : Subgroup Y) S) : IsHat Y S :=
  IsHat.of_mulEquiv Subgroup.topEquiv h

theorem isPSL_of_top {n p e : ℕ} (h : IsPSL n p e ↥(⊤ : Subgroup Y)) : IsPSL n p e Y := by
  obtain ⟨hadm, K, hF, hfin, hK, ⟨f⟩⟩ := h
  exact ⟨hadm, K, hF, hfin, hK, ⟨Subgroup.topEquiv.symm.trans f⟩⟩

variable [Finite Y] (π : Y →* X) (hπ : Function.Surjective π)
  (hker : π.ker ≤ Subgroup.center Y)
include hπ hker

theorem concl_b_of
    (hlist : B56QuasisimpleList X) (h : IsAlt 7 Y ∨ IsHat Y ↥(alternatingGroup (Fin 7))) :
    Nonempty (X ≃* ↥(alternatingGroup (Fin 7))) := by
  have : Finite X := Finite.of_surjective π hπ
  rcases h with ⟨⟨e⟩⟩ | h
  · have hZ : Subgroup.center Y = ⊥ := by
      apply Subgroup.card_eq_one.mp
      rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv, center_alt7, Subgroup.card_bot]
    obtain ⟨f⟩ := nonempty_equiv_of_ker_eq_bot π hπ (le_bot_iff.1 (hZ ▸ hker))
    exact ⟨f.trans e⟩
  · obtain ⟨-, h3, ⟨e⟩⟩ := h
    have hdvd : Nat.card π.ker ∣ 3 := h3 ▸ Subgroup.card_dvd_of_le hker
    rcases (Nat.dvd_prime (by norm_num)).1 hdvd with h1 | h1
    · exfalso
      obtain ⟨f⟩ := nonempty_equiv_of_ker_eq_bot π hπ (Subgroup.card_eq_one.mp h1)
      have hX : Nat.card X = 7560 := by
        rw [Nat.card_congr f.toEquiv, Subgroup.card_eq_card_quotient_mul_card_subgroup
          (Subgroup.center Y), h3, Nat.card_congr e.toEquiv, card_alternatingGroup1527d 7
          (by norm_num)]
        decide
      have := (b56Card_of_list hlist).cond (v := 3) (u := 945) (by rw [hX]; norm_num)
        (by decide)
      rw [hX] at this
      exact absurd this (by decide)
    · have hk : π.ker = Subgroup.center Y :=
        Subgroup.eq_of_le_of_card_ge hker (by rw [h1, h3])
      obtain ⟨f⟩ := nonempty_equiv_quot_of_ker_eq π hπ hk
      exact ⟨f.trans e⟩

omit [Finite Y] in
theorem concl_c_of {n : ℕ} (hn : 0 < n) (h : IsPSL n 2 1 Y) :
    π.ker = ⊥ ∧ Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) := by
  have hk : π.ker = ⊥ := le_bot_iff.1 (center_eq_bot_of_psl hn h ▸ hker)
  obtain ⟨f⟩ := nonempty_equiv_of_ker_eq_bot π hπ hk
  obtain ⟨g⟩ := nonempty_equiv_sl_of_psl h
  exact ⟨hk, ⟨f.trans g⟩⟩

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH
