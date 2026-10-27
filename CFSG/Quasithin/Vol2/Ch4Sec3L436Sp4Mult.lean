module

public import CFSG.Quasithin.Vol2.Ch4Sec3L436Sp4Defs
public import CFSG.RankThree.PartOne.KF.ClsCenter

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
open CFSG.Blueprint.Multiplier

namespace Sp4Mult

theorem card_multiplicative_zmod (k : ℕ) : Nat.card (Multiplicative (ZMod k)) = k := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

theorem card_multiplier_psp4_two {n : ℕ} (hn : 1 ≤ n) :
    Nat.card (generic .PSp 2 2 n × exceptional .PSp 2 2 n) = 1 := by
  have hodd : Odd (2 ^ n - 1) :=
    Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
  have hg : genericOrders .PSp 2 2 n = (1, 1) := by
    show (Nat.gcd 2 (2 ^ n - 1), 1) = (1, 1)
    rw [Nat.Coprime.gcd_eq_one (Nat.coprime_two_left.mpr hodd)]
  have he : exceptionalOrders .PSp 2 2 n = (1, 1) := rfl
  simp only [Nat.card_prod, card_multiplicative_zmod, hg, he, mul_one]

end Sp4Mult

theorem sp4MultTrivial_of (hGA : CFSG.Open.GriessAllModelsStatement) : Sp4MultTrivial := by
  intro X _ _ n hn hX hm
  have hm' : CFSG.Models.LieModel (X ⧸ Subgroup.center X) .PSp 2 2 n := ⟨hm.1, Or.inl hm⟩
  obtain ⟨hperf, hcard⟩ := CFSG.RankThree.PartOne.card_hopfMultiplier_of_model hGA hm'
  have hd := CFSG.RankThree.PartOne.card_ker_dvd_card_hopfMultiplier hperf ⟨hX.1⟩
    (QuotientGroup.mk' (Subgroup.center X)) (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' (Subgroup.center X)).le
  rw [QuotientGroup.ker_mk', hcard, Sp4Mult.card_multiplier_psp4_two (by omega),
    Nat.dvd_one] at hd
  exact Subgroup.eq_bot_of_card_eq _ hd

end CFSG.Quasithin.H13.Ch4
