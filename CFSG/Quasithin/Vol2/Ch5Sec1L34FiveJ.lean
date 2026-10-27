module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveMain
public import CFSG.Quasithin.EmptyFaithful.S146zYJ1
public import CFSG.Quasithin.EmptyFaithful.S146zYFSJ2
public import CFSG.Sporadic.Schreier.J1Outer
public import CFSG.Sporadic.Schreier.PairJ2Pairs

public section

namespace CFSG.Quasithin.H13.FiveNorm

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint.NativeSporadic

theorem fiveRigid_J1 :
    FiveRigid (Carrier .J1) := by
  have hcard0 : Nat.card (Carrier .J1) = 175560 := CFSG.Sporadic.J1.card_J1
  have : Finite (Carrier .J1) := Nat.finite_of_card_ne_zero (by rw [hcard0]; norm_num)
  have : IsSimpleGroup (Carrier .J1) := CFSG.Sporadic.J1.isSimpleGroup_J1
  have hZ := center_eq_bot_of_card_not_prime (W := Carrier .J1) (by rw [hcard0]; norm_num)
  have hout1 : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer (Carrier .J1)) = 1 :=
    CFSG.Sporadic.Schreier.at_j1_schreier.1
  have hout : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer (Carrier .J1)) ≤ 2 :=
    by rw [hout1]; norm_num
  refine ⟨hZ, fiveInner_of_card_outer_le_two hout, fun S H hS hSH hcard => ?_⟩
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hS8 : Nat.card S = 2 ^ 3 :=
    card_eq_of_isSylowTwoOf_top hS (m := 21945) (by norm_num [hcard0]) (by decide)
  rw [hS8] at hcard
  obtain ⟨⟨y, hyH⟩, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥H) 5
    (by rw [hcard]; exact dvd_mul_right 5 _)
  have hyo : orderOf y = 5 := by rw [← Subgroup.orderOf_mk y hyH]; exact hy
  have hL : CFSG.Quasithin.IsSporadic .J1 ↥(⊤ : Subgroup (Carrier .J1)) :=
    ⟨Subgroup.topEquiv⟩
  refine CFSG.Quasithin.S146zY.j1_no_five (Carrier .J1) ⊤ H S y hL hSH le_top hS ?_ hyH hyo
  intro q hq hqH
  rw [hcard, show 5 * 2 ^ 3 = 2 ^ 3 * 5 by norm_num] at hqH
  rcases (Nat.Prime.dvd_mul hq).mp hqH with h | h
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h))
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp h)

theorem fiveRigid_J2 :
    FiveRigid (Carrier .J2) := by
  have hcard0 : Nat.card (Carrier .J2) = 604800 := CFSG.Sporadic.J2.card_J2
  have : Finite (Carrier .J2) := Nat.finite_of_card_ne_zero (by rw [hcard0]; norm_num)
  have : IsSimpleGroup (Carrier .J2) := CFSG.Sporadic.J2.isSimpleGroup_J2
  have hZ := center_eq_bot_of_card_not_prime (W := Carrier .J2) (by rw [hcard0]; norm_num)
  refine ⟨hZ, fiveInner_of_card_outer_le_two CFSG.Sporadic.Schreier.AT_J2_Schreier.1,
    fun S H hS hSH hcard => ?_⟩
  have hS7 : Nat.card S = 2 ^ 7 :=
    card_eq_of_isSylowTwoOf_top hS (m := 4725) (by norm_num [hcard0]) (by decide)
  rw [hS7] at hcard
  rcases CFSG.Quasithin.S146zY.j2_overgroups ⟨MulEquiv.refl _⟩ hS hSH with
    h | h | h | h | h
  · rw [h, Subgroup.card_top, hcard0] at hcard
    norm_num at hcard
  all_goals (rw [h] at hcard; norm_num at hcard)

theorem fiveRigidJanko_of
    (hJ4 : FiveRigid (Carrier .J4)) : FiveRigidJanko :=
  ⟨fiveRigid_J1, fiveRigid_J2, hJ4⟩

end CFSG.Quasithin.H13.FiveNorm
