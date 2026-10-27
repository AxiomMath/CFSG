module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3Core
public import CFSG.CharacterTheory.Burnside
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.G2A5
public import CFSG.Quasithin.Vol2.Ch10SecD33E

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model

theorem isSolvable_of_card_dvd_sixty {X : Type} [Group X] [Finite X] (hd : Nat.card X ∣ 60)
    (hle : Nat.card X ≤ 12) : Group.IsSolvable X := by
  have : Fintype X := Fintype.ofFinite X
  have key : ∀ (p q a b : ℕ), p.Prime → q.Prime → p ≠ q → Nat.card X = p ^ a * q ^ b →
      Group.IsSolvable X := fun p q a b hp hq hpq h =>
    CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := a) (b := b)
      hp hq hpq (by rw [← Nat.card_eq_fintype_card]; exact h)
  have hpos : 0 < Nat.card X := Nat.card_pos
  interval_cases h : Nat.card X
  · exact key 2 3 0 0 Nat.prime_two Nat.prime_three (by norm_num) (by norm_num)
  · exact key 2 3 1 0 Nat.prime_two Nat.prime_three (by norm_num) (by norm_num)
  · exact key 2 3 0 1 Nat.prime_two Nat.prime_three (by norm_num) (by norm_num)
  · exact key 2 3 2 0 Nat.prime_two Nat.prime_three (by norm_num) (by norm_num)
  · exact key 2 5 0 1 Nat.prime_two (by norm_num) (by norm_num) (by norm_num)
  · exact key 2 3 1 1 Nat.prime_two Nat.prime_three (by norm_num) (by norm_num)
  · norm_num at hd
  · norm_num at hd
  · norm_num at hd
  · exact key 2 5 1 1 Nat.prime_two (by norm_num) (by norm_num) (by norm_num)
  · norm_num at hd
  · exact key 2 3 2 1 Nat.prime_two Nat.prime_three (by norm_num) (by norm_num)

theorem eq_top_of_perfect_alt5 {R : Subgroup (alternatingGroup (Fin 5))} (hR : ⁅R, R⁆ = R)
    (hne : R ≠ ⊥) : R = ⊤ := by
  by_contra htop
  have hsimple : IsSimpleGroup (alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin])
  have h60 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide
  have hcore : R.normalCore = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal R.normalCore with h | h
    · exact h
    · exact absurd (top_le_iff.mp (h ▸ R.normalCore_le)) htop
  have hdvd := R.index_normalCore_dvd_factorial_index
  rw [hcore, Subgroup.index_bot, h60] at hdvd
  have hidx : 5 ≤ R.index := by
    by_contra hlt
    push Not at hlt
    have hpos : 0 < R.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
    interval_cases h : R.index <;> norm_num [Nat.factorial] at hdvd
  have hcard : Nat.card R * R.index = 60 := by rw [Subgroup.card_mul_index, h60]
  have hle : Nat.card R ≤ 12 := by nlinarith
  have hsolv : Group.IsSolvable ↥R := isSolvable_of_card_dvd_sixty ⟨R.index, hcard.symm⟩ hle
  have : Group.IsPerfect ↥R := Subgroup.isPerfect_iff.mpr hR
  have : Nontrivial ↥R := (Subgroup.nontrivial_iff_ne_bot R).mpr hne
  exact Group.IsPerfect.not_isSolvable (G := ↥R) hsolv

end CFSG.Quasithin.H13.A5
