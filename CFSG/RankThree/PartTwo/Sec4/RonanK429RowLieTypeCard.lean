module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429Cfg
public import CFSG.RankThree.PartTwo.KFacts.KS14Orders
public import CFSG.RankThree.PartTwo.Sec13.Item13Models
public import CFSG.RankThree.PartTwo.Sec4.RonanK429Rows

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429Lie

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.KFacts
open CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.Assembly.RankThreeEven (projSL projSU)

theorem card_alternatingGroup_seven : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  decide

theorem card_of_isType429 {X : Type} [Group X] (h : IsType429 X) :
    (∃ p e : ℕ, p.Prime ∧ p ≠ 3 ∧ 1 ≤ e ∧
      ((p ^ e % 3 = 1 ∧ Nat.card X * 3 = (p ^ e) ^ 3 * (((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 - 1))) ∨
        (p ^ e % 3 = 2 ∧ Nat.card X * 3 = (p ^ e) ^ 3 * (((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 + 1)) ∧
          (p ^ e = 2 → Group.IsSolvable X)))) ∨
      Nat.card X = 2520 ∨ Nat.card X = 95040 ∨ Nat.card X = 443520 ∨ Nat.card X = 604800 := by
  rcases h with ⟨p, e, hp, he, hiso⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
  · left
    have hpp : p.Prime := hp.out
    have hp3 : p ≠ 3 := by
      rintro rfl
      have h0 : 3 ^ e % 3 = 0 := Nat.mod_eq_zero_of_dvd (dvd_pow_self 3 (by omega))
      rcases hiso with ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega
    refine ⟨p, e, hpp, hp3, he, ?_⟩
    rcases hiso with ⟨hq, ⟨φ⟩⟩ | ⟨hq, ⟨φ⟩⟩
    · left
      refine ⟨hq, ?_⟩
      have hc := KS14.card_projSL_three_mul_gcd (GaloisField p e)
      rw [GaloisField.card p e (by omega)] at hc
      have hg : Nat.gcd 3 (p ^ e - 1) = 3 := by
        refine Nat.gcd_eq_left ?_
        have : 1 ≤ p ^ e := Nat.one_le_pow _ _ hpp.pos
        omega
      rw [hg, ← Nat.card_congr φ.toEquiv] at hc
      exact hc
    · right
      refine ⟨hq, ?_, fun h2 => ?_⟩
      · have hc := KS14.card_projSU_three_mul_gcd p e he
        have hg : Nat.gcd 3 (p ^ e + 1) = 3 := Nat.gcd_eq_left (by omega)
        rw [hg, ← Nat.card_congr φ.toEquiv] at hc
        exact hc
      · obtain ⟨rfl, rfl⟩ := Sec13.eq_two_one_of_pow_eq_two hpp h2
        have := Sec13.isSolvable_projSU_two
        exact Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective
  · right; left
    rw [Nat.card_congr φ.toEquiv, card_alternatingGroup_seven]
  · right; right; left
    rw [Nat.card_congr φ.toEquiv, KS14.card_nativeM12]
  · right; right; right; left
    rw [Nat.card_congr φ.toEquiv, KS14.card_nativeM22]
  · right; right; right; right
    rw [Nat.card_congr φ.toEquiv, KS14.card_nativeJ2]

end CFSG.RankThree.PartTwo.Sec4.RonanK429Lie
