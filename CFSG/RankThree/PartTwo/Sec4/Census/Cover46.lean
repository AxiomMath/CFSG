module

public import CFSG.RankThree.PartTwo.Sec4.Census.Open46
public import CFSG.RankThree.PartTwo.Sec4.Census.Lift46
import CFSG.RankThree.PartTwo.Sec4.Census.Witness46
import CFSG.RankThree.PartTwo.Sec4.Census.FromTheoremThree
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface46

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4 TauCeti
open CFSG.Assembly.RankThreeEven (projSL projSU localRank)

abbrev Conclusion43 (X : Type) [Group X] : Prop :=
  (∃ (p e : ℕ) (_ : Fact p.Prime), 1 ≤ e ∧ IsoLThreePi (X ⧸ Subgroup.center X) p e) ∨
    Nonempty (X ⧸ Subgroup.center X ≃* alternatingGroup (Fin 6)) ∨
    Nonempty (X ⧸ Subgroup.center X ≃* alternatingGroup (Fin 7)) ∨
    Blueprint.ChevalleyExceptionalModel (X ⧸ Subgroup.center X) .G2 3 1 ∨
    Nonempty (X ⧸ Subgroup.center X ≃* projSU 4 3 1) ∨
    Nonempty (X ⧸ Subgroup.center X ≃* Blueprint.NativeSporadic.M22) ∨
    Nonempty (X ⧸ Subgroup.center X ≃* Blueprint.NativeSporadic.J3) ∨
    Nonempty (X ⧸ Subgroup.center X ≃* Blueprint.NativeSporadic.McL) ∨
    Nonempty (X ⧸ Subgroup.center X ≃* Blueprint.NativeSporadic.ON)

theorem three_pow_mod_three {e : ℕ} (he : 1 ≤ e) : 3 ^ e % 3 = 0 :=
  Nat.mod_eq_zero_of_dvd (dvd_pow_self 3 (by omega))

theorem two_or_le_two_of_isoLThreePi {S : Type} [Group S] [Finite S] (hS : SectionFourHyp S)
    {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e) (hpi : IsoLThreePi S p e) : p = 2 ∨ e ≤ 2 := by
  by_cases hp2 : p = 2
  · exact Or.inl hp2
  · right
    by_cases hp3 : p = 3
    · subst hp3
      exfalso
      have h0 := three_pow_mod_three he
      rcases hpi with ⟨h1, -⟩ | ⟨h2, -⟩ <;> omega
    · have hp : 3 < p := three_lt_of_prime Fact.out hp2 hp3
      by_contra he3
      rcases hpi with ⟨-, ⟨f⟩⟩ | ⟨-, ⟨f⟩⟩
      · exact SectionFourHyp.false_of_three_le_localRank hS f Fact.out hp
          (le_trans (by omega) (le_localRank_projSL_three hp2 he))
      · exact SectionFourHyp.false_of_three_le_localRank hS f Fact.out hp
          (le_trans (by omega) (le_localRank_projSU_three hp2 he))

theorem isList46_of_cover {X : Type} [Group X] [Finite X] (hX : SectionFourHyp X)
    (hS : SectionFourHyp (X ⧸ Subgroup.center X)) (hq : IsQuasisimple X)
    (hZ3 : IsPGroup 3 (Subgroup.center X)) (hZ : Subgroup.center X ≠ ⊥) (hin : CoverInputs46)
    (h : Conclusion43 X) : IsList46 X := by
  have hc1 : Nat.card (Subgroup.center X) ≠ 1 := fun h1 => hZ (Subgroup.card_eq_one.mp h1)
  have hc3 : Nat.card (Subgroup.center X) ∣ 3 → Nat.card (Subgroup.center X) = 3 := by
    intro h3
    rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h | h
    · exact absurd h hc1
    · exact h
  have htc : ∀ {Y : Type} [Group Y], Nonempty (X ⧸ Subgroup.center X ≃* Y) →
      Nat.card (Subgroup.center X) ∣ 3 → IsExtOf X Y (Multiplicative (ZMod 3)) :=
    fun hY h3 => IsTripleCover.isExtOf ⟨hc3 h3, hY⟩
  have hcen := hin.centerThree X hq hZ3
  rcases h with ⟨p, e, _, he, hpi⟩ | hA6 | hA7 | hG2 | hU43 | hM22 | hJ3 | hMcL | hON
  · have hbd := two_or_le_two_of_isoLThreePi hS he hpi
    have hsl := hin.slThree X hq hZ3 hZ p e he hbd hpi
    by_cases hp2 : p = 2
    · subst hp2
      exact IsList46.six_SL3 he hsl
    · by_cases hp3 : p = 3
      · subst hp3
        exfalso
        have h0 := three_pow_mod_three he
        rcases hpi with ⟨h1, -⟩ | ⟨h2, -⟩ <;> omega
      · exact IsList46.two_SLeps p e (three_lt_of_prime Fact.out hp2 hp3) he
          (hbd.resolve_left hp2) hsl
  · exact IsList46.four_A6 (htc hA6 (hcen (Or.inl hA6)))
  · exact IsList46.four_A7 (htc hA7 (hcen (Or.inr (Or.inl hA7))))
  · exact IsList46.eight_G23 (Nat.le_of_dvd (by norm_num) (hcen (Or.inr (Or.inr (Or.inl hG2)))))
      hG2
  · obtain ⟨f⟩ := hU43
    have h9 := hin.u43 X hq hZ3 ⟨f⟩
    have hne9 : Nat.card (Subgroup.center X) ≠ 9 := fun h9' => by
      have h4 := hin.u43Rank X hq h9' ⟨f⟩
      have h3 := SectionFourHyp.localRank_three_le hX
      omega
    refine IsList46.eight_U43 ?_ f
    obtain ⟨i, hi, hci⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
      (show Nat.card (Subgroup.center X) ∣ 3 ^ 2 from h9)
    interval_cases i
    · rw [hci]
      norm_num
    · rw [hci]
      norm_num
    · exact absurd hci hne9
  · exact IsList46.five_cover (s := .M22) (by decide)
      (htc hM22 (hcen (Or.inr (Or.inr (Or.inr (Or.inl hM22))))))
  · exact IsList46.five_cover (s := .J3) (by decide)
      (htc hJ3 (hcen (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hJ3)))))))
  · exact IsList46.five_cover (s := .McL) (by decide)
      (htc hMcL (hcen (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hMcL))))))))
  · exact IsList46.five_cover (s := .ONan) (by decide)
      (htc hON (hcen (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hON))))))))

end CFSG.RankThree.PartTwo.Sec4.Census
