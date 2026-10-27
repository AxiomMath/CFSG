module

public import CFSG.RankThree.PartTwo.Sec4.Item49Tools
import CFSG.RankThree.PartTwo.Sec4.Item47Close
import CFSG.RankThree.PartTwo.Sec4.Item47CoreOut
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearOuterOrder

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.RankThree.PartTwo.Sec4.Item49Tools
open CFSG.ComponentClassification.CatalogueSchreierAlternating
  (outer_card_dvd_two_of_equiv_outside_six)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  (higher_linear_outer_order_divides_field_gcd_bound)

namespace Item49Small

theorem finite_outer (X : Type*) [Group X] [Finite X] : Finite (Outer X) := by
  have : Finite (MulAut X) := MulEquiv.finite_left
  infer_instance

theorem odd_of_not_three_dvd {X : Type*} [Group X] [Finite X]
    (h : ¬ 3 ∣ Nat.card (Outer X)) : Odd (Nat.card (oThreePrime (Outer X))) := by
  have := finite_outer X
  exact odd_card_oThreePrime_of_not_dvd h

theorem not_three_dvd_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : ¬ 3 ∣ Nat.card (Outer Y)) : ¬ 3 ∣ Nat.card (Outer X) := by
  rwa [Nat.card_congr (equivalence e).toEquiv]

theorem odd_of_center_quotient {X Y : Type*} [Group X] [Group Y] [Finite X]
    (hq : CFSG.IsQuasisimple X) (e : X ⧸ Subgroup.center X ≃* Y)
    (h : ¬ 3 ∣ Nat.card (Outer Y)) : Odd (Nat.card (oThreePrime (Outer X))) := by
  have : Group.IsPerfect X := hq.1
  have := finite_outer (X ⧸ Subgroup.center X)
  exact odd_card_oThreePrime_outer_of_center X
    (odd_of_not_three_dvd (not_three_dvd_of_mulEquiv e h))

theorem odd_of_isExtOf {X Y : Type*} [Group X] [Group Y] [Finite X]
    (hq : CFSG.IsQuasisimple X) (hY : Subgroup.center Y = ⊥)
    (h : IsExtOf X Y (Multiplicative (ZMod 3))) (hY3 : ¬ 3 ∣ Nat.card (Outer Y)) :
    Odd (Nat.card (oThreePrime (Outer X))) := by
  obtain ⟨-, ⟨e⟩⟩ := (isTripleCover_iff_isExtOf hq hY).mpr h
  exact odd_of_center_quotient hq e hY3

theorem not_three_dvd_card_outer_alternating {X : Type*} [Group X] {n : ℕ} (hn : 5 ≤ n)
    (e : X ≃* alternatingGroup (Fin n)) : ¬ 3 ∣ Nat.card (Outer X) := by
  rcases (show n = 6 ∨ n = 5 ∨ 7 ≤ n by omega) with rfl | h
  · exact CFSG.Quasithin.A10.three_not_dvd_card_outer e
  · intro h3
    have h2 := outer_card_dvd_two_of_equiv_outside_six h e
    have := Nat.le_of_dvd (by norm_num) (h3.trans h2)
    omega

theorem not_three_dvd_card_outer_projSL {n e : ℕ} (hn : 3 ≤ n) (he : 1 ≤ e)
    (h : ¬ 3 ∣ 2 * e * Nat.gcd n (3 ^ e - 1)) :
    ¬ 3 ∣ Nat.card (Outer (projSL n (GaloisField 3 e))) := by
  intro h3
  have hd := higher_linear_outer_order_divides_field_gcd_bound Nat.prime_three he hn
    (GaloisField.card 3 e (by omega))
  rw [Nat.card_congr (equivalence (projSLEquivProjectiveSL n (GaloisField 3 e))).toEquiv] at h3
  exact h (h3.trans hd)

theorem not_three_dvd_card_outer_projSU {n e : ℕ} (hn : 3 ≤ n) (he : 1 ≤ e)
    (h : ¬ 3 ∣ 2 * e * (3 ^ e + 1)) : ¬ 3 ∣ Nat.card (Outer (projSU n 3 e)) := by
  intro h3
  refine h (h3.trans (card_outer_projSU_dvd n 3 e he hn ?_))
  rintro ⟨-, h2⟩
  have : 3 ^ 1 ≤ 3 ^ e := Nat.pow_le_pow_right (by norm_num) he
  omega

end Item49Small

open Item49Small

theorem oddOThreePrime_four (X : Type) [Group X] [Finite X]
    (hX : (∃ n : ℕ, n ≤ 9 ∧ Nonempty (X ≃* alternatingGroup (Fin n))) ∨
      IsExtOf X (alternatingGroup (Fin 6)) (Multiplicative (ZMod 3)) ∨
      IsExtOf X (alternatingGroup (Fin 7)) (Multiplicative (ZMod 3)))
    (hq : CFSG.IsQuasisimple X) : Odd (Nat.card (oThreePrime (Outer X))) := by
  rcases hX with ⟨n, -, ⟨e⟩⟩ | h6 | h7
  · rcases Nat.lt_or_ge n 5 with hn | hn
    · exfalso
      have : Group.IsSolvable (alternatingGroup (Fin n)) :=
        isSolvable_alternatingGroup_of_le_four (by omega)
      exact false_of_isQuasisimple_of_isSolvable hq
        (Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective)
    · exact odd_of_not_three_dvd (not_three_dvd_card_outer_alternating hn e)
  · exact odd_of_isExtOf hq (alternatingGroup.center_eq_bot (by simp)) h6
      (not_three_dvd_card_outer_alternating (by norm_num) (MulEquiv.refl _))
  · exact odd_of_isExtOf hq (alternatingGroup.center_eq_bot (by simp)) h7
      (not_three_dvd_card_outer_alternating (by norm_num) (MulEquiv.refl _))

section Sporadic


theorem oddOThreePrime_five (X : Type) [Group X] [Finite X]
    (hX : (∃ s ∈ sporadics46, Nonempty (X ≃* Blueprint.NativeSporadic.Carrier s)) ∨
      ∃ s ∈ sporadicCovers46,
        IsExtOf X (Blueprint.NativeSporadic.Carrier s) (Multiplicative (ZMod 3)))
    (hq : CFSG.IsQuasisimple X) : Odd (Nat.card (oThreePrime (Outer X))) := by
  have hout := not_three_dvd_card_outer_sporadic46 inputs47Core_outJ4 inputs47Core_outON
  rcases hX with ⟨s, hs, ⟨e⟩⟩ | ⟨s, hs, h⟩
  · exact odd_of_not_three_dvd (not_three_dvd_of_mulEquiv e (hout s (Or.inl hs)))
  · exact odd_of_isExtOf hq (center_carrier_eq_bot_of_cover hs) h (hout s (Or.inr hs))

end Sporadic

section CharThree


theorem oddOThreePrime_eight (X : Type) [Group X] [Finite X]
    (hX : (∃ e : ℕ, 1 ≤ e ∧ e ≤ 2 ∧
        (Nonempty (X ≃* projSL 3 (GaloisField 3 e)) ∨ Nonempty (X ≃* projSU 3 3 e))) ∨
      Nonempty (X ≃* projSL 4 (GaloisField 3 1)) ∨
      (Nat.card (Subgroup.center X) ≤ 3 ∧
        (Blueprint.ChevalleyExceptionalModel (X ⧸ Subgroup.center X) .G2 3 1 ∨
          Nonempty (X ⧸ Subgroup.center X ≃* projSU 4 3 1))))
    (hq : CFSG.IsQuasisimple X) : Odd (Nat.card (oThreePrime (Outer X))) := by
  rcases hX with ⟨e, he1, he2, ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩⟩ | ⟨⟨f⟩⟩ | ⟨-, hG | ⟨⟨f⟩⟩⟩
  · refine odd_of_not_three_dvd (not_three_dvd_of_mulEquiv f
      (not_three_dvd_card_outer_projSL le_rfl he1 ?_))
    interval_cases e <;> norm_num
  · refine odd_of_not_three_dvd (not_three_dvd_of_mulEquiv f
      (not_three_dvd_card_outer_projSU le_rfl he1 ?_))
    interval_cases e <;> norm_num
  · exact odd_of_not_three_dvd (not_three_dvd_of_mulEquiv f
      (not_three_dvd_card_outer_projSL (n := 4) (e := 1) (by norm_num) le_rfl
        (by norm_num)))
  · exact odd_of_center_quotient hq (MulEquiv.refl _) (inputs47Core_outG23 _ hG)
  · exact odd_of_center_quotient hq f outU43_holds

end CharThree

end CFSG.RankThree.PartTwo.Sec4
