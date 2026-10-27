module

public import CFSG.RankThree.PartOne.KS.LyFiveCore
public import CFSG.RankThree.PartOne.KS.PlaneCores
public import CFSG.RankThree.PartOne.KS.Arith
public import CFSG.RankThree.PartOne.SPOR.OuterLy

public section

namespace CFSG.RankThree.PartOne

open CFSG.Sporadic.Ly CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.RankThree.PartOne.LyFive

theorem not_sq_dvd_card_Ly {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hp5 : p ≠ 5) :
    ¬ p ^ 2 ∣ 51765179004000000 := by
  have hs : Nat.Coprime p (2 ^ 8 * 3 ^ 7 * 5 ^ 6) := coprime_two_three_five_pow hp hp3 hp5 8 7 6
  have hN : (51765179004000000 : ℕ) = (2 ^ 8 * 3 ^ 7 * 5 ^ 6) * 5917373 := by norm_num
  rw [hN]
  exact not_sq_dvd_mul_of_coprime hp hs (B := 2432) (by norm_num) (by decide +kernel)
    (by norm_num)

theorem sporadicPlaneOdd_Ly :
    SporadicPlaneOdd (NativeSporadic.Carrier .Ly) := by
  intro T _ _ _ hnab hTA p hp hp3
  obtain ⟨e⟩ := hTA
  have hdvd : Nat.card (Outer T) ∣ 2 :=
    (SPOR.outer_order_divides_two' (T := T) ⟨e⟩).1
  by_cases hp5 : p = 5
  · subst hp5
    have e' : T ≃* J := by exact e.trans lyEquivJ
    have hnd : ¬ 5 ∣ Nat.card (Outer T) := fun h => by
      have := Nat.le_of_dvd (by norm_num) (h.trans hdvd)
      omega
    refine planeLocalCoreOdd_of_cores hp (isPGroup_le_inner_of_not_dvd_card_outer hp hnd)
      (conj_injective_of_center_eq_bot (center_eq_bot_of_simple hnab)) ?_ ?_
    · intro w hw N hNC hNn hNp
      have hc := @fiveCoreAt'_of_equiv T J _ inferInstance e' fiveCore_J w hw
      exact eq_bot_of_fiveCoreAt' hc N hNC hNn hNp
    · have H : ∀ w : J, orderOf w = 5 → ∀ f : J → J, (∀ x y, f (x * y) = f x * f y) →
          (∀ x, f (f x) = x) → (∀ g ∈ Subgroup.centralizer ({w} : Set J), f g = g) →
          ∃ j : J, ∀ x, f x = j * x * j⁻¹ :=
        fun w hw f hmul hinv hfix => hpt_all_J_fun hw hmul hinv hfix
      exact @hpt_of_equiv T J _ inferInstance e' H
  · refine planeLocalCoreOdd_of_not_sq_dvd ?_
    have e0 : NativeSporadic.Carrier .Ly ≃* NativeSporadic.Ly := MulEquiv.refl _
    have hout : Nat.card (Outer (NativeSporadic.Carrier .Ly)) ≤ 2 :=
      Nat.le_of_dvd (by norm_num) (SPOR.outer_order_divides_two' (T := NativeSporadic.Carrier .Ly) ⟨e0⟩).1
    exact not_sq_dvd_card_mulAut_of_outer_le hnab e (N := 51765179004000000) (k := 2)
      CFSG.Sporadic.Ly.card_Ly' hout hp (by omega) (not_sq_dvd_card_Ly hp hp3 hp5)

end CFSG.RankThree.PartOne
