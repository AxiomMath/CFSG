module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.AlternatingFourSylowThree
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Normal odd-prime subgroups of `A₄`

A normal subgroup of odd prime-power order in a finite group isomorphic to
`A₄` is trivial.  This is the `A₄` endpoint needed when Dickson's subgroup
classification is applied to an overgroup of a Sylow `2`-subgroup.
-/

namespace CFSG.GorensteinWalter

universe u

/-- A normal odd-prime subgroup of a finite group isomorphic to `A₄` is
trivial. -/
public theorem normal_pSubgroup_eq_bot_of_mulEquiv_alternatingGroup_four
    {G : Type u} [Group G] [Finite G]
    (he : Nonempty (G ≃* alternatingGroup (Fin 4)))
    (p : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (P : Subgroup G) (hPnormal : P.Normal) (hPp : IsPGroup p P) :
    P = ⊥ := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  by_contra hPbot
  have hGcard : Nat.card G = 12 := by
    calc
      Nat.card G = Nat.card (alternatingGroup (Fin 4)) :=
        Nat.card_congr he.some.toEquiv
      _ = 12 := alternatingGroup.card_of_card_eq_four (by simp)
  have hPcard_dvd : Nat.card P ∣ 12 := by
    have hd := Subgroup.card_subgroup_dvd_card P
    simpa [hGcard] using hd
  rcases hPp.exists_card_eq with ⟨n, hn⟩
  have hPcard_ne_one : Nat.card P ≠ 1 := by
    intro hcard
    exact hPbot (Subgroup.eq_bot_of_card_eq (H := P) hcard)
  have hn_ne_zero : n ≠ 0 := by
    intro hn_zero
    apply hPcard_ne_one
    rw [hn, hn_zero, pow_zero]
  have hn_pos : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn_ne_zero)
  have hp_dvd_twelve : p ∣ 12 := by
    apply (show p ∣ Nat.card P from ?_).trans hPcard_dvd
    rw [hn]
    exact dvd_pow_self p (Nat.ne_of_gt hn_pos)
  have hp_eq_three : p = 3 := by
    have hp_ne_two : p ≠ 2 := by
      intro hp_two
      exact hpodd.not_two_dvd_nat (by simp [hp_two])
    have hp_coprime_four : Nat.Coprime p 4 := by
      have hp_coprime_two : Nat.Coprime p 2 :=
        (hp.odd_of_ne_two hp_ne_two).coprime_two_left.symm
      simpa using hp_coprime_two.pow_right 2
    have hp_dvd_three : p ∣ 3 := by
      apply hp_coprime_four.dvd_of_dvd_mul_left
      simpa [pow_two] using hp_dvd_twelve
    rcases (Nat.dvd_prime (p := 3) (m := p) Nat.prime_three).mp hp_dvd_three with
      hp_one | hp_three
    · exact False.elim (hp.ne_one hp_one)
    · exact hp_three
  subst p
  have hPcard_three : Nat.card P = 3 := by
    by_cases hn_one : n = 1
    · simpa [hn_one] using hn
    · exfalso
      have hn_two : 2 ≤ n :=
        Nat.succ_le_iff.mpr (Nat.lt_of_le_of_ne hn_pos (fun h => hn_one h.symm))
      have hnine_dvd : 9 ∣ Nat.card P := by
        rw [hn]
        exact pow_dvd_pow 3 hn_two
      have : 9 ∣ 12 := hnine_dvd.trans hPcard_dvd
      norm_num at this
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPindex : ¬ 3 ∣ P.index := by
    have hmul := P.index_mul_card
    rw [hPcard_three, hGcard] at hmul
    have hPindex_four : P.index = 4 := by omega
    rw [hPindex_four]
    norm_num
  let S : Sylow 3 G := hPp.toSylow hPindex
  have hSnormal : (S : Subgroup G).Normal := by
    simpa [S, IsPGroup.toSylow_coe] using hPnormal
  let : Unique (Sylow 3 G) := Sylow.unique_of_normal S hSnormal
  have hSylow_count_one : Nat.card (Sylow 3 G) = 1 := Nat.card_unique
  have hSylow_count_four : Nat.card (Sylow 3 G) = 4 :=
    sylow_three_card_eq_four_of_mulEquiv_alternatingGroup_four he
  omega

end CFSG.GorensteinWalter
