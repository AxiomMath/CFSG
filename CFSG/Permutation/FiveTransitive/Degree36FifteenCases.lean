module

public import CFSG.Permutation.FiveTransitive.Degree36FiveFixerArithmetic
public import CFSG.Permutation.FiveTransitive.Degree36SylowThreeSharp

public section

namespace CFSG

namespace FiveTransitive.Degree36FifteenCases

open MulAction Degree36FiveFixerNumeric

theorem card_exponents_mem
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 36)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    ∃ a b c : ℕ, (a,b,c) ∈ allowedTriplesFour ∧
      Nat.card (fixingSubgroup P s) = 2^a * 3^b * 5^c ∧
      Nat.card P = 45239040 * 2^a * 3^b * 5^c := by
  classical
  let _ : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨a,b,c,hm,hH,hP⟩ := Degree36FiveFixerArithmetic.card_exponents_mem P hcard h5 hnotAlt s hs
  have hb : b ≤ 4 := by
    by_contra hn
    let S : Sylow 3 (fixingSubgroup P s) := Sylow.nonempty.some
    have hd : 3^5 ∣ Nat.card (fixingSubgroup P s) := by
      rw [hH]
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (pow_dvd_pow 3 (by omega : 5 ≤ b)) _) _
    have hdS : 243 ∣ Nat.card S := S.pow_dvd_card_of_pow_dvd_card (n := 5) hd
    have hlow := Nat.le_of_dvd Nat.card_pos hdS
    have hu := Degree36SylowThreeSharp.card_le_eighty_one P hcard h5 hnotAlt s hs S
    omega
  exact ⟨a,b,c,mem_four hm hb,hH,hP⟩

end FiveTransitive.Degree36FifteenCases

end CFSG
