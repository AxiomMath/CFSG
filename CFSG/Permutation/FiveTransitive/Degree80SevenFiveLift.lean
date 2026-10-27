module

public import CFSG.Permutation.FiveTransitive.Degree80LargePrimeFixed

public section

namespace CFSG

namespace FiveTransitive.Degree80SevenFiveLift
open MulAction SylowFixedActionCore

theorem exists_normalizer_five
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 80)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 7 (fixingSubgroup P s)) (hS : Nat.card S ≠ 1) :
    ∃ g : sylowNormalizer X P s S, orderOf g = 5 ∧
      Nat.card (Function.fixedPoints g.val.val) ≤ 40 := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let N := sylowNormalizer X P s S
  let F := sylowFixedPoints X P s S
  let _ : Fintype F := Fintype.ofFinite F
  obtain ⟨hlo,hhi,hN5⟩ := Degree80LargePrimeFixed.bounds_and_transitive
    7 (by decide) P hcard h5 hnotAlt s hs S hS
  have htuple : (Nat.card F).descFactorial 5 ∣ Nat.card N := by
    simpa only [Nat.card_eq_fintype_card] using
      (FiveTransitive.descFactorial_dvd_card_of_isMultiplyPretransitive N F 5
        (by simpa only [Nat.card_eq_fintype_card] using hlo) hN5)
  have hd : 5 ∣ (Nat.card F).descFactorial 5 :=
    (by decide : 5 ∣ Nat.factorial 5).trans (Nat.factorial_dvd_descFactorial _ _)
  obtain ⟨g,hg⟩ := exists_prime_orderOf_dvd_card' (G := N) 5 (hd.trans htuple)
  have hgP : orderOf g.val = 5 := (Subgroup.orderOf_coe g).trans hg
  have hgperm : orderOf g.val.val = 5 := (Subgroup.orderOf_coe g.val).trans hgP
  have hne : g.val.val ≠ 1 := by intro he; rw [he,orderOf_one] at hgperm; omega
  have hb := HighDegreeManningSupport.degree_le_two_mul_support P (by omega) h5
    hnotAlt g.val.property hne
  rw [hcard] at hb
  refine ⟨g,hg,?_⟩
  rw [Nat.card_eq_fintype_card,Equiv.Perm.card_fixedPoints,g.val.val.sum_cycleType,hcard]
  omega

end FiveTransitive.Degree80SevenFiveLift

end CFSG
