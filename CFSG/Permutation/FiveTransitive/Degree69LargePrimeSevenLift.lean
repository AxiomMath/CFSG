module

public import CFSG.Permutation.FiveTransitive.Degree69LargePrimeFixed

public section

namespace CFSG

namespace FiveTransitive.Degree69LargePrimeSevenLift
open MulAction SylowFixedActionCore

theorem seven_dvd_normalizer
    {X : Type} [Fintype X] [DecidableEq X]
    (p : ℕ) (hp : p.Prime)
    (hcases : p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 23 ∨ p = 29 ∨ p = 31)
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 69)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow p (fixingSubgroup P s)) (hS : Nat.card S ≠ 1)
    (h12 : Nat.card (sylowFixedPoints X P s S) ≠ 12) :
    7 ∣ Nat.card (sylowNormalizer X P s S) := by
  classical
  let _ : Fact p.Prime := ⟨hp⟩
  let F := sylowFixedPoints X P s S
  let N := sylowNormalizer X P s S
  let _ : Fintype F := Fintype.ofFinite _
  obtain ⟨hlo,hhi,hN5⟩ := Degree69LargePrimeFixed.bounds_and_transitive p hp P hcard h5 hnotAlt s hs S hS
  change 5 ≤ Nat.card F at hlo
  change Nat.card F ≤ 34 at hhi
  have hm := SylowFixedActionPrimeFree.fixed_degree_modEq X P s S
  change Nat.card X % p = Nat.card F % p at hm
  rw [Nat.card_eq_fintype_card,hcard] at hm
  have hd := FiveTransitive.descFactorial_dvd_card_of_isMultiplyPretransitive N F 5
    (by rw [← Nat.card_eq_fintype_card]; exact hlo) hN5
  rw [← Nat.card_eq_fintype_card] at hd
  apply (show 7 ∣ (Nat.card F).descFactorial 5 from ?_).trans hd
  change Nat.card F ≠ 12 at h12
  have hF : Nat.card F = 7 ∨ Nat.card F = 11 ∨ Nat.card F = 14 ∨
      Nat.card F = 17 ∨ Nat.card F = 18 ∨ Nat.card F = 23 ∨
      Nat.card F = 25 ∨ Nat.card F = 30 ∨ Nat.card F = 31 := by
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  rcases hF with hF | hF | hF | hF | hF | hF | hF | hF | hF <;>
    rw [hF] <;> norm_num [Nat.descFactorial]

end FiveTransitive.Degree69LargePrimeSevenLift

end CFSG
