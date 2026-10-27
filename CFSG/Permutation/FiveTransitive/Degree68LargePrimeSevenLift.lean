module

public import CFSG.Permutation.FiveTransitive.Degree68LargePrimeAlternating

public section

namespace CFSG

namespace FiveTransitive.Degree68LargePrimeSevenLift
open MulAction SylowFixedActionCore

theorem seven_dvd_normalizer
    {X : Type} [Fintype X] [DecidableEq X]
    (p : ℕ) (hp : p.Prime)
    (hcases : p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 23 ∨ p = 29)
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 68)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow p (fixingSubgroup P s)) (hS : Nat.card S ≠ 1) :
    7 ∣ Nat.card (sylowNormalizer X P s S) := by
  classical
  let _ : Fact p.Prime := ⟨hp⟩
  let F := sylowFixedPoints X P s S
  let N := sylowNormalizer X P s S
  let _ : Fintype F := Fintype.ofFinite _
  let rho := toPermHom N F
  let J := rho.range
  obtain ⟨hlo,hhi,hN5⟩ := Degree68LargePrimeFixed.bounds_and_transitive p hp P hcard h5 hnotAlt s hs S hS
  change 5 ≤ Nat.card F at hlo
  change Nat.card F ≤ 34 at hhi
  have hm := SylowFixedActionPrimeFree.fixed_degree_modEq X P s S
  change Nat.card X % p = Nat.card F % p at hm
  rw [Nat.card_eq_fintype_card,hcard] at hm
  by_cases h24 : Nat.card F = 24
  · have hd := FiveTransitive.descFactorial_dvd_card_of_isMultiplyPretransitive N F 5
      (by rw [← Nat.card_eq_fintype_card]; exact hlo) hN5
    rw [← Nat.card_eq_fintype_card,h24] at hd
    exact (show 7 ∣ (24 : ℕ).descFactorial 5 by norm_num).trans hd
  have hJ5 : IsMultiplyPretransitive J F 5 := by
    constructor
    intro a b
    obtain ⟨g,hg⟩ := hN5.exists_smul_eq a b
    exact ⟨⟨rho g,⟨g,rfl⟩⟩,hg⟩
  have hAlt : alternatingGroup F ≤ J := by
    by_cases h11 : p = 11
    · have h13 : Nat.card F = 13 := by subst p; omega
      apply SmallDegreeFixedAction.alternatingGroup_le_of_card_le_twentySeven_away_mathieu F J
      · rw [← Nat.card_eq_fintype_card,h13]; decide
      · rw [← Nat.card_eq_fintype_card,h13]; decide
      · rw [← Nat.card_eq_fintype_card,h13]; decide
      · rw [← Nat.card_eq_fintype_card,h13]; decide
      · intro a b ha hb
        obtain ⟨g,hg⟩ := hJ5.exists_smul_eq (⟨a,ha⟩ : Fin 5 ↪ F) ⟨b,hb⟩
        exact ⟨g,fun i => DFunLike.congr_fun hg i⟩
    · have hc : p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 23 ∨ p = 29 ∨ p = 31 := by tauto
      exact Degree68LargePrimeAlternating.alternating_image p hp hc P hcard h5 hnotAlt s hs S hS
  have h7F : 7 ≤ Fintype.card F := by
    rw [← Nat.card_eq_fintype_card]
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have hd : 7 ∣ Nat.card J :=
    (odd_prime_dvd_alternating_card F (by decide : Nat.Prime 7) (by decide) h7F).trans
      (Subgroup.card_dvd_of_le hAlt)
  exact hd.trans (Subgroup.card_range_dvd rho)

end FiveTransitive.Degree68LargePrimeSevenLift

end CFSG
