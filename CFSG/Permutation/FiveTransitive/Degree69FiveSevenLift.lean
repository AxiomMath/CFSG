module

public import CFSG.Permutation.FiveTransitive.Degree69FiveFixed

public section

namespace CFSG

namespace FiveTransitive.Degree69FiveSevenLift
open MulAction SylowFixedActionCore

theorem exists_seven
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 69)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 5 (fixingSubgroup P s))
    (hS : Nat.card S ≠ 1) : ∃ g : sylowNormalizer X P s S, orderOf g = 7 := by
  classical
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  let F := sylowFixedPoints X P s S
  let N := sylowNormalizer X P s S
  let _ : Fintype F := Fintype.ofFinite _
  let rho := toPermHom N F
  obtain ⟨hF,hAlt⟩ := Degree69FiveFixed.fixed_card_and_alternating P hcard h5 hnotAlt s hs S hS
  change Nat.card F = 9 at hF
  change alternatingGroup F ≤ rho.range at hAlt
  have hd : 7 ∣ Nat.card rho.range :=
    (odd_prime_dvd_alternating_card F (by decide : Nat.Prime 7) (by decide)
      (by rw [← Nat.card_eq_fintype_card,hF]; decide)).trans (Subgroup.card_dvd_of_le hAlt)
  exact exists_prime_orderOf_dvd_card' (G := N) 7 (hd.trans (Subgroup.card_range_dvd rho))

theorem card_eq_one_of_seven_free
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 69)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (hseven : ¬ 7 ∣ Nat.card P) (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 5 (fixingSubgroup P s)) : Nat.card S = 1 := by
  by_contra hS
  obtain ⟨g,hg⟩ := exists_seven P hcard h5 hnotAlt s hs S hS
  have hd : 7 ∣ Nat.card (sylowNormalizer X P s S) := hg ▸ orderOf_dvd_natCard g
  exact hseven (hd.trans (Subgroup.card_subgroup_dvd_card (sylowNormalizer X P s S)))

end FiveTransitive.Degree69FiveSevenLift

end CFSG
