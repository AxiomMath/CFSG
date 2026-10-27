module

public import CFSG.Permutation.FiveTransitive.Degree79FiveFixed

public section

namespace CFSG

namespace FiveTransitive.Degree79FiveSevenLift
open MulAction SylowFixedActionCore

theorem exists_seven
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 79)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 5 (fixingSubgroup P s))
    (hS : Nat.card S ≠ 1) : ∃ g : sylowNormalizer X P s S, orderOf g = 7 := by
  classical
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  let F := sylowFixedPoints X P s S
  let N := sylowNormalizer X P s S
  let _ : Fintype F := Fintype.ofFinite _
  let rho := toPermHom N F
  obtain ⟨hF,hAlt⟩ := Degree79FiveFixed.fixed_card_and_alternating P hcard h5 hnotAlt s hs S hS
  change Nat.card F = 9 at hF
  change alternatingGroup F ≤ rho.range at hAlt
  have hd : 7 ∣ Nat.card rho.range :=
    (odd_prime_dvd_alternating_card F (by decide : Nat.Prime 7) (by decide)
      (by rw [← Nat.card_eq_fintype_card,hF]; decide)).trans (Subgroup.card_dvd_of_le hAlt)
  exact exists_prime_orderOf_dvd_card' (G := N) 7 (hd.trans (Subgroup.card_range_dvd rho))

end FiveTransitive.Degree79FiveSevenLift

end CFSG
