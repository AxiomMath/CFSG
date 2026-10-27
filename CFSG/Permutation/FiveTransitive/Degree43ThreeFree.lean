module

public import CFSG.Permutation.FiveTransitive.Degree43ThreeSevenLift
public import CFSG.Permutation.FiveTransitive.Degree43SevenFixedElements

public section

namespace CFSG

namespace FiveTransitive.Degree43ThreeFree

open MulAction Subgroup SylowFixedActionCore

private theorem sylow_card_eq_one
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 43)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 3 (fixingSubgroup P s)) : Nat.card S = 1 := by
  by_contra hS
  obtain ⟨z,hz,hfixed⟩ := Degree43ThreeSevenLift.exists_seven_fixed_fifteen
    P hcard h5 hnotAlt s hs S hS
  have hh := Degree43SevenFixedElements.fixed_card_eq_eight P hcard h5 hnotAlt z.val
    ((Subgroup.orderOf_coe z).trans hz) (by rw [hfixed]; norm_num)
  omega

theorem not_dvd_five_fixer
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 43)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) : ¬ 3 ∣ Nat.card (fixingSubgroup P s) := by
  classical
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  intro hd
  obtain ⟨u,hu⟩ := exists_prime_orderOf_dvd_card' (G := fixingSubgroup P s) 3 hd
  have hZ : IsPGroup 3 (zpowers u) := by
    apply IsPGroup.of_card
    rw [Nat.card_zpowers,hu,pow_one]
  obtain ⟨S,hZS⟩ := hZ.exists_le_sylow
  have hSge : 3 ≤ Nat.card S := by
    have h := Subgroup.card_le_of_le hZS
    rwa [Nat.card_zpowers,hu] at h
  have hScard := sylow_card_eq_one P hcard h5 hnotAlt s hs S
  omega

end FiveTransitive.Degree43ThreeFree

end CFSG
