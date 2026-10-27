module

public import CFSG.Permutation.FiveTransitive.FixedNormalizerAction
public import CFSG.Permutation.FiveTransitive.Degree80FiveTupleBound
public import CFSG.Permutation.FiveTransitive.SylowTwoFixedDegreeBounded

public section

namespace CFSG

namespace FiveTransitive.Degree80TwoBound
open MulAction SylowFixedActionCore

theorem fixed_card_cases
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 80)
    (h5 : IsMultiplyPretransitive P X 5)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 2 (fixingSubgroup P s)) :
    Nat.card (sylowFixedPoints X P s S) = 6 ∨
      Nat.card (sylowFixedPoints X P s S) = 8 ∨
      Nat.card (sylowFixedPoints X P s S) = 12 := by
  let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hlo := SylowFixedActionPrimeFree.base_card_le_fixed_degree X P s S
  rw [hs] at hlo
  have hb := SylowTwoFixedDegreeBounded.fixed_degree_le_eight_or_eq_twelve X P h5 s hs S
  have hm := SylowFixedActionPrimeFree.fixed_degree_modEq X P s S
  change Nat.card X % 2 = Nat.card (sylowFixedPoints X P s S) % 2 at hm
  rw [Nat.card_eq_fintype_card,hcard] at hm
  omega

theorem sylow_card_le
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 80)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 2 (fixingSubgroup P s)) :
    Nat.card S ≤ 2^36 := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
  let Q := sylowImage X P s S
  have hQ : IsPGroup 2 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hfixed : 6 ≤ Nat.card (fixedPoints Q X) := by
    rw [← FixedNormalizerAction.fixed_eq Q]
    have hh := fixed_card_cases P hcard h5 s hs S
    change Nat.card (FixedNormalizerAction.Fixed (X := X) Q) = 6 ∨
      Nat.card (FixedNormalizerAction.Fixed (X := X) Q) = 8 ∨
      Nat.card (FixedNormalizerAction.Fixed (X := X) Q) = 12 at hh
    omega
  have hd := Degree80FiveTupleBound.card_dvd_exterior_tuples
    P hcard h5 hnotAlt Q 6 35 (by norm_num) hfixed
  obtain ⟨a,ha⟩ := IsPGroup.iff_card.mp hQ
  have habound : a ≤ 36 := by
    by_contra hn
    have hp : 2^37 ∣ Nat.card Q := by
      rw [ha]
      exact pow_dvd_pow 2 (by omega)
    have hc := hp.trans hd
    norm_num [Nat.descFactorial] at hc
  have hQcard : Nat.card Q = Nat.card S :=
    Subgroup.card_map_of_injective (fixingSubgroup P s).subtype_injective
  rw [← hQcard,ha]
  exact Nat.pow_le_pow_right (by decide) habound

end FiveTransitive.Degree80TwoBound

end CFSG
