module

public import CFSG.Permutation.FiveTransitive.Degree80ThreeNoSixFixed
public import CFSG.Permutation.FiveTransitive.Degree80ThreeOrbitAlternatives
public import CFSG.Permutation.FiveTransitive.Degree68ThreeBoundCore

public section

namespace CFSG

namespace FiveTransitive.Degree80ThreeCyclic
open MulAction SylowFixedActionCore

theorem sylow_card_le_three
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 80)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 3 (fixingSubgroup P s)) : Nat.card S ≤ 3 := by
  classical
  by_cases hS : Nat.card S = 1
  · omega
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  let Q := sylowImage X P s S
  let F := sylowFixedPoints X P s S
  let _ : Fintype F := Fintype.ofFinite _
  have hQ : IsPGroup 3 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hF := (Degree80ThreeFixed.three_fixed_card_and_image P hcard h5 hnotAlt s hs S hS).1
  have hcommon : Nat.card (fixedPoints Q X) = 5 := by
    rw [← FixedNormalizerAction.fixed_eq Q]
    exact hF
  obtain ⟨x,hx⟩ := Degree80ThreeOrbitAlternatives.exists_triple P hcard h5 hnotAlt s hs S hS
  have he := Degree68ThreeBoundCore.card_eq_three_of_triple P
    (Degree80ThreeNoSixFixed.card_eq_one_of_six_fixed P hcard h5 hnotAlt) Q hQ hcommon x hx
  have hQcard : Nat.card Q = Nat.card S := Nat.card_congr
    ((S : Subgroup (fixingSubgroup P s)).equivMapOfInjective
      (fixingSubgroup P s).subtype Subtype.val_injective).toEquiv.symm
  omega

theorem pow_dvd_five_fixer_le_one
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 80)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (b : ℕ)
    (hb : 3 ^ b ∣ Nat.card (fixingSubgroup P s)) : b ≤ 1 := by
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  let S : Sylow 3 (fixingSubgroup P s) := Sylow.nonempty.some
  have hd : 3 ^ b ∣ Nat.card S := S.pow_dvd_card_of_pow_dvd_card hb
  have hl := Nat.le_of_dvd (show 0 < Nat.card S from Nat.card_pos) hd
  have hu := sylow_card_le_three P hcard h5 hnotAlt s hs S
  by_contra hn
  have hh := Nat.pow_le_pow_right (by decide : 0 < 3) (by omega : 2 ≤ b)
  norm_num at hh hu
  omega

end FiveTransitive.Degree80ThreeCyclic

end CFSG
