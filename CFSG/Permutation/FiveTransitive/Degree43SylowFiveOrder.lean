module

public import CFSG.Permutation.FiveTransitive.Degree43FiveSylowData
public import CFSG.Permutation.FiveTransitive.Degree43FiveGroupBound
public import CFSG.Permutation.FiveTransitive.Degree43FiveCentralizer
public import CFSG.Permutation.FiveTransitive.Degree39FiveCentralizer
public import CFSG.Permutation.FiveTransitive.FixedNormalizerAction

public section

namespace CFSG

namespace FiveTransitive.Degree43SylowFiveOrder

open MulAction Subgroup SylowFixedActionCore

private theorem sylow_card
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 43)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 5 (fixingSubgroup P s)) (hS : Nat.card S ≠ 1) : Nat.card S = 5 := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  let Q := sylowImage X P s S
  let N := sylowNormalizer X P s S
  let F := sylowFixedPoints X P s S
  let _ : Fintype F := Fintype.ofFinite _
  obtain ⟨hF,hAlt⟩ := Degree43FiveSylowData.five_fixed_card_and_image P hcard h5 hnotAlt s hs S hS
  change Nat.card F = 8 at hF
  have hQ : IsPGroup 5 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hfixeq : (F : Set X) = fixedPoints Q X := FixedNormalizerAction.fixed_eq Q
  have hfixed : Nat.card (fixedPoints Q X) = 8 := by rwa [← hfixeq]
  have hQcard := Degree43FiveGroupBound.card_le_six_hundred_twenty_five P hcard h5 hnotAlt Q hQ hfixed.ge
  let rho : N →* Equiv.Perm F := toPermHom N F
  have hd : 7 ∣ Nat.card rho.range :=
    (odd_prime_dvd_alternating_card F (by decide : Nat.Prime 7) (by decide)
      (by rw [← Nat.card_eq_fintype_card,hF]; decide)).trans (Subgroup.card_dvd_of_le hAlt)
  obtain ⟨g,hg⟩ := exists_prime_orderOf_dvd_card' (G := N) 7
    (hd.trans (Subgroup.card_range_dvd rho))
  have hc := Degree39FiveCentralizer.centralizes Q hQ (by omega) g (hg ▸ pow_orderOf_eq_one g)
  have hle := Degree43FiveCentralizer.card_le_five P hcard h5 hnotAlt Q hQ hfixed g hg hc
  have heq : Nat.card Q = Nat.card S := Subgroup.card_map_of_injective (fixingSubgroup P s).subtype_injective
  rw [heq] at hle
  obtain ⟨e,he⟩ := IsPGroup.iff_card.mp S.isPGroup'
  have hepos : 1 ≤ e := by
    by_contra hn
    exact hS (by rw [he,show e=0 by omega,pow_zero])
  have hge : 5 ≤ Nat.card S := by rw [he]; exact Nat.pow_le_pow_right (by decide : 0 < 5) hepos
  omega

theorem twenty_five_not_dvd_five_fixer_card
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 43)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) : ¬ 25 ∣ Nat.card (fixingSubgroup P s) := by
  let _ : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  intro hd
  let S : Sylow 5 (fixingSubgroup P s) := Sylow.nonempty.some
  have h25 : 25 ∣ Nat.card S := S.pow_dvd_card_of_pow_dvd_card (n := 2) hd
  by_cases hS : Nat.card S = 1
  · rw [hS] at h25
    norm_num at h25
  · rw [sylow_card P hcard h5 hnotAlt s hs S hS] at h25
    norm_num at h25

end FiveTransitive.Degree43SylowFiveOrder

end CFSG
