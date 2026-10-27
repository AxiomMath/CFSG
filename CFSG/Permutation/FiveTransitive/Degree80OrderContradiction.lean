module

public import CFSG.Permutation.FiveTransitive.Degree80SharpFactorization
public import CFSG.Permutation.FiveTransitive.Degree80SeventyNineNormalizer
public import CFSG.Permutation.FiveTransitive.Degree80SeventyNineNumeric

public section

namespace CFSG

namespace FiveTransitive.Degree80OrderContradiction
open MulAction

private theorem excluded_of_five_set
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 80)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (hbound : ∀ S : Sylow 2 (fixingSubgroup P s), Nat.card S ≤ 2 ^ 16) : False := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
  obtain ⟨a,b,c,ha0,ha,hb,hc,hH,hP⟩ :=
    Degree80SharpFactorization.card_exponents P hcard h5 hnotAlt s hs
  let S : Sylow 2 (fixingSubgroup P s) := Sylow.nonempty.some
  have hpow : 2 ^ a ∣ Nat.card (fixingSubgroup P s) := by
    rw [hH]
    exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  have hdiv : 2 ^ a ∣ Nat.card S := by
    rw [S.card_eq_multiplicity]
    exact pow_dvd_pow 2 ((Nat.Prime.pow_dvd_iff_le_factorization
      (by decide : Nat.Prime 2) Nat.card_pos.ne').mp hpow)
  have hsmall := (Nat.le_of_dvd Nat.card_pos hdiv).trans (hbound S)
  have ha16 : a ≤ 16 := by
    by_contra hn
    have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 17 ≤ a)
    norm_num at hh hsmall
    omega
  obtain ⟨d,k,hd,hk,he⟩ := Degree80SeventyNineNormalizer.constraints P hcard h5 hnotAlt
  rw [hP] at he
  exact Degree80SeventyNineNumeric.excluded ha16 hb hc
    (Degree80SeventyNineNumeric.residue hd hk he)

theorem excluded
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 80)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (hbound : ∀ (s : Set X), s.ncard = 5 →
      ∀ S : Sylow 2 (fixingSubgroup P s), Nat.card S ≤ 2 ^ 16) : False := by
  obtain ⟨s,_,hs⟩ := Set.exists_subset_card_eq
    (show 5 ≤ (Set.univ : Set X).ncard by simp [Set.ncard_univ,hcard])
  exact excluded_of_five_set P hcard h5 hnotAlt s hs (hbound s hs)

end FiveTransitive.Degree80OrderContradiction

end CFSG
