module

public import CFSG.Permutation.FiveTransitive.Degree48FiveFixerFactorization
public import CFSG.Permutation.FiveTransitive.Degree48LargeSylowActual
public import CFSG.Permutation.FiveTransitive.Degree48FiveFixerNumeric

public section

namespace CFSG

namespace FiveTransitive.Degree48FiveFixerCard
open MulAction Degree48FiveFixerNumeric

private theorem card_eq
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 48)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) : Nat.card (fixingSubgroup P s) = 5505024 := by
  obtain ⟨a,b,c,d,ha0,ha,hb,hc,hd,hH,hP⟩ :=
    Degree48FiveFixerFactorization.card_exponents P hcard h5 hnotAlt s hs
  obtain ⟨v47,k47,hv47,hk47,hprod47⟩ :=
    Degree48LargeSylowActual.forty_seven P hcard h5 hnotAlt
  obtain ⟨v23,k23,hv23,hf23,hk23,hprod23⟩ :=
    Degree48LargeSylowActual.twenty_three P hcard h5 hnotAlt
  obtain ⟨v11,k11,hv11,hf11,hk11,hprod11⟩ :=
    Degree48LargeSylowActual.eleven P hcard h5 hnotAlt
  have h47 := forty_seven_residue hv47 (one_dvd _) hk47 (hprod47.trans hP)
  have h23 := twenty_three_residue hv23 hf23 hk23 (hprod23.trans hP)
  have h11 := eleven_residue hv11 hf11 hk11 (hprod11.trans hP)
  obtain ⟨rfl,rfl,rfl,rfl⟩ := exponents ha0 ha hb hc hd h47 h23 h11
  norm_num at hH ⊢
  exact hH

theorem five_not_dvd
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 48)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) : ¬ 5 ∣ Nat.card (fixingSubgroup P s) := by
  rw [card_eq P hcard h5 hnotAlt s hs]
  norm_num

theorem ambient_card
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 48)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P) :
    Nat.card P = 205476480 * 2^18 * 3 * 7 := by
  let _ := h5
  obtain ⟨s,_,hs⟩ := Set.exists_subset_card_eq
    (show 5 ≤ (Set.univ : Set X).ncard by simp [Set.ncard_univ,hcard])
  have hi := IsMultiplyPretransitive.index_of_fixingSubgroup_eq (G := P) s (by rwa [hs])
  rw [Nat.card_eq_fintype_card,hcard,hs] at hi
  norm_num [Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial] at hi
  have hm := (fixingSubgroup P s).index_mul_card
  rw [hi,card_eq P hcard h5 hnotAlt s hs] at hm
  norm_num at hm ⊢
  exact hm.symm

end FiveTransitive.Degree48FiveFixerCard

end CFSG
