module

public import CFSG.Permutation.FiveTransitive.Degree31PairFixerBound
public import CFSG.Permutation.FiveTransitive.OrbitFixedComplementBound

public section

namespace CFSG

namespace FiveTransitive.Degree31Order4096FixedFive

open MulAction

theorem fixed_eq
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 31)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (hH : Nat.card (fixingSubgroup P s) = 4096) :
    fixedPoints (fixingSubgroup P s) X = s := by
  have htwo : IsPGroup 2 (fixingSubgroup P s) :=
    IsPGroup.iff_card.mpr ⟨12,by rw [hH]; norm_num⟩
  have hsfix : s ⊆ fixedPoints (fixingSubgroup P s) X := by
    intro x hx q
    exact (mem_fixingSubgroup_iff P).mp q.property x hx
  have hle : Nat.card (fixedPoints (fixingSubgroup P s) X) ≤ 5 := by
    by_contra hn
    have hh := Degree31PairFixerBound.card_le_two_thousand_forty_eight
      P hcard h5 hnotAlt (fixingSubgroup P s) htwo (by omega)
    omega
  apply (Set.eq_of_subset_of_ncard_le hsfix ?_).symm
  rw [hs,← Nat.card_coe_set_eq]
  exact hle

theorem orbit_card_cases
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 31)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (hH : Nat.card (fixingSubgroup P s) = 4096)
    (x : X) (hx : x ∉ s) :
    Nat.card (orbit (fixingSubgroup P s) x) = 2 ∨
      Nat.card (orbit (fixingSubgroup P s) x) = 4 ∨
      Nat.card (orbit (fixingSubgroup P s) x) = 8 ∨
      Nat.card (orbit (fixingSubgroup P s) x) = 16 := by
  classical
  have htwo : IsPGroup 2 (fixingSubgroup P s) :=
    IsPGroup.iff_card.mpr ⟨12,by rw [hH]; norm_num⟩
  have hf := fixed_eq P hcard h5 hnotAlt s hs hH
  have hb := OrbitFixedComplementBound.card_le (G := fixingSubgroup P s) x
  have hsNat : Nat.card s = 5 := (Nat.card_coe_set_eq s).trans hs
  rw [hf,hsNat,Nat.card_eq_fintype_card (α := X),hcard] at hb
  obtain ⟨e,he⟩ := htwo.card_orbit x
  have he4 : e ≤ 4 := by
    by_contra hn
    have hp := Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega : 5 ≤ e)
    rw [he] at hb
    norm_num at hp hb
    omega
  have hepos : 0 < e := by
    by_contra hn
    have he0 : e = 0 := by omega
    have hfix : x ∈ fixedPoints (fixingSubgroup P s) X :=
      mem_fixedPoints_iff_card_orbit_eq_one.mpr (by
        rw [← Nat.card_eq_fintype_card,he,he0,pow_zero])
    exact hx (hf ▸ hfix)
  rw [he]
  interval_cases e <;> norm_num

end FiveTransitive.Degree31Order4096FixedFive

end CFSG
