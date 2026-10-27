module

public import CFSG.Permutation.FiveTransitive.Degree31Order4096FixedFive
public import CFSG.Permutation.FiveTransitive.OrbitIndexDividesComplement
public import CFSG.Permutation.FiveTransitive.MinimalOrbitStabilizer

public section

namespace CFSG

namespace FiveTransitive.Degree31TwoOrbitExists

open MulAction

theorem exists_two_orbit
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 31)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (hH : Nat.card (fixingSubgroup P s) = 4096) :
    ∃ x : X, x ∉ s ∧ Nat.card (orbit (fixingSubgroup P s) x) = 2 := by
  classical
  by_contra hn
  push Not at hn
  let H := fixingSubgroup P s
  have hf := Degree31Order4096FixedFive.fixed_eq P hcard h5 hnotAlt s hs hH
  have hstab : ∀ x : X, x ∉ fixedPoints H X → Nat.card (stabilizer H x) ∣ 1024 := by
    intro x hx
    have hxs : x ∉ s := by rwa [hf] at hx
    have hc := Degree31Order4096FixedFive.orbit_card_cases P hcard h5 hnotAlt s hs hH x hxs
    have hm := MinimalOrbitStabilizer.nat_card_orbit_mul_stabilizer H X x
    change Nat.card (orbit H x) * Nat.card (stabilizer H x) = Nat.card H at hm
    change Nat.card H = 4096 at hH
    rw [hH] at hm
    rcases hc with hc | hc | hc | hc
    · exact False.elim (hn x hxs hc)
    · change Nat.card (orbit H x) = 4 at hc
      rw [hc] at hm
      have he : Nat.card (stabilizer H x) = 1024 := by omega
      rw [he]
    · change Nat.card (orbit H x) = 8 at hc
      rw [hc] at hm
      have he : Nat.card (stabilizer H x) = 512 := by omega
      rw [he]
      norm_num
    · change Nat.card (orbit H x) = 16 at hc
      rw [hc] at hm
      have he : Nat.card (stabilizer H x) = 256 := by omega
      rw [he]
      norm_num
  have hd := OrbitIndexDividesComplement.quotient_dvd_complement H X 1024
    (by change 1024 ∣ Nat.card (fixingSubgroup P s); rw [hH]; norm_num) hstab
  change Nat.card (fixingSubgroup P s) / 1024 ∣ Nat.card X - (fixedPoints H X).ncard at hd
  rw [hH,hf,hs,Nat.card_eq_fintype_card,hcard] at hd
  norm_num at hd

end FiveTransitive.Degree31TwoOrbitExists

end CFSG
