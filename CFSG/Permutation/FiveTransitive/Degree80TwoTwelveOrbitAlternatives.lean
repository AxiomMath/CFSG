module

public import CFSG.Permutation.FiveTransitive.Degree80TwoTwelveOrbitNumeric
public import CFSG.Permutation.FiveTransitive.Degree80TwoTwelveOrbitBudget
public import CFSG.Permutation.FiveTransitive.Degree80TwoTwelveElevenElement

public section

namespace CFSG

namespace FiveTransitive.Degree80TwoTwelveOrbitAlternatives
open MulAction SylowFixedActionCore NormalizerOrbitFamily

theorem alternatives
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 80)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 2 (fixingSubgroup P s))
    (hF : Nat.card (sylowFixedPoints X P s S) = 12) :
    let Q := sylowImage X P s S
    Nat.card (Family (X := X) Q 8) = 0 ∧
    Nat.card (Family (X := X) Q 16) = 0 ∧
    Nat.card (Family (X := X) Q 32) = 0 ∧
    Nat.card (Family (X := X) Q 64) = 0 ∧
    ((Nat.card (Family (X := X) Q 2) = 34 ∧ Nat.card (Family (X := X) Q 4) = 0) ∨
      (Nat.card (Family (X := X) Q 2) = 12 ∧ Nat.card (Family (X := X) Q 4) = 11)) := by
  classical
  let Q := sylowImage X P s S
  have hQ : IsPGroup 2 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hcommon : Nat.card (fixedPoints Q X) = 12 := by
    rw [← FixedNormalizerAction.fixed_eq Q]
    exact hF
  have hm := Degree80TwoTwelveOrbitMass.card_eq_orbit_sum (X := X)
    (by rw [Nat.card_eq_fintype_card,hcard]) Q hQ
  rw [Nat.card_eq_fintype_card (α := X),hcard,hcommon] at hm
  obtain ⟨g,hg,_,_⟩ := Degree80TwoTwelveElevenElement.exists_eleven P hcard h5 hnotAlt s hs S hF
  have hb := Degree80TwoTwelveOrbitBudget.residue_budget P hcard h5 hnotAlt Q hQ g hg
  exact Degree80TwoTwelveOrbitNumeric.alternatives
    (Nat.card (Family (X := X) Q 2))
    (Nat.card (Family (X := X) Q 4))
    (Nat.card (Family (X := X) Q 8))
    (Nat.card (Family (X := X) Q 16))
    (Nat.card (Family (X := X) Q 32))
    (Nat.card (Family (X := X) Q 64)) (by omega) hb

theorem orbit_card_le_four
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 80)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 2 (fixingSubgroup P s))
    (hF : Nat.card (sylowFixedPoints X P s S) = 12) (x : X) :
    Nat.card (orbit (sylowImage X P s S) x) ≤ 4 := by
  classical
  let Q := sylowImage X P s S
  have hQ : IsPGroup 2 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  obtain ⟨h8,h16,h32,h64,_⟩ := alternatives P hcard h5 hnotAlt s hs S hF
  change Nat.card (orbit Q x) ≤ 4
  change Nat.card (Family (X := X) Q 8) = 0 at h8
  change Nat.card (Family (X := X) Q 16) = 0 at h16
  change Nat.card (Family (X := X) Q 32) = 0 at h32
  change Nat.card (Family (X := X) Q 64) = 0 at h64
  have hpos (m : ℕ) (hm : Nat.card (orbit Q x) = m) : 0 < Nat.card (Family (X := X) Q m) := by
    let O : Family (X := X) Q m := ⟨Quotient.mk'' x,by rwa [orbitRel.Quotient.orbit_mk]⟩
    let _ : Nonempty (Family (X := X) Q m) := ⟨O⟩
    exact Nat.card_pos
  have hc := Degree80TwoTwelveOrbitMass.orbit_card_cases
    (by rw [Nat.card_eq_fintype_card,hcard]) Q hQ (Quotient.mk'' x)
  rw [orbitRel.Quotient.orbit_mk] at hc
  rcases hc with h | h | h | h | h | h | h
  · omega
  · omega
  · omega
  · have hh := hpos 8 h; omega
  · have hh := hpos 16 h; omega
  · have hh := hpos 32 h; omega
  · have hh := hpos 64 h; omega

end FiveTransitive.Degree80TwoTwelveOrbitAlternatives

end CFSG
