module

public import CFSG.Sporadic.SchreierLemmas.OuterAlternatingSix
public import CFSG.Quasithin.Vol2.GoldschmidtTDOutAbs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingOutsideSix

public section

namespace CFSG.Quasithin.H13.OutTwoNilp

open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)
open CFSG.ComponentClassification.CatalogueSchreierAlternating
  (outer_card_dvd_two_of_equiv_outside_six)
open CFSG.Quasithin.H13.Ch838 (TwoNilpotent)

theorem twoNilpotent_outer_of_alt {S : Type} [Group S] [Finite S] {n : ℕ} (hn5 : 5 ≤ n)
    (hn8 : n ≤ 8) (e : S ≃* alternatingGroup (Fin n)) : TwoNilpotent (Outer S) := by
  by_cases hn6 : n = 6
  · subst hn6
    have hc := CFSG.Sporadic.SchreierLemmas.outer_alternating_six.2.1
    exact TwoNilpotent.of_mulEquiv (equivalence e).symm
      (twoNilpotent_of_comm fun a b => hc.is_comm.comm a b)
  · have hd := outer_card_dvd_two_of_equiv_outside_six (by omega : n = 5 ∨ 7 ≤ n) e
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
    · exact twoNilpotent_of_isPGroup_two (IsPGroup.of_card (n := 0) (by rw [h1]; rfl))
    · exact twoNilpotent_of_isPGroup_two (IsPGroup.of_card (n := 1) (by rw [h2]; rfl))

end CFSG.Quasithin.H13.OutTwoNilp
