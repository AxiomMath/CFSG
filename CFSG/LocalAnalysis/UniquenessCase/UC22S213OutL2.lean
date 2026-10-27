module

public import CFSG.Blueprint.Catalog
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.LocalAnalysis.ComponentInitial.LinearModelOuterTwoPart

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem uc22s213_not_dvd_card_outer_psl2 {X : Type} [Group X] {p e : ℕ}
    (h : CFSG.Blueprint.LieModel X .PSL 2 p e) (hp2 : p ≠ 2) (hpe : ¬ p ∣ e) :
    ¬ p ∣ Nat.card (Outer X) := by
  have hp : p.Prime := h.admissible.1
  have hdvd := (CFSG.LocalAnalysis.ComponentInitial.linear_model_outer_two_part_bound X 2 p e
    (h.statedClassicalModel (by decide))).2.2.2.1 rfl
  intro hpO
  rcases (Nat.Prime.dvd_mul hp).mp (hpO.trans hdvd) with h1 | h1
  · exact hpe h1
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      (h1.trans (Nat.gcd_dvd_left 2 _)))

end CFSG.LocalAnalysis.UniquenessCase.UC22
