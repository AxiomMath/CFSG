module

public import CFSG.RankThree.PartTwo.Sec13.KF135Core
import CFSG.RankThree.PartOne.KA.AlternatingPlaneInner

public section

namespace CFSG.RankThree.PartTwo.Sec13.KF135Proof

open CFSG.RankThree.PartTwo.Sec13.F135Last
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem not_sq_dvd_factorial {p n : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) (hn : n ≤ 12) :
    ¬ p ^ 2 ∣ n.factorial := by
  intro h
  have h12 : p ^ 2 ∣ (12 : ℕ).factorial := h.trans (Nat.factorial_dvd_factorial hn)
  have hp12 : p ≤ 12 := hp.dvd_factorial.1 ((dvd_pow_self p two_ne_zero).trans h12)
  interval_cases p <;> revert hp h12 <;> norm_num [Nat.factorial]

theorem kF135At_fam5 : KF135At Fam5 := by
  intro S _ _ p P x u V hF h
  obtain ⟨n, hn5, hn12, ⟨f⟩⟩ := hF
  exfalso
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
  have hp7 := h.seven_le
  have hout : ¬ p ∣ Nat.card (Outer S) := by
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence f).toEquiv]
    intro hd
    have hle := Nat.le_of_dvd Nat.card_pos hd
    have := CFSG.RankThree.PartOne.card_outer_alternating_le_four hn5
    omega
  have hcube := h.cube_dvd_card_of_not_dvd_outer hout
  rw [Nat.card_congr f.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
    Fintype.card_fin] at hcube
  have hdiv : n.factorial / 2 ∣ n.factorial :=
    Nat.div_dvd_of_dvd (Nat.dvd_factorial two_pos (by omega))
  exact not_sq_dvd_factorial h.prime hp7 hn12
    ((pow_dvd_pow p (by norm_num : 2 ≤ 3)).trans (hcube.trans hdiv))

end CFSG.RankThree.PartTwo.Sec13.KF135Proof
