module

public import CFSG.RankThree.PartOne.K133.KillBasic
import CFSG.RankThree.PartOne.KA.AlternatingPlaneInner
public import CFSG.RankThree.PartOne.K133.Quot

public section

namespace CFSG.RankThree.PartOne.K133

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K

theorem not_pow_three_dvd_factorial {n p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hn : n ≤ 12) :
    ¬ p ^ 3 ∣ Nat.factorial n := by
  intro h
  have hpn : p ∣ Nat.factorial n := (dvd_pow_self p (by norm_num)).trans h
  have hp12 : p ≤ 12 := ((hp.dvd_factorial).1 hpn).trans hn
  have key : ∀ m ≤ 12, ¬ 5 ^ 3 ∣ Nat.factorial m ∧ ¬ 7 ^ 3 ∣ Nat.factorial m ∧
      ¬ 11 ^ 3 ∣ Nat.factorial m := by decide +kernel
  interval_cases p
  · exact (key n hn).1 h
  · exact absurd hp (by norm_num)
  · exact (key n hn).2.1 h
  · exact absurd hp (by norm_num)
  · exact absurd hp (by norm_num)
  · exact absurd hp (by norm_num)
  · exact (key n hn).2.2 h
  · exact absurd hp (by norm_num)

theorem noRankThree_alternating {n : ℕ} (hn5 : 5 ≤ n) (hn12 : n ≤ 12) {p : ℕ} (hp : p.Prime)
    (h5 : 5 ≤ p) : NoRankThree p (alternatingGroup (Fin n)) := by
  refine noRankThree_of_inner hp (not_dvd_outer_alternating hp (by omega) hn5) fun h => ?_
  have h1 : Nat.card (alternatingGroup (Fin n)) ∣ Nat.factorial n := by
    have h := Subgroup.card_subgroup_dvd_card (alternatingGroup (Fin n))
    have e : Nat.card (Equiv.Perm (Fin n)) = Nat.factorial n := by
      rw [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin]
    rwa [e] at h
  exact not_pow_three_dvd_factorial hp h5 hn12 (h.trans h1)

theorem kf133ResMaxItem_four : KF133ResMaxItem 4 :=
  KF133ResMaxAt.of_noRankThree fun X _ _ hX p hp h5 => by
    obtain ⟨n, hn5, hn12, ⟨e⟩⟩ := hX
    exact NoRankThree.of_mulEquiv hp e (noRankThree_alternating hn5 hn12 hp h5)

end CFSG.RankThree.PartOne.K133
