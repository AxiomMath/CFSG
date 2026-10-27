module

public import CFSG.RankThree.PartOne.CTP.AltLeaf
public import CFSG.RankThree.PartOne.CTP.StrongPInspection

public section

namespace CFSG.RankThree.PartOne.K159F

open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.StrongP

theorem not_prime_cube_dvd_factorial {p n : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : n ≤ 12) :
    ¬ p ^ 3 ∣ n.factorial := by
  intro h
  have hpn : p ≤ n := (hp.dvd_factorial).mp (dvd_trans (dvd_pow_self p (by norm_num)) h)
  have hp12 : p ≤ 12 := hpn.trans hn
  interval_cases p <;> first | (exfalso; revert hp; norm_num; done) | skip
  all_goals interval_cases n <;> simp_all [Nat.factorial]

theorem false_of_alt_five {p n : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (hn5 : 5 ≤ n) (hn : n ≤ 12)
    {H : Type} [Group H] [Finite H] (S : Subgroup H) [S.Normal]
    (e : S ≃* alternatingGroup (Fin n)) (hSc : Subgroup.centralizer (S : Set H) = ⊥)
    {P : Subgroup H} (hP : IsSylowOf p P ⊤) (hΩ : Nat.card (omegaOne p P) = p ^ 3) : False := by
  have hp : p.Prime := Fact.out
  have hquot : ¬ p ∣ Nat.card (H ⧸ S) := by
    intro hd
    have hpos : 0 < Nat.card (H ⧸ S) := Nat.card_pos
    have h1 := Nat.le_of_dvd hpos hd
    have h2 := card_quotient_le_outer S hSc
    have h3 := Alt.outer_card_le_four hn5 e
    omega
  have hPS : P ≤ S := le_of_isPGroup_of_not_dvd_card_quotient hP.2.1 hquot
  have hPcard : p ^ 3 ∣ Nat.card P := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hP.2.1
    have h1 : p ^ 3 ≤ Nat.card P := by
      rw [← hΩ]
      exact Subgroup.card_le_of_le (omegaOne_le P)
    rw [hk] at h1 ⊢
    exact pow_dvd_pow p ((Nat.pow_le_pow_iff_right hp.one_lt).mp h1)
  let φ : ↥S →* Equiv.Perm (Fin n) := (alternatingGroup (Fin n)).subtype.comp e.toMonoidHom
  have hφ : Function.Injective φ := Subtype.val_injective.comp e.injective
  have hcard : Nat.card ((P.subgroupOf S).map φ) = Nat.card P := by
    rw [Subgroup.card_map_of_injective hφ]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPS).toEquiv
  have hdvd : p ^ 3 ∣ n.factorial := by
    have h2 := Subgroup.card_subgroup_dvd_card ((P.subgroupOf S).map φ)
    rw [hcard, Nat.card_eq_fintype_card (α := Equiv.Perm (Fin n)), Fintype.card_perm,
      Fintype.card_fin] at h2
    exact hPcard.trans h2
  exact not_prime_cube_dvd_factorial hp hp5 hn hdvd

end CFSG.RankThree.PartOne.K159F
