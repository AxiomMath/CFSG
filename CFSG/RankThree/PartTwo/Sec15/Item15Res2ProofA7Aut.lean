module

public import CFSG.RankThree.PartTwo.Sec15.Item1515ResProofA7
import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.RankThree.PartTwo.Sec15

namespace Proof15Res2

theorem exists_mem_dvd_of_prime_dvd_lcm {s : Multiset ℕ} {p : ℕ} (hp : p.Prime)
    (h : p ∣ s.lcm) : ∃ n ∈ s, p ∣ n := by
  induction s using Multiset.induction_on with
  | empty => exact absurd (by simpa using h) hp.not_dvd_one
  | cons a s ih =>
    rw [Multiset.lcm_cons, lcm_eq_nat_lcm, Nat.Prime.dvd_lcm hp] at h
    rcases h with ha | hs
    · exact ⟨a, Multiset.mem_cons_self a s, ha⟩
    · obtain ⟨n, hn, hpn⟩ := ih hs
      exact ⟨n, Multiset.mem_cons_of_mem hn, hpn⟩

theorem add_le_sum_of_mem_of_ne {s : Multiset ℕ} {a b : ℕ} (ha : a ∈ s) (hb : b ∈ s)
    (hab : a ≠ b) : a + b ≤ s.sum := by
  obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem ha
  rw [Multiset.sum_cons]
  have hbt : b ∈ t := (Multiset.mem_cons.mp hb).resolve_left fun h => hab h.symm
  have := Multiset.le_sum_of_mem hbt
  omega

theorem orderOf_perm_fin_seven_ne_fifteen (g : Equiv.Perm (Fin 7)) : orderOf g ≠ 15 := by
  intro h
  have hlcm : g.cycleType.lcm = 15 := by rw [Equiv.Perm.lcm_cycleType, h]
  obtain ⟨a, ha, h3a⟩ := exists_mem_dvd_of_prime_dvd_lcm Nat.prime_three
    (show 3 ∣ g.cycleType.lcm by rw [hlcm]; norm_num)
  obtain ⟨b, hb, h5b⟩ := exists_mem_dvd_of_prime_dvd_lcm Nat.prime_five
    (show 5 ∣ g.cycleType.lcm by rw [hlcm]; norm_num)
  have hsum : g.cycleType.sum ≤ 7 := by
    rw [Equiv.Perm.sum_cycleType]
    simpa using Finset.card_le_univ g.support
  have ha2 := Equiv.Perm.two_le_of_mem_cycleType ha
  have hb2 := Equiv.Perm.two_le_of_mem_cycleType hb
  have ha7 : a ≤ 7 := (Multiset.le_sum_of_mem ha).trans hsum
  have hab : a ≠ b := by
    rintro rfl
    obtain ⟨k, hk⟩ := (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 3 5) h3a
      h5b)
    omega
  have h3 : 3 ≤ a := Nat.le_of_dvd (by omega) h3a
  have h5 : 5 ≤ b := Nat.le_of_dvd (by omega) h5b
  have := add_le_sum_of_mem_of_ne ha hb hab
  omega

theorem eq_one_of_pow_three_of_commute {s y : Equiv.Perm (Fin 7)} (hs : s ^ 3 = 1)
    (hy : orderOf y = 5) (hc : Commute s y) : s = 1 := by
  by_contra hs1
  have h3 : orderOf s = 3 := orderOf_eq_prime hs hs1
  have h15 := hc.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [h3, hy]; norm_num)
  rw [h3, hy] at h15
  exact orderOf_perm_fin_seven_ne_fifteen _ h15

end Proof15Res2

theorem ks1515A7Aut : KS1515A7Aut := by
  intro Q _ hQ σ hσ3 x hx5 hσx
  obtain ⟨φ⟩ := hQ
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7
    (by norm_num) (by norm_num)
  set τ : MulAut (alternatingGroup (Fin 7)) := (φ.symm.trans σ).trans φ with hτ
  have hτa : ∀ a, τ a = φ (σ (φ.symm a)) := fun a => rfl
  obtain ⟨s, hs⟩ := hbij.2 τ
  have hτ3 : τ ^ 3 = 1 := by
    ext a
    simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply, hτa,
      MulEquiv.symm_apply_apply, hσ3, MulEquiv.apply_symm_apply]
  have hs3 : s ^ 3 = 1 := hbij.1 (by rw [map_pow, hs, hτ3, map_one])
  have hτy : τ (φ x) = φ x := by rw [hτa, MulEquiv.symm_apply_apply, hσx]
  have hcomm : Commute s ((φ x : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) := by
    have h := congrArg (fun t : alternatingGroup (Fin 7) => (t : Equiv.Perm (Fin 7)))
      (DFunLike.congr_fun hs (φ x))
    simp only [MulAut.conjNormal_apply, hτy] at h
    exact mul_inv_eq_iff_eq_mul.mp h
  have hy5 : orderOf ((φ x : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) = 5 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hx5]
  have hs1 := Proof15Res2.eq_one_of_pow_three_of_commute hs3 hy5 hcomm
  have hτ1 : τ = 1 := by rw [← hs, hs1, map_one]
  intro q
  have h := DFunLike.congr_fun hτ1 (φ q)
  rw [hτa, MulEquiv.symm_apply_apply, MulAut.one_apply] at h
  exact φ.injective h

end CFSG.RankThree.PartTwo.Sec15
