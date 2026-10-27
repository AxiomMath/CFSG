module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62xLift

public section

namespace CFSG.StandardType.RCKA6

theorem rckF4_no_center_prime_of_isCyclic {J : Type} [Group J] [Finite J]
    (hJ : commutator J = ⊤) {r : ℕ} (hr : r.Prime)
    (hcyc : ∀ P : Sylow r (J ⧸ Subgroup.center J), IsCyclic P) {z : J}
    (hz : z ∈ Subgroup.center J) (hzr : orderOf z = r) : False := by
  letI : Fact r.Prime := ⟨hr⟩
  let Z : Subgroup J := Subgroup.center J
  let π : J →* J ⧸ Z := QuotientGroup.mk' Z
  obtain ⟨S⟩ : Nonempty (Sylow r J) := Sylow.nonempty
  have hPmap : IsPGroup r (S.map π) := (Sylow.isPGroup' S).map π
  obtain ⟨P, hSP⟩ : ∃ P : Sylow r (J ⧸ Z), S.map π ≤ P := IsPGroup.exists_le_sylow hPmap
  haveI : IsCyclic P := hcyc P
  let f : S →* P :=
    (π.comp (S : Subgroup J).subtype).codRestrict P fun x =>
      hSP (by simpa using Subgroup.apply_coe_mem_map π (S : Subgroup J) x)
  have hfker : f.ker ≤ Subgroup.center S := by
    intro x hx
    have hx1 : f x = 1 := MonoidHom.mem_ker.mp hx
    have hxq : π (x : J) = 1 := by
      have := congrArg Subtype.val hx1
      simpa [f] using this
    have hxZ : (x : J) ∈ Z := (QuotientGroup.eq_one_iff (x : J)).mp hxq
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp hxZ (y : J)
  have hQc : IsMulCommutative S :=
    MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center f hfker
  have hzf : z ^ r = 1 := by
    rw [← hzr]
    exact pow_orderOf_eq_one z
  have hz1 : z = 1 :=
    CFSG.LocalAnalysis.RankThreeTheoremC.lift62x_center_eq_one hJ hr
      (Sylow.isPGroup' S) (Sylow.not_dvd_index S) hQc hz hzf
  have hr1 : r = 1 := by
    rw [← hzr, hz1, orderOf_one]
  exact hr.ne_one hr1

theorem rckF4_A6_sylow_isCyclic {Q : Type} [Group Q] (e : Q ≃* alternatingGroup (Fin 6)) {r : ℕ}
    [Fact r.Prime] (hr : 5 ≤ r) (P : Sylow r Q) : IsCyclic P := by
  haveI : Finite Q := Finite.of_equiv (alternatingGroup (Fin 6)) e.toEquiv.symm
  have hcardQ : Nat.card Q = 360 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  have hdvd : Nat.card P ∣ 360 := by
    rw [← hcardQ]
    exact Subgroup.card_subgroup_dvd_card (P : Subgroup Q)
  obtain ⟨n, hn⟩ := IsPGroup.exists_card_eq (Sylow.isPGroup' P)
  have hndvd : r ^ n ∣ 360 := by rwa [hn] at hdvd
  have hr2 : ¬ r ^ 2 ∣ 360 := by
    rintro h
    have hpr : r.Prime := Fact.out
    have hle : r ^ 2 ≤ 360 := Nat.le_of_dvd (by norm_num) h
    have hr18 : r ≤ 18 := by
      by_contra hc
      have hc' : 18 < r := Nat.lt_of_not_le hc
      nlinarith
    interval_cases r <;> (exfalso; revert h hpr; decide)
  have hnle : n ≤ 1 := by
    by_contra h
    have h2n : 2 ≤ n := Nat.succ_le_of_lt (Nat.lt_of_not_le h)
    exact hr2 (Nat.pow_dvd_of_le_of_pow_dvd h2n hndvd)
  have hdvdpr : Nat.card P ∣ r := by
    rw [hn]
    have : n = 0 ∨ n = 1 := by omega
    rcases this with h0 | h1
    · rw [h0]; simp
    · rw [h1]; simp
  exact isCyclic_of_card_dvd_prime hdvdpr

end CFSG.StandardType.RCKA6
