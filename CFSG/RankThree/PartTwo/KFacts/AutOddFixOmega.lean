module

public import CFSG.GH74.Uniqueness.Bender.SuzukiAut

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.GH74.Uniqueness.Bender

variable {X : Type} [Group X] [Finite X]

theorem eq_one_of_odd_of_fix_omega_sz {a : ℕ} (ha : 1 ≤ a)
    (e : X ≃* CFSG.Open.Sz a) (S : Sylow 2 X) (α : MulAut X) (hα : Odd (orderOf α))
    (hfix : ∀ z ∈ (S : Subgroup X), z ^ 2 = 1 → α z = z) : α = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB : BenderType X (2 * a + 1) 2 1 :=
    BenderType.suzuki a ha (e.trans (MulEquiv.subgroupCongr (szModel_eq_open_sz a).symm))
  obtain ⟨_, hc⟩ := hB.exists_benderCore S
  have hσ : ∀ z ∈ rootCenter (S : Subgroup X), α z = z := by
    intro z hz
    exact hfix z (rootCenter_le (S : Subgroup X) hz) (by
      simpa [pow_two] using hc.center_sq z hz)
  obtain ⟨r, hr, hαr⟩ := hB.exists_eq_conj_of_centralizes_center_suzuki S α hσ
  obtain ⟨k, hk⟩ : ∃ k : ℕ, orderOf r = 2 ^ k := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp S.isPGroup' ⟨r, hr⟩
    exact ⟨k, (Subgroup.orderOf_coe ⟨r, hr⟩).trans hk⟩
  have hdvd : orderOf α ∣ 2 ^ k := by
    rw [hαr]
    exact (orderOf_map_dvd (MulAut.conj : X →* MulAut X) r).trans (by rw [hk])
  have hone : orderOf α = 1 := (hα.coprime_two_right.pow_right k).eq_one_of_dvd hdvd
  exact orderOf_eq_one_iff.mp hone

end CFSG.RankThree.PartTwo.KFacts

end
