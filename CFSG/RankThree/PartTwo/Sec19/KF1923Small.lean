module

public import CFSG.RankThree.PartTwo.Sec19.Item1923Defs
import CFSG.RankThree.PartTwo.Sec20.KFactL3OddRank
import CFSG.RankThree.PartTwo.KFacts.K72L3Field
import CFSG.RankThree.PartTwo.KFacts.L34PGLFusionFacts
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.L34AutFix
import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable

public section

namespace CFSG.RankThree.PartTwo.Late

private theorem kf_center_eq_bot_of_mulEquiv {X Y : Type} [Group X] [Group Y] (f : X ≃* Y)
    (hY : Subgroup.center Y = ⊥) : Subgroup.center X = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hfx : f x ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro g
    obtain ⟨h, rfl⟩ := f.surjective g
    rw [← map_mul, ← map_mul, hx h]
  rw [hY, Subgroup.mem_bot] at hfx
  rw [Subgroup.mem_bot]
  exact f.injective (by rw [hfx, map_one])

private theorem kf_prime_dvd_241920 {r : ℕ} (hr : r.Prime) (h : r ∣ 241920) :
    r = 2 ∨ r = 3 ∨ r = 5 ∨ r = 7 := by
  have h' : r ∣ 2 ^ 8 * 3 ^ 3 * 5 * 7 := by
    norm_num
    exact h
  rcases (Nat.Prime.dvd_mul hr).mp h' with h1 | h1
  · rcases (Nat.Prime.dvd_mul hr).mp h1 with h2 | h2
    · rcases (Nat.Prime.dvd_mul hr).mp h2 with h3 | h3
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h3))
      · exact Or.inr (Or.inl
          ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp (hr.dvd_of_dvd_pow h3)))
    · exact Or.inr (Or.inr (Or.inl
        ((Nat.prime_dvd_prime_iff_eq hr (by norm_num : Nat.Prime 5)).mp h2)))
  · exact Or.inr (Or.inr (Or.inr
      ((Nat.prime_dvd_prime_iff_eq hr (by norm_num : Nat.Prime 7)).mp h1)))

theorem kf3b_holds : KF3b := by
  intro X _ _ hX
  obtain ⟨n, hn, ⟨e⟩⟩ := hX
  refine ⟨CFSG.RankThree.PartTwo.Sec20.kFactL3OddThreeRank n hn X ⟨e⟩, ?_⟩
  exact kf_center_eq_bot_of_mulEquiv
    (e.trans (CFSG.RankThree.PartTwo.KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 n)))
    CFSG.RankThree.PartTwo.Sec3.Sims321.center_projectiveSL_eq_bot

theorem kf4_holds : KF4 := by
  intro X _ _ hX α hα
  have hcen : Subgroup.center X = ⊥ := (kf3b_holds X hX).2
  obtain ⟨n, hn, ⟨e⟩⟩ := hX
  have hα3 : α ^ 3 = 1 := by
    rw [← hα]
    exact pow_orderOf_eq_one α
  by_cases hin : CFSG.RankThree.PartTwo.KFacts.IsInnerAut α
  · have hin' : α ∈ (MulAut.conj : X →* MulAut X).range := hin
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp hin'
    have hgα : MulAut.conj g = α := hg
    have hg3 : MulAut.conj (g ^ 3) = 1 := by
      rw [map_pow, hgα, hα3]
    have hmem : g ^ 3 ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro h
      have hh : MulAut.conj (g ^ 3) h = h := by
        rw [hg3, MulAut.one_apply]
      rw [MulAut.conj_apply] at hh
      calc h * g ^ 3 = (g ^ 3 * h * (g ^ 3)⁻¹) * g ^ 3 := by rw [hh]
        _ = g ^ 3 * h := by group
    rw [hcen, Subgroup.mem_bot] at hmem
    have hg1 : g ≠ 1 := by
      rintro rfl
      rw [map_one] at hgα
      rw [← hgα, orderOf_one] at hα
      norm_num at hα
    refine ⟨g, orderOf_eq_prime hmem hg1, ?_⟩
    rw [← hgα, MulAut.conj_apply, mul_inv_cancel_right]
  · have hK : Nat.card (GaloisField 2 n) % 3 = 2 := by
      rw [GaloisField.card 2 n hn.pos.ne']
      exact CFSG.RankThree.PartTwo.Sec20.two_pow_mod_three_of_odd hn
    haveI : Finite (GaloisField 2 n) :=
      Nat.finite_of_card_ne_zero (by rw [GaloisField.card 2 n hn.pos.ne']; positivity)
    obtain ⟨-, x₀, _y₀, hαx₀, -, hx₀3, hx₀1, -⟩ :=
      CFSG.RankThree.PartTwo.KFacts.fixedData_of_mulEquiv_projSL hK e α hα3 hin
    exact ⟨x₀, orderOf_eq_prime hx₀3 hx₀1, hαx₀⟩

theorem kf5_holds : KF5 := by
  intro X _ _ hX α hα
  obtain ⟨e⟩ := hX
  exact CFSG.RankThree.PartTwo.KFacts.L34.pow_three_eq_one_of_isPGroup_zpowers
    CFSG.RankThree.PartTwo.KFacts.L34.card_galoisField_two_two
    (e.trans (CFSG.RankThree.PartTwo.KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 2))) hα

theorem kf6_holds : KF6 := by
  intro X _ _ hX E _hEab hE H hH
  obtain ⟨e⟩ := hX
  have hk : Nat.card (GaloisField 2 2) = 4 :=
    CFSG.RankThree.PartTwo.KFacts.L34.card_galoisField_two_two
  have hψ := e.trans (CFSG.RankThree.PartTwo.KFacts.L34.projSLEquivProjectiveSL 3
    (GaloisField 2 2))
  have hAut : Nat.card (MulAut X) = 241920 := by
    rw [Nat.card_congr (MulAut.congr hψ).toEquiv,
      CFSG.RankThree.PartTwo.KFacts.L34.card_mulAut hk]
  haveI : Finite (MulAut X) := Nat.finite_of_card_ne_zero (by rw [hAut]; norm_num)
  have hno : ∀ q : ℕ, q.Prime → 5 ≤ q → ¬ q ∣ Nat.card H := by
    intro q hq hq5 hdvd
    haveI := Fact.mk hq
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' q hdvd
    have hxp : x ^ q = 1 := by
      rw [← hx]
      exact pow_orderOf_eq_one x
    have hxα : (x : MulAut X) ^ q = 1 := by
      rw [← Subgroup.coe_pow, hxp, Subgroup.coe_one]
    have h1 : (x : MulAut X) = 1 :=
      CFSG.LocalAnalysis.AGL81TheoremCD.Section14.eq_one_of_map_eq_of_pow_prime e hE hq hq5
        (hH _ x.2) hxα
    have h2 : orderOf (x : MulAut X) = q := by
      rw [Subgroup.orderOf_coe, hx]
    rw [h1, orderOf_one] at h2
    exact (Nat.Prime.one_lt hq).ne h2
  have hsub : (Nat.card H).primeFactors ⊆ {2, 3} := by
    intro r hr
    have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
    have hrd : r ∣ Nat.card H := Nat.dvd_of_mem_primeFactors hr
    have hHdvd : Nat.card H ∣ 241920 := by
      have h := Subgroup.card_subgroup_dvd_card H
      rwa [hAut] at h
    rcases kf_prime_dvd_241920 hrp (hrd.trans hHdvd) with rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact absurd hrd (hno 5 (by norm_num) le_rfl)
    · exact absurd hrd (hno 7 (by norm_num) (by norm_num))
  have hcard : (Nat.card H).primeFactors.card ≤ 2 :=
    (Finset.card_le_card hsub).trans Finset.card_le_two
  exact CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two hcard

end CFSG.RankThree.PartTwo.Late
