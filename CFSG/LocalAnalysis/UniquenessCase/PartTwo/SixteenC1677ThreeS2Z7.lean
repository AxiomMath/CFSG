module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeKernel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeS2Z7Gen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightOdd

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s168e3_s2_163_12 {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) (hs : s15 D.M V₀ V hV L = 2) (h : Case163_12 D V₀ V hV L) :
    D.sig = {7} := by
  obtain ⟨hc, hrk, -⟩ := h
  have hodd : Odd (Nat.card ↥(lBar V₀ V hV L)) := by
    rw [hc.2]
    decide
  have hV1 := s16e_v1Sub_eq_of_odd D hV hodd
  obtain ⟨g, hg⟩ := s16e_twoConj D c.std.h1217 hV c.setting c.ne hV1 hs
  have hsq := s15_Infra_vtil_sq_eq_one V₀ V hV
  have hcard : Nat.card ↥(Mbar D.M V₀ V hV) ∣ 2 * 168 ^ 2 := s168e3_z7_card_dvd hsq hg hrk
  have h3 : 3 ∉ D.sig := by
    intro h3
    have hfix := s168e3_z7_fix hsq hg hrk hc (c.two_le_pRank_mbar h3)
    have hcube : ¬ 3 ^ 3 ∣ Nat.card ↥(Mbar D.M V₀ V hV) := by
      intro hd
      have := hd.trans hcard
      norm_num at this
    exact s168e3_false_of_kernel c Nat.prime_three h3
      (s168e3_kernel_of_cube Nat.prime_three (Mbar D.M V₀ V hV) hcube hfix)
  have key : ∀ q ∈ D.sig, q = 7 := by
    intro q hq
    obtain ⟨hqp, hq2⟩ := D.sig_prime q hq
    have h2 := c.two_le_pRank_mbar hq
    obtain ⟨E, hE, -, hEcard⟩ := CFSG.SectionRank.exists_pRank hqp.one_lt (Mbar D.M V₀ V hV)
    have h1 : q ∣ Nat.card E := by
      rw [hEcard]
      exact dvd_pow_self q (by omega)
    have h4 : q ∣ 2 * 168 ^ 2 := h1.trans ((Subgroup.card_dvd_of_le hE).trans hcard)
    have hq3 : q ≠ 3 := fun h => h3 (h ▸ hq)
    have hfac : 2 * 168 ^ 2 = 2 ^ 7 * 3 ^ 2 * 7 ^ 2 := by norm_num
    rw [hfac] at h4
    rcases (Nat.Prime.dvd_mul hqp).1 h4 with h5 | h5
    · rcases (Nat.Prime.dvd_mul hqp).1 h5 with h6 | h6
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hqp Nat.prime_two).1
          (hqp.dvd_of_dvd_pow h6)) hq2
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hqp Nat.prime_three).1
          (hqp.dvd_of_dvd_pow h6)) hq3
    · exact (Nat.prime_dvd_prime_iff_eq hqp (by norm_num : Nat.Prime 7)).1
        (hqp.dvd_of_dvd_pow h5)
  obtain ⟨p₀, hp₀⟩ := c.std.hx.sig_nonempty
  ext q
  constructor
  · intro hq
    exact key q hq
  · intro hq
    rw [Set.mem_singleton_iff.1 hq, ← key p₀ hp₀]
    exact hp₀

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
