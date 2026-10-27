module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3KC
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3TCore
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3TRGroup
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3F3A
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4Exc
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Facts13

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s21_22R3F3SzQ5T_of_inputs {D : Data G}
    {Ch : Choice2011 G} (h205 : S20_5 D)
    (hF : H1930 D → ∀ {K₁ : Subgroup G}, K₁ ∈ calL D.T D.M → ∀ {x y : G}, x ∈ K₁ → y ∈ K₁ →
      x ∈ normalizer (D.T : Set G) → y ∈ normalizer (D.T : Set G) → ∀ {r : ℕ}, r.Prime →
      7 < r → ∀ {k : ℕ}, orderOf y = r ^ k → x * y * x⁻¹ * y⁻¹ ∈ D.T) :
    S21_22R3F3SzQ5T D Ch := by
  intro h1930 c H₁ hH₁ H₂ hH₂ hL0 hfX hS1 hU3 hs he L hL hc2 n hn hSz q b hq hqd hqn hm hb hbo
    hbT hbL hnq h5 h53 h5cl hninn
  rw [hnq] at hSz hqn
  obtain ⟨K, hne, hset, hK⟩ := uc22s21ru4e_exists_second_member hc2 hL
  obtain ⟨e, m, hmo, -, hqm⟩ := hm
  have hq7 : 7 ≤ q := PartTwo.s13_seven_le_of_dvd hmo hq hqm
  have hq2 : q ≠ 2 := by omega
  have hqL : ¬ q ∣ Nat.card L := uc22r3g_not_dvd_card (Or.inr hSz) hq hq2 hqn hmo hqm
  have hθ : inducedQuotInfAut L b hbL ∉ (MulAut.conj).range :=
    uc22r3g_not_inner hL (center_eq_bot_of_isSz hL.2.2 hSz) hbL hninn
  have hbM : b ∈ D.M := c.hBM hb
  have hq1 : 2 ^ q - 1 ≠ 1 := by
    have h2 : 2 ^ 2 ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) hq.two_le
    norm_num at h2
    omega
  obtain ⟨r, hr, hrq⟩ := Nat.exists_prime_and_dvd hq1
  have h2q : 2 * q < r := uc22r3t_two_mul_lt_of_dvd hq hq2 hr hrq
  have hr2 : r ≠ 2 := by omega
  obtain ⟨R, hR, hRM, hRT, hbR, z, hzR, hzbc⟩ :=
    uc22r3t_exists_rgroup hL hK hne hset hSz hr hrq hq hq7 hqL hbM hbo hbT hbL hθ
  rcases uc22r3t_split hH₁ hH₂ hfX hr hR hr2 hRM hRT ⟨z, hzR, hzbc⟩ with
    ⟨z, hz, hzne⟩ | ⟨z, hz, hzne⟩
  · exact hzne (uc22r3t_commute_of_mem_inf h205 h1930 c hH₁ (hL0.trans inf_le_left) hr hR hRM
      hRT hb hq hq2 hbo hbT hbR hq7 h2q he (hF h1930) z hz)
  · exact hzne (uc22r3t_commute_of_mem_inf h205 h1930 c hH₂ (hL0.trans inf_le_right) hr hR hRM
      hRT hb hq hq2 hbo hbT hbR hq7 h2q he (hF h1930) z hz)

end CFSG.LocalAnalysis.UniquenessCase.UC22
