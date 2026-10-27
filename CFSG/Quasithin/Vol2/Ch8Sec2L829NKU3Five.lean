module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A134EvenClassical
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.Quasithin.H13.L829NK

open CFSG.Open CFSG.SectionRank CFSG.SectionRank.ClassicalEven

theorem nk_leafU3Five : NKLeafU3Five := by
  intro n hn X _ _ hm
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hm
  have hq0 : 2 ^ n ≠ 0 := by positivity
  have hKu : Nat.card Kˣ = (2 ^ n + 1) * (2 ^ n - 1) := by
    rw [Nat.card_units, hK, ← Nat.sq_sub_sq, one_pow]
  have hmod : 2 ^ n % 5 = 4 := by
    obtain ⟨k, hk⟩ : ∃ k, n = 4 * k + 2 := ⟨n / 4, by omega⟩
    have h16 : 16 ^ k % 5 = 1 := by
      rw [Nat.pow_mod]
      norm_num
    have hpow : 2 ^ n = 16 ^ k * 4 := by
      rw [hk, pow_add, pow_mul]
      norm_num
    rw [hpow]
    omega
  have h5 : 5 ∣ 2 ^ n + 1 := by omega
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 5
    (by rw [hKu]; exact h5.mul_right _)
  have hζq : ζ ^ (2 ^ n + 1) = 1 :=
    orderOf_dvd_iff_pow_eq_one.1 (by rw [hζ]; exact h5)
  have hd0 : torusDiag (torusVec ζ (0 : Fin 3) 2) ∈ StatedSU 3 (2 ^ n) K :=
    torusDiag_mem_SU hq0 (prod_torusVec ζ _ _) (by rw [torusVec_pow, hζq, torusVec_one])
  have hd1 : torusDiag (torusVec ζ (1 : Fin 3) 2) ∈ StatedSU 3 (2 ^ n) K :=
    torusDiag_mem_SU hq0 (prod_torusVec ζ _ _) (by rw [torusVec_pow, hζq, torusVec_one])
  have h2 : 2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup (StatedProj (StatedSU 3 (2 ^ n) K))) :=
    CFSG.QuasithinUnique.Vol2Native.EvenWit.two_le_pRank_torus (r := 5) (by norm_num) hζ
      (i₀ := (0 : Fin 3)) (i₁ := 1) (i₂ := 2) (by decide) (by decide) (by decide) hd0 hd1
  rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact CFSG.QuasithinUnique.Vol2Native.EvenWit.two_le_pRank_of_mulEquiv (by norm_num) e h2

end CFSG.Quasithin.H13.L829NK
