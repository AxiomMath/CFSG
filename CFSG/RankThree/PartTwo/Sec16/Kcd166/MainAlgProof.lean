module

public import CFSG.RankThree.PartTwo.Sec16.Kcd166.TheoremD

public section

namespace CFSG.RankThree.PartTwo.Sec16.Kcd166

private lemma six_ne_zero_of_five_le {𝕜 : Type*} [Field 𝕜] {p : ℕ} [CharP 𝕜 p]
    (hp : p.Prime) (hp5 : 5 ≤ p) : (6 : 𝕜) ≠ 0 := by
  intro h0
  have hp6 : p ∣ 2 * 3 := (CharP.cast_eq_zero_iff 𝕜 p 6).1 (by exact_mod_cast h0)
  rcases (Nat.Prime.dvd_mul hp).1 hp6 with h | h
  · have := Nat.le_of_dvd (by norm_num) h
    omega
  · have := Nat.le_of_dvd (by norm_num) h
    omega

theorem mainAlg166_holds : MainAlg166 := by
  intro 𝕜 _ _ p _ hp hp5 Γ _ _ hperf V _ _ _ σ hirr hfaith hr3 T _ π hπ hT hker3 hkerS d hd3
    hdZ I hIperf hIA5 hI2 hId v hv
  have h6 : (6 : 𝕜) ≠ 0 := six_ne_zero_of_five_le hp hp5
  have h2 : (2 : 𝕜) ≠ 0 := fun h => h6 (by rw [show (6 : 𝕜) = 2 * 3 by norm_num, h, zero_mul])
  have hinv : ∀ t : Γ, t ^ 2 = 1 → t ≠ 1 →
      Module.finrank 𝕜 (LinearMap.ker (σ t - 1)) ≤ 3 := by
    intro t ht ht1
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine hr3 t (IsPGroup.of_card (n := 1) ?_) ht1
    rw [Nat.card_zpowers, orderOf_eq_prime ht ht1, pow_one]
  by_cases hno : ∀ s t : Γ, s ^ 2 = 1 → t ^ 2 = 1 → s ≠ 1 → t ≠ 1 → s * t = t * s → s = t
  · exact apply_eq_self_of_noKlein hp hp5 hperf hno σ hinv π hπ hT hker3 hkerS hd3 hdZ hIperf
      hIA5 hI2 hId hv
  · push Not at hno
    obtain ⟨s, t, hs, ht, hs1, ht1, hst, hne⟩ := hno
    have hst2 : (s * t) ^ 2 = 1 := by
      rw [(show Commute s t from hst).mul_pow, hs, ht, one_mul]
    have hst1 : s * t ≠ 1 := by
      intro h1
      apply hne
      have hts : t = s⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [hts, inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hs)]
    have hdim : Module.finrank 𝕜 V ≤ 9 := by
      refine finrank_le_nine_of_commute h2 σ hs ht hst ?_
      rintro x (rfl | rfl | rfl)
      · exact hinv _ hs hs1
      · exact hinv _ ht ht1
      · exact hinv _ hst2 hst1
    have hcen := ker_le_center_of_finrank_le_nine hp hp5 hperf σ hirr hfaith hdim π hπ hT hker3
      hkerS hr3
    have hv0 : v = 0 :=
      eq_zero_of_ker_le_center h6 hperf σ hirr hfaith π hπ hT hcen hker3 hinv hIA5 hv
    rw [hv0, map_zero]

end CFSG.RankThree.PartTwo.Sec16.Kcd166
