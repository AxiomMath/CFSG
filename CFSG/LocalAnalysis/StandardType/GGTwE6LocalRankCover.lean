module

public import CFSG.LocalAnalysis.StandardType.GGTwE6LocalRankTorus

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Exceptional

namespace TwE6Lang


theorem exists_cover_localRank {n : ℕ} (hn : 1 ≤ n) (h3 : 3 ∣ 2 ^ n + 1) :
    ∃ U E : Subgroup (twistedE6Group 2 n), U ≠ ⊥ ∧ IsPGroup 2 U ∧
      E ≤ Subgroup.normalizer (U : Set (twistedE6Group 2 n)) ∧
      IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 5 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (GaloisField 2 (2 * n)) :=
    Nat.finite_of_card_ne_zero (by rw [GaloisField.card 2 (2 * n) (by omega)]; positivity)
  have hdvd : 3 ∣ Nat.card (GaloisField 2 (2 * n))ˣ := by
    rw [card_units_galoisField hn]
    exact h3.trans (add_one_dvd_sq_sub_one _)
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
  obtain ⟨l, hl⟩ := exists_frobQ_ne hn
  have hm : ζ ^ ((2 : ℤ) ^ n + 1) = 1 := by
    rw [show ((2 : ℤ) ^ n + 1) = ((2 ^ n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
    exact orderOf_dvd_iff_pow_eq_one.1 (hζ ▸ h3)
  have hle := langTorusE5_le_fixedGroup (frobQ 2 n) (frobQ_frobQ 2 n hn) hl
    (units_map_frobQ ζ) hm
  refine ⟨(langRootU (GaloisField 2 (2 * n)) (frobQ 2 n)).subgroupOf
      (fixedGroup (GaloisField 2 (2 * n)) (frobQ 2 n)),
    (langTorusE5 (GaloisField 2 (2 * n)) (frobQ 2 n) l ζ).subgroupOf
      (fixedGroup (GaloisField 2 (2 * n)) (frobQ 2 n)), ?_, ?_, ?_, ?_, ?_⟩
  · intro hbot
    apply langRootU_ne_bot (frobQ 2 n)
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hxU : (⟨x, (Subgroup.mem_inf.1 hx).2⟩ :
        ↥(fixedGroup (GaloisField 2 (2 * n)) (frobQ 2 n))) ∈
        (langRootU (GaloisField 2 (2 * n)) (frobQ 2 n)).subgroupOf
          (fixedGroup (GaloisField 2 (2 * n)) (frobQ 2 n)) := hx
    rw [hbot, Subgroup.mem_bot] at hxU
    exact congrArg Subtype.val hxU
  · exact (langRootU_isPGroup (frobQ 2 n)).comap_subtype
  · intro x hx
    rw [Subgroup.mem_set_normalizer_iff]
    intro y
    simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_set_normalizer_iff.1
      (langTorusE5_le_normalizer (frobQ 2 n) l ζ hx)
      (y : e6Data_valid.minGroup (GaloisField 2 (2 * n)))
  · exact (langTorusE5_isElemAbelian (frobQ 2 n) l hζ).subgroupOf
      (fixedGroup (GaloisField 2 (2 * n)) (frobQ 2 n))
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
      card_langTorusE5 (frobQ 2 n) l hζ]

end TwE6Lang

end CFSG.StandardType
