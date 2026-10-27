module

public import CFSG.RankThree.PartTwo.Census.Carrier.G2EvenRank
public import CFSG.LieType.Ree.LargeReeInvolutionTwoCentralizers
import CFSG.LieType.Ree.LargeReeInvolutionFusion
public import CFSG.LieType.Ree.ReeGenericPerfect

public section

namespace CFSG.RankThree.PartTwo.Census.Carrier.ReeF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.LargeReeInvolution CFSG.Assembly.RankThreeEven ReeTag

theorem two_pow_odd_mod_three (m : ℕ) : 2 ^ (2 * m + 1) % 3 = 2 := by
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem not_three_dvd_card_centralZ (m : ℕ) :
    ¬ 3 ∣ (2 ^ (2 * m + 1)) ^ 12 * (2 ^ (2 * m + 1) - 1) * ((2 ^ (2 * m + 1)) ^ 2 + 1) := by
  have hq := two_pow_odd_mod_three m
  have hq1 : 1 ≤ 2 ^ (2 * m + 1) := Nat.one_le_two_pow
  set q := 2 ^ (2 * m + 1)
  have h12 : q ^ 12 % 3 = 1 := by rw [Nat.pow_mod, hq]
  have h2 : (q ^ 2 + 1) % 3 = 2 := by rw [Nat.add_mod, Nat.pow_mod, hq]
  have h1 : (q - 1) % 3 = 1 := by omega
  rw [Nat.dvd_iff_mod_eq_zero, Nat.mul_mod, Nat.mul_mod (q ^ 12), h12, h1, h2]
  norm_num

variable {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K F4.prime]

theorem threeRankLeOne_centralZ (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    ThreeRankLeOne (F4.reeGamma K m ⊓ Subgroup.centralizer {centralZ K m 1} :
      Subgroup (ModGL F4.tag K)) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hcard, -⟩ :=
    large_Ree_two_involution_centralizers m hm K hK
  exact threeRankLeOne_of_not_dvd (by rw [hcard]; exact not_three_dvd_card_centralZ m)

theorem threeRankLeOne_sylowL (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    ThreeRankLeOne (F4.reeGamma K m ⊓ Subgroup.centralizer {sylowL m K 1} :
      Subgroup (ModGL F4.tag K)) := by
  obtain ⟨-, -, -, -, -, hC, hQR, hQn, -, hQcard, ⟨eSL⟩, -⟩ :=
    large_Ree_two_involution_centralizers m hm K hK
  have : CharP K 2 := ‹CharP K F4.prime›
  have hQ2 : IsPGroup 2 (tKernel K m) :=
    IsPGroup.of_card (n := (2 * m + 1) * 9) (by rw [hQcard, pow_mul])
  have hRN : rankOneGroupOne K m ≤ Subgroup.normalizer (tKernel K m : Set (ModGL F4.tag K)) := by
    rw [hC] at hQn
    have hle := (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mp hQn
    exact le_sup_right.trans hle
  exact ThreeRankLeOne.of_eq hC (ThreeRankLeOne.sup hQ2 hRN hQR
    (ThreeRankLeOne.of_mulEquiv eSL threeRankLeOne_SL2))

theorem localRank_three_reeGamma (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    localRank 3 (F4.reeGamma K m) ≤ 2 := by
  refine localRank_three_le_two_of_centralizers fun s hs => ?_
  have hs2 : (s : ModGL F4.tag K) ^ 2 = 1 := by
    rw [← Subgroup.coe_pow, ← hs, pow_orderOf_eq_one, Subgroup.coe_one]
  have hs1 : (s : ModGL F4.tag K) ≠ 1 := by
    intro h1
    have : s = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hs
    exact absurd hs (by norm_num)
  have hconj : ∀ s₀ : ModGL F4.tag K, ∀ x ∈ F4.reeGamma K m, x * s * x⁻¹ = s₀ →
      ThreeRankLeOne (F4.reeGamma K m ⊓ Subgroup.centralizer {s₀} : Subgroup (ModGL F4.tag K)) →
      ThreeRankLeOne (Subgroup.centralizer {s} : Subgroup (F4.reeGamma K m)) := by
    intro s₀ x hx hxs h
    have hs₀ : s₀ ∈ F4.reeGamma K m := by
      rw [← hxs]
      exact mul_mem (mul_mem hx s.2) (inv_mem hx)
    have hst : IsConj s ⟨s₀, hs₀⟩ := isConj_iff.mpr ⟨⟨x, hx⟩, Subtype.ext hxs⟩
    exact ThreeRankLeOne.centralizer_of_isConj hst (ThreeRankLeOne.centralizer_of_le le_rfl h)
  rcases (large_Ree_every_involution_fuses m hm K hK).1 s s.2 hs2 hs1 with ⟨x, hx, hxs⟩ |
      ⟨x, hx, hxs⟩
  · rw [sylowH_zero_eq_centralZ] at hxs
    exact hconj _ x hx hxs (threeRankLeOne_centralZ hm hK)
  · exact hconj _ x hx hxs (threeRankLeOne_sylowL hm hK)

theorem nonempty_derivedCentralQuotient_equiv (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    Nonempty (CFSG.Blueprint.DerivedCentralQuotient (F4.reeGamma K m) ≃* F4.reeGamma K m) := by
  have hcomm := (ReeTag.ree_generic_fixed_group_perfect .F4 m hm K hK).2.1
  have hD : ⁅F4.reeGamma K m, F4.reeGamma K m⁆ = F4.reeGamma K m := by
    rw [← Subgroup.map_subtype_commutator, hcomm, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  let e₁ : ↥⁅F4.reeGamma K m, F4.reeGamma K m⁆ ≃* F4.reeGamma K m := MulEquiv.subgroupCongr hD
  have hZ : Subgroup.center ↥⁅F4.reeGamma K m, F4.reeGamma K m⁆ = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : e₁ z ∈ Subgroup.center (F4.reeGamma K m) :=
      Subgroup.mem_center_iff.2 fun g => by
        obtain ⟨y, rfl⟩ := e₁.surjective g
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz y]
    rw [ReeTag.large_Ree_fixed_group_center_trivial m K hK, Subgroup.mem_bot] at hz'
    exact Subgroup.mem_bot.2 (e₁.injective (hz'.trans (map_one e₁).symm))
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans e₁)⟩

end CFSG.RankThree.PartTwo.Census.Carrier.ReeF4
