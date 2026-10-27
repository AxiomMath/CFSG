module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.CentDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.FamDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg

theorem noSevenCent_of_e9c7Free {J : Type} [Group J] [Finite J] (h : E9C7Free J) :
    NoSevenCent J := by
  intro X R hX hE hcard hR hRne hcent
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨hcomm, hpow⟩ := hE
  haveI : IsMulCommutative X := hcomm
  rcases Subgroup.bot_or_exists_ne_one X with hXbot | ⟨a, haX, ha1⟩
  · rw [hXbot, Subgroup.card_bot] at hcard
    exact absurd hcard (by norm_num)
  have ha3 : a ^ 3 = 1 := hpow a haX
  have hord_a_dvd : orderOf a ∣ 3 := orderOf_dvd_of_pow_eq_one ha3
  have hord_a : orderOf a = 3 := by
    rcases (by norm_num : Nat.Prime 3).eq_one_or_self_of_dvd _ hord_a_dvd with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) ha1
    · exact h3
  have hcard_zp : Nat.card (Subgroup.zpowers a) = 3 := by
    rw [Nat.card_zpowers, hord_a]
  have hzp_ne : Subgroup.zpowers a ≠ X := by
    intro heq
    rw [heq] at hcard_zp
    rw [hcard] at hcard_zp
    exact absurd hcard_zp (by norm_num)
  have hle : Subgroup.zpowers a ≤ X := Subgroup.zpowers_le.mpr haX
  have hbexists : ∃ b : J, b ∈ X ∧ b ∉ Subgroup.zpowers a := by
    by_contra hc
    apply hzp_ne
    apply le_antisymm hle
    intro x hx
    by_contra hx'
    exact hc ⟨x, hx, hx'⟩
  obtain ⟨b, hbX, hbz⟩ := hbexists
  have hb1 : b ≠ 1 := by
    intro hb
    apply hbz
    rw [hb]
    exact Subgroup.one_mem _
  have hb3 : b ^ 3 = 1 := hpow b hbX
  have hab1 : a * b ≠ 1 := by
    intro hab
    apply hbz
    rw [eq_inv_of_mul_eq_one_right hab]
    exact inv_mem (Subgroup.mem_zpowers a)
  have hab21 : a * b ^ 2 ≠ 1 := by
    intro hab2
    have hb2a : b ^ 2 = a⁻¹ := eq_inv_of_mul_eq_one_right hab2
    have hb3' : b * b ^ 2 = 1 := by rw [← pow_succ']; exact hb3
    have hb2b : b ^ 2 = b⁻¹ := eq_inv_of_mul_eq_one_right hb3'
    have hbinv : b⁻¹ = a⁻¹ := hb2b ▸ hb2a
    have hba : b = a := inv_inj.mp hbinv
    exact hbz (by rw [hba]; exact Subgroup.mem_zpowers a)
  have h7dvd : 7 ∣ Nat.card R := by
    rcases hR.card_eq_or_dvd with h1 | hdvd
    · exact absurd (Subgroup.eq_bot_of_card_eq R h1) hRne
    · exact hdvd
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' 7 h7dvd
  let r : J := (x : J)
  have hrR : r ∈ R := x.2
  have hordr : orderOf r = 7 := by
    show orderOf (x : J) = 7
    rw [Subgroup.orderOf_coe, hxord]
  have hr1 : r ≠ 1 := by
    intro hr
    rw [hr, orderOf_one] at hordr
    exact absurd hordr (by norm_num)
  have hr7 : r ^ 7 = 1 := by
    rw [← hordr]
    exact pow_orderOf_eq_one r
  have hab : a * b = b * a := setLike_mul_comm haX hbX
  have har : a * r = r * a := (Subgroup.mem_centralizer_iff.mp (hcent hrR)) a haX
  have hbr : b * r = r * b := (Subgroup.mem_centralizer_iff.mp (hcent hrR)) b hbX
  exact h a b r ⟨ha1, hb1, hab1, hab21, ha3, hb3, hr1, hr7, hab, har, hbr⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg
