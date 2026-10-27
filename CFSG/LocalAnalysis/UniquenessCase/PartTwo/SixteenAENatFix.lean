module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg9Nat

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W] [Finite W]

theorem s16ae_inf_fixV_eq_bot_of_irr {L : Subgroup (MulAut W)} {I : Subgroup W}
    (hI : XMod.IsIrr ↥L I) (hcard : Nat.card ↥I = 8) : I ⊓ fixV L = ⊥ := by
  have hinv : XMod.IsInv ↥L (I ⊓ fixV L) := by
    intro a l hl
    have h : a • l = l := hl.2 a a.2
    rw [h]
    exact hl
  rcases hI.2.2 (I ⊓ fixV L) hinv bot_le inf_le_left with h | h
  · exact h
  · exfalso
    have hfix : ∀ x ∈ I, ∀ g ∈ L, g x = x := fun x hx g hg => by
      have hx' : x ∈ I ⊓ fixV L := by rw [h]; exact hx
      exact hx'.2 g hg
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h2 : 2 ∣ Nat.card ↥I := by rw [hcard]; norm_num
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥I) 2 h2
    have hto : orderOf (t : W) = 2 := (Subgroup.orderOf_coe t).trans ht
    have hZI : Subgroup.zpowers (t : W) ≤ I := Subgroup.zpowers_le.2 t.2
    have hZinv : XMod.IsInv ↥L (Subgroup.zpowers (t : W)) := by
      intro a l hl
      have h' : a • l = l := hfix l (hZI hl) a a.2
      rw [h']
      exact hl
    rcases hI.2.2 (Subgroup.zpowers (t : W)) hZinv bot_le hZI with hb | hI'
    · have : (t : W) = 1 := by
        have h1 : (t : W) ∈ Subgroup.zpowers (t : W) := Subgroup.mem_zpowers _
        rw [hb] at h1
        exact h1
      rw [this, orderOf_one] at hto
      omega
    · have hc : Nat.card ↥(Subgroup.zpowers (t : W)) = 2 := by rw [Nat.card_zpowers, hto]
      rw [hI', hcard] at hc
      omega

theorem s16ae_natSum3_inf_fixV_eq_bot {L : Subgroup (MulAut W)} {J : Subgroup W}
    (h : NatSum3 L J) : J ⊓ fixV L = ⊥ := by
  obtain ⟨I₀, I₁, I₂, hi₀, hi₁, hi₂, hc₀, hc₁, hc₂, h01, h012, hsum⟩ := h
  rw [eq_bot_iff]
  rintro w ⟨hwJ, hwfix⟩
  rw [← hsum] at hwJ
  obtain ⟨u, hu, c, hc, rfl⟩ := Subgroup.mem_sup.1 hwJ
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hu
  have hcomp : ∀ g ∈ L, g a = a ∧ g b = b ∧ g c = c := by
    intro g hg
    have hga : g a ∈ I₀ := hi₀.1 ⟨g, hg⟩ a ha
    have hgb : g b ∈ I₁ := hi₁.1 ⟨g, hg⟩ b hb
    have hgc : g c ∈ I₂ := hi₂.1 ⟨g, hg⟩ c hc
    have hw : g a * g b * g c = a * b * c := by
      have := hwfix g hg
      rwa [map_mul, map_mul] at this
    have hq : g c / c = (a * b) / (g a * g b) :=
      div_eq_div_iff_mul_eq_mul.2 (by rw [mul_comm (g c), hw])
    have h1 : g c / c ∈ (I₀ ⊔ I₁) ⊓ I₂ :=
      ⟨by rw [hq]; exact (I₀ ⊔ I₁).div_mem (Subgroup.mul_mem_sup ha hb)
            (Subgroup.mul_mem_sup hga hgb),
        I₂.div_mem hgc hc⟩
    rw [h012, Subgroup.mem_bot, div_eq_one] at h1
    rw [h1] at hw
    have hab : g a * g b = a * b := mul_right_cancel hw
    have hq2 : g a / a = b / g b :=
      div_eq_div_iff_mul_eq_mul.2 (by rw [hab, mul_comm])
    have h2 : g a / a ∈ I₀ ⊓ I₁ :=
      ⟨I₀.div_mem hga ha, by rw [hq2]; exact I₁.div_mem hb hgb⟩
    rw [h01, Subgroup.mem_bot, div_eq_one] at h2
    rw [h2] at hab
    exact ⟨h2, mul_left_cancel hab, h1⟩
  have hax : a ∈ I₀ ⊓ fixV L := ⟨ha, fun g hg => (hcomp g hg).1⟩
  have hbx : b ∈ I₁ ⊓ fixV L := ⟨hb, fun g hg => (hcomp g hg).2.1⟩
  have hcx : c ∈ I₂ ⊓ fixV L := ⟨hc, fun g hg => (hcomp g hg).2.2⟩
  rw [s16ae_inf_fixV_eq_bot_of_irr hi₀ hc₀, Subgroup.mem_bot] at hax
  rw [s16ae_inf_fixV_eq_bot_of_irr hi₁ hc₁, Subgroup.mem_bot] at hbx
  rw [s16ae_inf_fixV_eq_bot_of_irr hi₂ hc₂, Subgroup.mem_bot] at hcx
  rw [hax, hbx, hcx]
  simp

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
