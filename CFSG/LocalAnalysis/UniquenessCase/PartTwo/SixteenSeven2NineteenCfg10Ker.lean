module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2NineteenCfg10Stab
public import CFSG.GroupTheory.SubgroupCardMul

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W] {X Fs : Subgroup (MulAut W)} {I₁ I₂ : Subgroup W}

theorem s16c167_cfg10_ker_ge (F : Cfg10Mod X Fs I₁ I₂) {I : Subgroup W}
    (hI : I = I₁ ∨ I = I₂) : 3 ≤ Nat.card ↥(Fs ⊓ centSub I) := by
  have hstab : Fs ≤ stabSub I := by
    rcases hI with rfl | rfl
    · exact fun f hf => (s16c167_cfg10_stab F hf).1
    · exact fun f hf => (s16c167_cfg10_stab F hf).2
  have hcard := card_autSub_mul (A := Fs) (U := I) hstab
  have ha_dvd : Nat.card (autSub Fs I) ∣ 27 := by
    rw [← s16c167_cfg10_F_card F.el]
    exact ⟨_, hcard.symm⟩
  have hrk : rk ↥I = 4 := by
    rcases hI with rfl | rfl
    · exact F.rk₁
    · exact F.rk₂
  have hcardI : Nat.card ↥I = 2 ^ 4 := by
    rw [card_eq_two_pow F.sq I, hrk]
  have hcomm : ∀ a b : ↥I, a * b = b * a := fun a b => mul_comm a b
  have hpow : ∀ a : ↥I, a ^ 2 = 1 := fun a => Subtype.ext (by
    simpa using F.sq (a : W))
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary
    (p := 2) hcomm hpow hcardI
  have hMulAut : Nat.card (MulAut ↥I) = 20160 := by
    rw [CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e,
      CFSG.SectionRank.Ccomm.card_GL_zmod (p := 2)]
    decide
  have ha_dvd' : Nat.card (autSub Fs I) ∣ 20160 := by
    rw [← hMulAut]
    exact Subgroup.card_subgroup_dvd_card (autSub Fs I)
  have ha9 : Nat.card (autSub Fs I) ≤ 9 := by
    have h := Nat.dvd_gcd ha_dvd ha_dvd'
    rw [show Nat.gcd 27 20160 = 9 from by norm_num] at h
    exact Nat.le_of_dvd (by norm_num) h
  have h27 : Nat.card (autSub Fs I) * Nat.card ↥(Fs ⊓ centSub I) = 27 :=
    hcard.trans (s16c167_cfg10_F_card F.el)
  have hle : 27 ≤ 9 * Nat.card ↥(Fs ⊓ centSub I) := by
    calc 27 = Nat.card (autSub Fs I) * Nat.card ↥(Fs ⊓ centSub I) := h27.symm
      _ ≤ 9 * Nat.card ↥(Fs ⊓ centSub I) := Nat.mul_le_mul_right _ ha9
  omega

theorem s16c167_cfg10_ker_card (F : Cfg10Mod X Fs I₁ I₂) {I : Subgroup W}
    (hI : I = I₁ ∨ I = I₂) : Nat.card ↥(Fs ⊓ centSub I) = 3 := by
  set q := Nat.card ↥(Fs ⊓ centSub I₁) with hq
  have hqeq : Nat.card ↥(Fs ⊓ centSub I₂) = q := by
    rw [hq]
    exact s16c167_cfg10_ker_card_eq F
  have hprod := CFSG.card_mul_card_le_of_inf_eq_bot
    (A := Fs) (D := Fs ⊓ centSub I₁) (D' := Fs ⊓ centSub I₂)
    inf_le_left inf_le_left (s16c167_cfg10_ker_inf F)
  have hq2 : q * q ≤ 27 := by
    rw [← hq, hqeq, s16c167_cfg10_F_card F.el] at hprod
    exact hprod
  have hge : 3 ≤ q := by
    rw [hq]
    exact s16c167_cfg10_ker_ge (I := I₁) F (Or.inl rfl)
  have hdvd : q ∣ 27 := by
    rw [hq]
    have h := Subgroup.card_dvd_of_le (inf_le_left : Fs ⊓ centSub I₁ ≤ Fs)
    rwa [s16c167_cfg10_F_card F.el] at h
  have hq3 : q = 3 := by
    have hdvd3 : q ∣ 3 ^ 3 := by
      rw [show (3 : ℕ) ^ 3 = 27 by norm_num]
      exact hdvd
    obtain ⟨k, hk3, hqk⟩ :=
      (Nat.dvd_prime_pow Nat.prime_three (m := 3) (i := q)).1 hdvd3
    interval_cases k
    · rw [hqk] at hge; norm_num at hge
    · simpa using hqk
    · rw [hqk] at hq2; norm_num at hq2
    · rw [hqk] at hq2; norm_num at hq2
  rcases hI with rfl | rfl
  · rw [← hq]
    exact hq3
  · rw [hqeq, hq3]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
