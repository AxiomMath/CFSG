module

public import CFSG.Assembly.Defs
public import CFSG.Quasithin.Background.B1Restrict

public section

namespace CFSG.Quasithin

variable {V : Type*} [CommGroup V]

theorem rAV_le_of_card_le [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {X A B : Subgroup (MulAut V)}
    (hA : IsA2 X A) (hB : IsA2 X B) (hBA : B ≤ A) (hr : rAV A ≤ 1)
    (hF : Nat.card A * Nat.card (fixV A) ≤ Nat.card B * Nat.card (fixV B)) : rAV B ≤ rAV A := by
  have hA' : Nat.card A = 2 ^ rk A := B1.card_elemAbelian hA.2.2
  have hB' : Nat.card B = 2 ^ rk B := B1.card_elemAbelian hB.2.2
  have hfA : Nat.card (fixV A) = 2 ^ rk (fixV A) := card_eq_two_pow hV _
  have hfB : Nat.card (fixV B) = 2 ^ rk (fixV B) := card_eq_two_pow hV _
  have h1 : rk A + rk (fixV A) ≤ rk B + rk (fixV B) := by
    rw [hA', hfA, hB', hfB, ← pow_add, ← pow_add] at hF
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hF
  have h2 := rk_add_rkIdx (fixV A)
  have h3 := rk_add_rkIdx (fixV B)
  have h4 : rk B ≤ rk A := rk_mono hBA
  have h5 : rkIdx (fixV A) ≤ rk A :=
    (B1.card_le_iff hV hA.2.2).1 ((rAV_le_one_iff hV hA).1 hr)
  have hkA : 0 < rk A := hA.rk_pos
  have hkB : 0 < rk B := hB.rk_pos
  have h6 : rkIdx (fixV B) + rk A ≤ rkIdx (fixV A) + rk B := by omega
  unfold rAV
  rw [div_le_div_iff₀ (by exact_mod_cast hkB) (by exact_mod_cast hkA)]
  have h7 : rkIdx (fixV B) * rk A ≤ rkIdx (fixV A) * rk B := by
    zify at h4 h5 h6 ⊢
    nlinarith [mul_nonneg (sub_nonneg.2 h4) (sub_nonneg.2 h5)]
  exact_mod_cast h7

theorem exists_offender_rAV_le [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)}
    (hA : IsA2 X A) (hr : rAV A ≤ 1) :
    ∃ B, B ≤ A ∧ IsFFStarOffender X B ∧ rAV B ≤ rAV A := by
  have h0 : Nat.card V ≤ Nat.card A * Nat.card (fixV A) := (rAV_le_one_iff hV hA).1 hr
  obtain ⟨B, hBA, hB, hBc⟩ := B1.exists_offender_below hA
    (Nat.card A * Nat.card (fixV A) - Nat.card V) (by omega)
  refine ⟨B, hBA, hB, rAV_le_of_card_le hV hA hB.isA2 hBA hr ?_⟩
  omega

theorem qOf_eq_of_offenders [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)}
    {s : ℚ} (hs : s ≤ 1) (hlow : ∀ B, IsFFStarOffender X B → s ≤ rAV B)
    (hex : ∃ A, IsFFStarOffender X A ∧ rAV A ≤ s) : qOf X = (s : WithTop ℚ) := by
  apply le_antisymm
  · obtain ⟨A₁, hA₁, hr₁⟩ := hex
    obtain ⟨A₀, hle, hmin⟩ := B1.exists_isFFStarMin_le hA₁
    have hquad : IsQuadratic A₀ := B1_4_3 hV hmin
    have hr0 : rAV A₀ ≤ rAV A₁ :=
      rAV_le_of_card_le hV hA₁.isA2 hle.1 hle.2.2.1 (B1_4_1 hV hA₁) (le_of_eq hle.2.2.2.symm)
    exact qOf_le_iff.2 ⟨A₀, hmin.1.isA2, hquad, hr0.trans hr₁⟩
  · unfold qOf
    rw [le_kq_iff]
    intro A hA _
    by_cases h1 : 1 ≤ rAV A
    · exact hs.trans h1
    · obtain ⟨B, -, hB, hrB⟩ := exists_offender_rAV_le hV hA (not_le.1 h1).le
      exact (hlow B hB).trans hrB

end CFSG.Quasithin
