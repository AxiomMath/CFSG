module

public import CFSG.LocalAnalysis.StandardType.GGSporKLamOrders

public section

namespace CFSG.GGQ2Prime

open CFSG.Assembly CFSG.StandardType

private theorem pptp6_labOrd_twA_3 :
    CFSG.StandardType.SporadicShape.labOrd ⟨.twA, 3, 1⟩ = 25920 := by
  decide +kernel

private theorem pptp6_labOrd_B_3 :
    CFSG.StandardType.SporadicShape.labOrd ⟨.B, 3, 1⟩ = 1451520 := by
  decide +kernel

private theorem pptp6_labOrd_B_4 :
    CFSG.StandardType.SporadicShape.labOrd ⟨.B, 4, 1⟩ = 47377612800 := by
  decide +kernel

private theorem pptp6_labOrd_C_3 :
    CFSG.StandardType.SporadicShape.labOrd ⟨.C, 3, 1⟩ = 1451520 := by
  decide +kernel

private theorem pptp6_labOrd_C_4 :
    CFSG.StandardType.SporadicShape.labOrd ⟨.C, 4, 1⟩ = 47377612800 := by
  decide +kernel

private theorem pptp6_labOrd_D_3 :
    CFSG.StandardType.SporadicShape.labOrd ⟨.D, 3, 1⟩ = 20160 := by
  decide +kernel

private theorem pptp6_labOrd_D_4 :
    CFSG.StandardType.SporadicShape.labOrd ⟨.D, 4, 1⟩ = 174182400 := by
  decide +kernel

private theorem pptp6_labOrd_twD_2 :
    CFSG.StandardType.SporadicShape.labOrd ⟨.twD, 2, 1⟩ = 60 := by
  decide +kernel

private theorem pptp6_labOrd_twD_3 :
    CFSG.StandardType.SporadicShape.labOrd ⟨.twD, 3, 1⟩ = 25920 := by
  decide +kernel

private theorem pptp6_labOrd_twD_4 :
    CFSG.StandardType.SporadicShape.labOrd ⟨.twD, 4, 1⟩ = 197406720 := by
  decide +kernel

private theorem pptp6_labOrd_F4_0 :
    CFSG.StandardType.SporadicShape.labOrd ⟨.F4, 0, 1⟩ = 3311126603366400 := by
  decide +kernel

private theorem pptp6_labOrd_triD4_0 :
    CFSG.StandardType.SporadicShape.labOrd ⟨.triD4, 0, 1⟩ = 211341312 := by
  decide +kernel

private theorem pptp6_labOrd_B2der_0 :
    CFSG.StandardType.SporadicShape.labOrd ⟨.B2der, 0, 1⟩ = 360 := by
  decide +kernel

private theorem pptp6_labOrd_G2der_0 :
    CFSG.StandardType.SporadicShape.labOrd ⟨.G2der, 0, 1⟩ = 6048 := by
  decide +kernel

private theorem pptp6_labOrd_twF4der_0 :
    CFSG.StandardType.SporadicShape.labOrd ⟨.twF4der, 0, 1⟩ = 17971200 := by
  decide +kernel

theorem label_one_eleven_cases (lab : LargeEvenLabel) (hl : LargeEvenInLambda2 lab)
    (hn : lab.n = 1) (h11 : 11 ∣ CFSG.StandardType.SporadicShape.labOrd lab) :
    lab.tag = .A ∨
      (lab.tag = .twA ∧ 4 ≤ lab.rank) ∨
      ((lab.tag = .B ∨ lab.tag = .C ∨ lab.tag = .D ∨ lab.tag = .twD) ∧ 5 ≤ lab.rank) ∨
      lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .E7 ∨ lab.tag = .E8 := by
  rcases lab with ⟨t, r, n⟩
  subst hn
  dsimp only
  cases t <;> simp only [LargeEvenInLambda2] at hl
  · simp
  ·
    simp
    have h2 : 2 ≤ r := hl.2.1
    have hne2 : r ≠ 2 := by
      intro h
      exact absurd (hl.2.2 h) (by norm_num)
    by_contra h4
    have hr : r = 3 := by omega
    subst hr
    rw [pptp6_labOrd_twA_3] at h11
    norm_num at h11
  ·
    simp
    have h2 : 2 ≤ r := hl.2.1
    have hne2 : r ≠ 2 := by
      intro h
      exact absurd (hl.2.2 h) (by norm_num)
    by_contra h5
    have hr : r = 3 ∨ r = 4 := by omega
    rcases hr with h | h
    · subst h
      rw [pptp6_labOrd_B_3] at h11
      norm_num at h11
    · subst h
      rw [pptp6_labOrd_B_4] at h11
      norm_num at h11
  ·
    simp
    have h2 : 2 ≤ r := hl.2.1
    have hne2 : r ≠ 2 := by
      intro h
      exact absurd (hl.2.2 h) (by norm_num)
    by_contra h5
    have hr : r = 3 ∨ r = 4 := by omega
    rcases hr with h | h
    · subst h
      rw [pptp6_labOrd_C_3] at h11
      norm_num at h11
    · subst h
      rw [pptp6_labOrd_C_4] at h11
      norm_num at h11
  ·
    simp
    have h3 : 3 ≤ r := hl.2
    by_contra h5
    have hr : r = 3 ∨ r = 4 := by omega
    rcases hr with h | h
    · subst h
      rw [pptp6_labOrd_D_3] at h11
      norm_num at h11
    · subst h
      rw [pptp6_labOrd_D_4] at h11
      norm_num at h11
  ·
    simp
    have h2 : 2 ≤ r := hl.2
    by_contra h5
    have hr : r = 2 ∨ r = 3 ∨ r = 4 := by omega
    rcases hr with h | h | h
    · subst h
      rw [pptp6_labOrd_twD_2] at h11
      norm_num at h11
    · subst h
      rw [pptp6_labOrd_twD_3] at h11
      norm_num at h11
    · subst h
      rw [pptp6_labOrd_twD_4] at h11
      norm_num at h11
  ·
    simp
  ·
    simp
  ·
    simp
  ·
    simp
    have hr : r = 0 := hl.2
    subst hr
    rw [pptp6_labOrd_F4_0] at h11
    norm_num at h11
  ·
    simp
  ·
    simp
    have hr : r = 0 := hl.2
    subst hr
    rw [pptp6_labOrd_triD4_0] at h11
    norm_num at h11
  ·
    simp
    omega
  ·
    simp
    omega
  ·
    simp
    omega
  ·
    simp
    have hr : r = 0 := hl.2.1
    subst hr
    rw [pptp6_labOrd_B2der_0] at h11
    norm_num at h11
  ·
    simp
    have hr : r = 0 := hl.2.1
    subst hr
    rw [pptp6_labOrd_G2der_0] at h11
    norm_num at h11
  ·
    simp
    have hr : r = 0 := hl.2.1
    subst hr
    rw [pptp6_labOrd_twF4der_0] at h11
    norm_num at h11

end CFSG.GGQ2Prime

end
