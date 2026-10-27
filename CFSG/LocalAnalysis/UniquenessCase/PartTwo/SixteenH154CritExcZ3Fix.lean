module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154CritExcZ3Gen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

private theorem s16h_zpowers_eq_of_mem_zpowers_of_prime {G : Type} [Group G] [Finite G]
    {g x : G} {p : ℕ} (hp : p.Prime) (hg : orderOf g = p)
    (hx : x ∈ Subgroup.zpowers g) (hx1 : x ≠ 1) :
    Subgroup.zpowers x = Subgroup.zpowers g := by
  have hdvd : orderOf x ∣ p := hg ▸ orderOf_dvd_of_mem_zpowers hx
  have hne : orderOf x ≠ 1 := fun h => hx1 (orderOf_eq_one_iff.mp h)
  have hxp : orderOf x = p := by
    rcases (Nat.dvd_prime hp).mp hdvd with h | h
    · exact absurd h hne
    · exact h
  have hxle : Subgroup.zpowers x ≤ Subgroup.zpowers g := Subgroup.zpowers_le.mpr hx
  refine Subgroup.eq_of_le_of_card_ge hxle ?_
  rw [Nat.card_zpowers, Nat.card_zpowers, hxp, hg]

private theorem s16h_fixV_zpowers_le_of_mem_zpowers_three {W : Type} [CommGroup W] [Finite W]
    {l x : MulAut W} (hl : orderOf l = 3) (hx : x ∈ Subgroup.zpowers l) (hx1 : x ≠ 1) :
    fixV (Subgroup.zpowers x) ≤ fixV (Subgroup.zpowers l) := by
  rw [s16h_zpowers_eq_of_mem_zpowers_of_prime (by norm_num : Nat.Prime 3) hl hx hx1]

theorem s16h_fix_card_of_prime_Z3 {W : Type} [CommGroup W] [Finite W] (hcard : Nat.card W = 64)
    {l : MulAut W} (hl : orderOf l = 3) (hfpf : ∀ w : W, l w = w → w = 1) {ρ : MulAut W}
    (hρl : ρ * l = l * ρ) {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r) (hρ : orderOf ρ = r) :
    (r = 7 ∧ ∀ w : W, ρ w = w → w = 1) ∨ (r = 5 ∧ Nat.card ↥(fixV (zpowers ρ)) = 4) := by
  classical
  let F : Subgroup W := fixV (Subgroup.zpowers ρ)
  have hFixl : fixV (Subgroup.zpowers l) = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [mem_fixV] at hw
    rw [Subgroup.mem_bot]
    exact hfpf w (hw l (Subgroup.mem_zpowers l))
  have h3dvd : 3 ∣ Nat.card F - 1 := by
    have hmain := s16h_card_dvd_sub_of_fix_card (W := W) (R := Subgroup.zpowers l) (U := F)
      (c := 1) ?_ ?_
    · simpa [Nat.card_zpowers, hl] using hmain
    · intro x hx u hu
      rw [mem_fixV] at hu ⊢
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hx
      intro y hy
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hyx : y * x = x * y := by
        rw [← hj, ← hi]
        exact ((show Commute ρ l from hρl).zpow_zpow j i).eq
      calc
        y (x u) = (y * x) u := by rw [MulAut.mul_apply]
        _ = (x * y) u := by rw [hyx]
        _ = x (y u) := by rw [MulAut.mul_apply]
        _ = x u := by rw [hu y hy]
    · intro x hx hx1
      have hxbot : fixV (Subgroup.zpowers x) ≤ (⊥ : Subgroup W) :=
        (s16h_fixV_zpowers_le_of_mem_zpowers_three hl hx hx1).trans (le_of_eq hFixl)
      have hinf : F ⊓ fixV (Subgroup.zpowers x) = ⊥ := by
        rw [eq_bot_iff]
        intro w hw
        rw [Subgroup.mem_inf] at hw
        exact hxbot hw.2
      rw [hinf, Subgroup.card_bot]
  have hrdvd : r ∣ 64 - Nat.card F := by
    have hmain := s16h_card_dvd_sub_of_fix_card (W := W) (R := Subgroup.zpowers ρ) (U := ⊤)
      (c := Nat.card F) ?_ ?_
    · simpa [Nat.card_zpowers, hρ, Subgroup.card_top, hcard] using hmain
    · intro x _ u _
      exact Subgroup.mem_top (x u)
    · intro x hx hx1
      have hxeq : Subgroup.zpowers x = Subgroup.zpowers ρ :=
        s16h_zpowers_eq_of_mem_zpowers_of_prime hr hρ hx hx1
      rw [top_inf_eq, hxeq]
  have hFdvd : Nat.card F ∣ 64 := by
    simpa [hcard] using Subgroup.card_subgroup_dvd_card F
  have h64 : (64 : ℕ) = 2 ^ 6 := by norm_num
  obtain ⟨k, hk6, hFk⟩ :=
    (Nat.dvd_prime_pow (by norm_num : Nat.Prime 2)).mp (h64 ▸ hFdvd)
  have h3dvd' : 3 ∣ 2 ^ k - 1 := by simpa [hFk] using h3dvd
  have hFval : Nat.card F = 1 ∨ Nat.card F = 4 ∨ Nat.card F = 16 ∨ Nat.card F = 64 := by
    interval_cases k
    · left
      simpa using hFk
    · exfalso
      norm_num at h3dvd'
    · right; left
      simpa using hFk
    · exfalso
      norm_num at h3dvd'
    · right; right; left
      simpa using hFk
    · exfalso
      norm_num at h3dvd'
    · right; right; right
      simpa using hFk
  have hF64 : Nat.card F ≠ 64 := by
    intro h64F
    have htop : F = ⊤ := by
      refine Subgroup.eq_of_le_of_card_ge le_top ?_
      simpa [Subgroup.card_top, hcard, h64F]
    have hρone : ρ = 1 := by
      ext w
      have hw : w ∈ F := by
        rw [htop]
        exact Subgroup.mem_top w
      change w ∈ fixV (Subgroup.zpowers ρ) at hw
      rw [mem_fixV] at hw
      simpa using hw ρ (Subgroup.mem_zpowers ρ)
    have hr1 : r = 1 := by simpa [hρone] using hρ.symm
    exact hr.ne_one hr1
  rcases hFval with h1 | h4 | h16 | h64F
  · have hr7 : r = 7 := by
      have hd : r ∣ 63 := by simpa [h1] using hrdvd
      have hrle : r ≤ 63 := Nat.le_of_dvd (by norm_num) hd
      interval_cases r
      all_goals norm_num at hd
      all_goals norm_num at hr
      all_goals norm_num at ⊢
    refine Or.inl ⟨hr7, ?_⟩
    intro w hw
    have hwF : w ∈ F := by
      change w ∈ fixV (Subgroup.zpowers ρ)
      rw [mem_fixV]
      intro y hy
      exact smul_eq_self_of_mem_zpowers hy hw
    have hFbot : F = ⊥ := Subgroup.card_eq_one.mp h1
    rw [hFbot] at hwF
    simpa using hwF
  · have hr5' : r = 5 := by
      have hd : r ∣ 60 := by simpa [h4] using hrdvd
      have hrle : r ≤ 60 := Nat.le_of_dvd (by norm_num) hd
      interval_cases r
      all_goals norm_num at hd
      all_goals norm_num at hr
      all_goals norm_num at ⊢
    exact Or.inr ⟨hr5', by simpa [F] using h4⟩
  · exfalso
    have hd : r ∣ 48 := by simpa [h16] using hrdvd
    have hrle : r ≤ 48 := Nat.le_of_dvd (by norm_num) hd
    interval_cases r
    all_goals norm_num at hd
    all_goals norm_num at hr
  · exact absurd h64F hF64

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
