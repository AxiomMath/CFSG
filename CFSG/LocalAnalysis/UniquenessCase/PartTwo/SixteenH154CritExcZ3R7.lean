module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154CritExcZ3Fix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Table

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

private theorem s16h_zpowers_eq_of_mem_zpowers_of_prime {G : Type*} [Group G] [Finite G]
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

private theorem s16h_commute_zpowers_mem {G : Type*} [Group G] {a b : G}
    (hab : a * b = b * a) {y : G} (hy : y ∈ Subgroup.zpowers b) : y * a = a * y := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact (show Commute b a from hab.symm).zpow_left n

private theorem s16h_fixV_invariant_of_commute {W : Type} [CommGroup W] {g h : MulAut W}
    (hgh : g * h = h * g) :
    ∀ x ∈ Subgroup.zpowers g, ∀ u ∈ fixV (Subgroup.zpowers h),
      x u ∈ fixV (Subgroup.zpowers h) := by
  intro x hx u hu
  rw [mem_fixV] at hu ⊢
  intro y hy
  have hxh : x * h = h * x := s16h_commute_zpowers_mem (a := h) (b := g) hgh.symm hx
  have hyx : y * x = x * y := s16h_commute_zpowers_mem (a := x) (b := h) hxh hy
  calc y (x u) = (y * x) u := by rw [MulAut.mul_apply]
    _ = (x * y) u := by rw [hyx]
    _ = x (y u) := by rw [MulAut.mul_apply]
    _ = x u := by rw [hu y hy]

theorem s16h_false_of_seven_torus {W : Type} [CommGroup W] [Finite W] (hcard : Nat.card W = 64)
    {l : MulAut W} (hl : orderOf l = 3) (hfpf : ∀ w : W, l w = w → w = 1)
    {R D : Subgroup (MulAut W)} (hRl : R ≤ centralizer ({l} : Set (MulAut W)))
    (hR7 : IsPGroup 7 R) (hR1 : R ≠ ⊥) (hDl : D ≤ centralizer ({l} : Set (MulAut W)))
    (hD : IsElemAbelian 3 D) (hD27 : 27 ≤ Nat.card ↥D)
    (hDR : D ≤ normalizer (R : Set (MulAut W))) : False := by
  classical
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hFixR : ∀ x ∈ R, x ≠ 1 → fixV (Subgroup.zpowers x) = ⊥ := by
    intro x hx hx1
    obtain ⟨k, hk⟩ := hR7.exists_orderOf_eq_pow (⟨x, hx⟩ : R)
    have hxord : orderOf x = 7 ^ k :=
      (Subgroup.orderOf_coe (H := R) (⟨x, hx⟩ : R)).trans hk
    have hkpos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · exfalso
        exact hx1 (orderOf_eq_one_iff.mp (by rw [hxord, hk0, pow_zero]))
      · exact hkpos
    let ρ : MulAut W := x ^ (7 ^ (k - 1))
    have hρmem : ρ ∈ Subgroup.zpowers x := by
      rw [show ρ = x ^ (7 ^ (k - 1)) from rfl]
      exact Subgroup.mem_zpowers_iff.mpr
        ⟨(7 ^ (k - 1) : ℤ), zpow_natCast x (7 ^ (k - 1))⟩
    have hρR : ρ ∈ R := Subgroup.zpowers_le.mpr hx hρmem
    have hρpow : ρ ^ 7 = 1 := by
      have hexp : 7 ^ (k - 1) * 7 = 7 ^ k := by
        rw [← pow_succ, Nat.sub_add_cancel hkpos]
      rw [show ρ = x ^ (7 ^ (k - 1)) from rfl, ← pow_mul, hexp, ← hxord,
        pow_orderOf_eq_one]
    have hlt : 7 ^ (k - 1) < 7 ^ k := by
      rw [← Nat.sub_add_cancel hkpos]
      exact Nat.pow_lt_pow_succ (by norm_num : 1 < 7)
    have hρne : ρ ≠ 1 := by
      intro hρ1
      have hdvd' : orderOf x ∣ 7 ^ (k - 1) :=
        orderOf_dvd_iff_pow_eq_one.mpr
          (by rw [show x ^ (7 ^ (k - 1)) = ρ from rfl, hρ1])
      rw [hxord] at hdvd'
      exact absurd (Nat.le_of_dvd (by positivity) hdvd') (not_le.mpr hlt)
    have hρord : orderOf ρ = 7 := by
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp
        (orderOf_dvd_iff_pow_eq_one.mpr hρpow) with h1 | h7
      · exact absurd (orderOf_eq_one_iff.mp h1) hρne
      · exact h7
    have hρl : ρ * l = l * ρ :=
      Subgroup.mem_centralizer_singleton_iff.mp (hRl hρR)
    have hfixρ1 : ∀ w : W, ρ w = w → w = 1 := by
      rcases s16h_fix_card_of_prime_Z3 (W := W) hcard hl hfpf hρl
        (by norm_num : Nat.Prime 7) (by norm_num : 5 ≤ 7) hρord with
        ⟨_, h⟩ | ⟨h5, _⟩
      · exact h
      · omega
    have hfixρ : fixV (Subgroup.zpowers ρ) = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      rw [Subgroup.mem_bot]
      exact hfixρ1 v (mem_fixV_zpowers_iff_apply.mp hv)
    have hle : fixV (Subgroup.zpowers x) ≤ fixV (Subgroup.zpowers ρ) := by
      intro v hv
      rw [mem_fixV] at hv ⊢
      intro y hy
      exact hv y (Subgroup.zpowers_le.mpr hρmem hy)
    rw [eq_bot_iff]
    exact hle.trans (le_of_eq hfixρ)
  have hFixTop : ∀ x ∈ R, x ≠ 1 →
      Nat.card ↥((⊤ : Subgroup W) ⊓ fixV (Subgroup.zpowers x)) = 1 := by
    intro x hx hx1
    rw [top_inf_eq, hFixR x hx hx1, Subgroup.card_bot]
  have hdvd63 : Nat.card ↥R ∣ 63 := by
    have h := s16h_card_dvd_sub_of_fix_card (W := W) (R := R) (U := ⊤) (c := 1)
      (fun x _ u _ => Subgroup.mem_top (x u)) hFixTop
    simpa [Subgroup.card_top, hcard] using h
  obtain ⟨n, hncard⟩ := hR7.exists_card_eq
  have hncard' : Nat.card ↥R = 7 ^ n := hncard
  have hdvd7n : 7 ^ n ∣ 63 := hncard' ▸ hdvd63
  have hle7n : 7 ^ n ≤ 63 := Nat.le_of_dvd (by positivity) hdvd7n
  have hnle : n ≤ 2 := by
    by_contra h
    have h3 : 3 ≤ n := by omega
    have hpow : 7 ^ 3 ≤ 7 ^ n := Nat.pow_le_pow_right (by norm_num) h3
    omega
  have hcardR : Nat.card ↥R = 7 := by
    interval_cases n
    · exfalso
      exact hR1 (Subgroup.card_eq_one.mp (by simpa using hncard'))
    · simpa using hncard'
    · norm_num at hdvd7n
  have hex : ∃ ρ ∈ R, ρ ≠ 1 := by
    rcases Subgroup.bot_or_exists_ne_one R with hbot | h
    · exact absurd hbot hR1
    · exact h
  obtain ⟨ρ, hρR, hρ1⟩ := hex
  have hρord : orderOf ρ = 7 := by
    have hdvdp : orderOf ρ ∣ 7 := by
      have h := Subgroup.orderOf_dvd_natCard R hρR
      rwa [hcardR] at h
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp hdvdp with h1 | h7
    · exact absurd (orderOf_eq_one_iff.mp h1) hρ1
    · exact h7
  have hRzp : R = Subgroup.zpowers ρ := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hρR) ?_).symm
    simp [Nat.card_zpowers, hρord, hcardR]
  have hEn : D ≤ normalizer
      ((Subgroup.zpowers ρ : Subgroup (MulAut W)) : Set (MulAut W)) := by
    rw [← hRzp]
    exact hDR
  let E : Subgroup (MulAut W) := D ⊓ Subgroup.centralizer ({ρ} : Set (MulAut W))
  have hcardle := s16h_card_le_mul_cent_of_normalizes (X := MulAut W) (e := ρ) (p := 7)
    (q := 3) (E := D) (by norm_num : Nat.Prime 7) hρord (by norm_num : Nat.Prime 3) hEn
    (fun x hx => hD.2 x hx)
  have hEcard : Nat.card ↥D ≤ 3 * Nat.card ↥E := by
    have h := hcardle
    rw [if_pos (by norm_num : 3 ∣ 7 - 1)] at h
    simpa [E] using h
  have hEab : IsElemAbelian 3 E := by simpa [E] using hD.mono inf_le_left
  have hE9 : 9 ≤ Nat.card ↥E := by omega
  have hFixl : fixV (Subgroup.zpowers l) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Subgroup.mem_bot]
    exact hfpf v (mem_fixV_zpowers_iff_apply.mp hv)
  have hFixE : ∀ h ∈ E, h ≠ 1 → fixV (Subgroup.zpowers h) = ⊥ := by
    intro h hhE hh1
    have hhD : h ∈ D := (Subgroup.mem_inf.mp hhE).1
    have hhC : h ∈ Subgroup.centralizer ({ρ} : Set (MulAut W)) :=
      (Subgroup.mem_inf.mp hhE).2
    have hhρ : h * ρ = ρ * h := Subgroup.mem_centralizer_singleton_iff.mp hhC
    have hhl : h * l = l * h := Subgroup.mem_centralizer_singleton_iff.mp (hDl hhD)
    let U : Subgroup W := fixV (Subgroup.zpowers h)
    have hUρ : ∀ x ∈ Subgroup.zpowers ρ, ∀ u ∈ U, x u ∈ U :=
      s16h_fixV_invariant_of_commute (g := ρ) (h := h) hhρ.symm
    have hUl : ∀ x ∈ Subgroup.zpowers l, ∀ u ∈ U, x u ∈ U :=
      s16h_fixV_invariant_of_commute (g := l) (h := h) hhl.symm
    have h7 : 7 ∣ Nat.card ↥U - 1 := by
      have h := s16h_card_dvd_sub_of_fix_card (W := W) (R := Subgroup.zpowers ρ)
        (U := U) (c := 1) hUρ ?_
      · simpa [Nat.card_zpowers, hρord] using h
      · intro x hx hx1
        have hxbot : fixV (Subgroup.zpowers x) = ⊥ := by
          rw [s16h_zpowers_eq_of_mem_zpowers_of_prime (by norm_num : Nat.Prime 7)
            hρord hx hx1]
          exact hFixR ρ hρR hρ1
        rw [hxbot, inf_bot_eq, Subgroup.card_bot]
    have h3 : 3 ∣ Nat.card ↥U - 1 := by
      have h := s16h_card_dvd_sub_of_fix_card (W := W) (R := Subgroup.zpowers l)
        (U := U) (c := 1) hUl ?_
      · simpa [Nat.card_zpowers, hl] using h
      · intro x hx hx1
        have hxbot : fixV (Subgroup.zpowers x) = ⊥ := by
          rw [s16h_zpowers_eq_of_mem_zpowers_of_prime (by norm_num : Nat.Prime 3)
            hl hx hx1]
          exact hFixl
        rw [hxbot, inf_bot_eq, Subgroup.card_bot]
    have hUdvd : Nat.card ↥U ∣ 64 := by
      have h := Subgroup.card_dvd_of_le (le_top : U ≤ (⊤ : Subgroup W))
      simpa [Subgroup.card_top, hcard] using h
    have h64 : (64 : ℕ) = 2 ^ 6 := by norm_num
    obtain ⟨j, hjle, hUj⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 2)).mp
      (h64 ▸ hUdvd)
    have h7' : 7 ∣ 2 ^ j - 1 := by simpa [hUj] using h7
    have h3' : 3 ∣ 2 ^ j - 1 := by simpa [hUj] using h3
    have hUval : Nat.card ↥U = 1 ∨ Nat.card ↥U = 64 := by
      interval_cases j
      · left; simpa using hUj
      · exfalso; norm_num at h7'
      · exfalso; norm_num at h7'
      · exfalso; norm_num at h3'
      · exfalso; norm_num at h7'
      · exfalso; norm_num at h7'
      · right; simpa using hUj
    rcases hUval with hU1 | hU64
    · exact Subgroup.card_eq_one.mp hU1
    · exfalso
      have hUtop : U = ⊤ := by
        refine Subgroup.eq_of_le_of_card_ge le_top ?_
        simpa [Subgroup.card_top, hcard, hU64]
      apply hh1
      ext v
      have hv : v ∈ U := by rw [hUtop]; exact Subgroup.mem_top v
      have hv' : h v = v := mem_fixV.mp hv h (Subgroup.mem_zpowers h)
      simpa using hv'
  have hE9' : 3 ^ 2 ≤ Nat.card ↥E := by
    have h32 : (3 : ℕ) ^ 2 = 9 := by norm_num
    rw [h32]
    exact hE9
  have hbot : (⊥ : Subgroup W) = ⊤ :=
    s16h_eq_top_of_fixV_le (W := W) (p := 3) (by norm_num : Nat.Prime 3)
      (by rw [hcard]; norm_num) (E := E) hEab hE9'
      (F := ⊥) (fun x hx hx1 => le_of_eq (hFixE x hx hx1))
  have hW1 : Nat.card W = 1 := by
    have h := congrArg (fun H : Subgroup W => Nat.card ↥H) hbot
    have h' : (1 : ℕ) = Nat.card W := by
      simpa [Subgroup.card_bot, Subgroup.card_top] using h
    omega
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
