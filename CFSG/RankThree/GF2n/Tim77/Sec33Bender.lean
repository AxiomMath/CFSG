module

public import CFSG.RankThree.GF2n.BenderTwoTrans
public import CFSG.GH74.Uniqueness.Bender.SuzukiOdd
public import CFSG.GH74.Uniqueness.Bender.LinearOdd

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG.GH74.Uniqueness.Bender CFSG.RankThree.GF2n CFSG.CGT.Timmesfeld75 Subgroup

variable {K : Type} [Group K]

@[expose] def Sec33DihTrans (K : Type) [Group K] (m : ℕ) : Prop :=
  ∀ a x a' x' : K, a * a = 1 → x * x = 1 → a ≠ x → (a * x) ^ m = 1 →
    a' * a' = 1 → x' * x' = 1 → a' ≠ x' → (a' * x') ^ m = 1 →
    ∃ g : K, g * a * g⁻¹ = a' ∧ g * x * g⁻¹ = x'

section Generic

variable [Finite K]

theorem sec33_exists_sylow_rootCenter_of_invol {n i e : ℕ} (h : BenderType K n i e) {x : K}
    (hx : x * x = 1) (hx1 : x ≠ 1) : ∃ Q : Sylow 2 K, x ∈ rootCenter (Q : Subgroup K) := by
  obtain ⟨Q, hQ⟩ := exists_sylow_mem_of_mul_self hx
  obtain ⟨t, hc⟩ := h.exists_benderCore Q
  exact ⟨Q, hc.mem_rootCenter_of_mul_self hQ hx⟩

theorem sec33_exists_mem_smul_eq_of_ne {n i e : ℕ} (h : BenderType K n i e) {Q R₁ R₂ : Sylow 2 K}
    (h₁ : R₁ ≠ Q) (h₂ : R₂ ≠ Q) : ∃ p ∈ (Q : Subgroup K), p • R₁ = R₂ := by
  obtain ⟨t, hc⟩ := h.exists_benderCore Q
  have key : ∀ R : Sylow 2 K, R ≠ Q → ∃ p ∈ (Q : Subgroup K), R = (p * t) • Q := by
    intro R hR
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K Q R
    have hgB : g ∉ borel (Q : Subgroup K) := fun hgN =>
      hR (by rw [← hg]; exact Sylow.smul_eq_iff_mem_normalizer.mpr hgN)
    obtain ⟨p, hp, m, hm, rfl⟩ := hc.bruhat hgB
    exact ⟨p, hp, by rw [← hg, mul_smul, Sylow.smul_eq_iff_mem_normalizer.mpr hm]⟩
  obtain ⟨p₁, hp₁, rfl⟩ := key R₁ h₁
  obtain ⟨p₂, hp₂, rfl⟩ := key R₂ h₂
  refine ⟨p₂ * p₁⁻¹, (Q : Subgroup K).mul_mem hp₂ ((Q : Subgroup K).inv_mem hp₁), ?_⟩
  rw [← mul_smul, show p₂ * p₁⁻¹ * (p₁ * t) = p₂ * t by group]

theorem sec33_partner_unique {n i : ℕ} (h : BenderType K n i 1) {m : ℕ} (hm : Odd m)
    (hT : Sec33DihTrans K m) {S : Sylow 2 K} {a b x : K} (ha : a ∈ rootCenter (S : Subgroup K))
    (hb : b ∈ rootCenter (S : Subgroup K)) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hx : x * x = 1)
    (hx1 : x ≠ 1) (hxS : x ∉ (S : Subgroup K)) (hax : (a * x) ^ m = 1) (hbx : (b * x) ^ m = 1) :
    a = b := by
  have haS : a ∈ (S : Subgroup K) := rootCenter_le _ ha
  have hbS : b ∈ (S : Subgroup K) := rootCenter_le _ hb
  have haa : a * a = 1 := by
    obtain ⟨t, hc⟩ := h.exists_benderCore S
    exact hc.center_sq a ha
  have hbb : b * b = 1 := by
    obtain ⟨t, hc⟩ := h.exists_benderCore S
    exact hc.center_sq b hb
  obtain ⟨g, hga, hgx⟩ := hT a x b x haa hx (fun h' => hxS (h' ▸ haS)) hax hbb hx
    (fun h' => hxS (h' ▸ hbS)) hbx
  obtain ⟨Qx, hQx⟩ := sec33_exists_sylow_rootCenter_of_invol h hx hx1
  obtain ⟨tx, hcx⟩ := h.exists_benderCore Qx
  have hCx := hcx.centralizer_eq_of_e_one hQx hx1
  have hgx' : g ∈ centralizer ({x} : Set K) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact mul_inv_eq_iff_eq_mul.mp hgx
  rw [hCx] at hgx'
  obtain ⟨tS, hcS⟩ := h.exists_benderCore S
  have haB : a ∈ borel (S : Subgroup K) := le_borel _ haS
  have ha2 : orderOf a = 2 := (hcS.involution_iff.mpr ⟨ha, ha1⟩).2
  have hgB : g ∈ borel (S : Subgroup K) := by
    have h1 : g⁻¹ ∈ borel (S : Subgroup K) := by
      refine hcS.mem_borel_of_conj haB ha2 ?_
      rw [inv_inv, hga]
      exact le_borel _ hbS
    simpa using (borel (S : Subgroup K)).inv_mem h1
  have hgS : g ∈ (S : Subgroup K) := by
    have hP : IsPGroup 2 (zpowers g) :=
      IsPGroup.to_le Qx.isPGroup' ((Subgroup.zpowers_le).mpr hgx')
    have h1 : g ∈ zpowers g ⊓ normalizer (S : Set K) :=
      ⟨Subgroup.mem_zpowers g, hgB⟩
    rw [hP.inf_normalizer_sylow S] at h1
    exact h1.2
  by_contra hab
  have hg1 : g ≠ 1 := by
    rintro rfl
    apply hab
    simpa using hga
  have hQxS : Qx = S := by
    refine hcS.sylow_eq_of_ne_bot (V := zpowers g) ?_ ?_ ?_
    · intro hbot
      apply hg1
      have : g ∈ (⊥ : Subgroup K) := hbot ▸ Subgroup.mem_zpowers g
      exact Subgroup.mem_bot.mp this
    · exact (Subgroup.zpowers_le).mpr hgS
    · exact (Subgroup.zpowers_le).mpr hgx'
  apply hxS
  rw [← hQxS]
  exact rootCenter_le _ hQx

omit [Finite K] in
theorem sec33_eq_one_of_sq_of_pow {g : K} (hg : g * g = 1) {m : ℕ} (hm : Odd m) (hgm : g ^ m = 1) :
    g = 1 := by
  obtain ⟨k, rfl⟩ := hm
  have h2 : g ^ 2 = 1 := by rw [sq]; exact hg
  rw [pow_succ, pow_mul, h2, one_pow, one_mul] at hgm
  exact hgm

theorem sec33_partner_exists {n i : ℕ} (h : BenderType K n i 1) {m : ℕ} (hm : Odd m)
    (hT : Sec33DihTrans K m) (hne : ∃ a x : K, a * a = 1 ∧ x * x = 1 ∧ a ≠ x ∧ (a * x) ^ m = 1)
    {P P' : Sylow 2 K} (hPP : P ≠ P') {x : K} (hx : x ∈ rootCenter (P' : Subgroup K))
    (hx1 : x ≠ 1) :
    ∃ a ∈ rootCenter (P : Subgroup K), a ≠ 1 ∧ (a * x) ^ m = 1 := by
  obtain ⟨a₀, x₀, ha₀, hx₀, hne₀, hm₀⟩ := hne
  obtain ⟨tP', hcP'⟩ := h.exists_benderCore P'
  have hxx : x * x = 1 := hcP'.center_sq x hx
  have hx₀1 : x₀ ≠ 1 := by
    intro h1
    apply hne₀
    rw [h1, mul_one] at hm₀
    rw [h1]
    exact sec33_eq_one_of_sq_of_pow ha₀ hm hm₀
  have ha₀1 : a₀ ≠ 1 := by
    intro h1
    apply hne₀
    rw [h1, one_mul] at hm₀
    rw [h1]
    exact (sec33_eq_one_of_sq_of_pow hx₀ hm hm₀).symm
  obtain ⟨c, hc⟩ := isConj_iff.mp (h.lemma_3_4_a hx₀ hx₀1 hxx hx1)
  have hconj : ∀ y : K, c * y * c⁻¹ * (c * y * c⁻¹) = c * (y * y) * c⁻¹ := fun y => by group
  set a₁ := c * a₀ * c⁻¹ with ha₁def
  have ha₁ : a₁ * a₁ = 1 := by rw [ha₁def, hconj, ha₀]; group
  have ha₁1 : a₁ ≠ 1 := by
    intro h1
    apply ha₀1
    have : a₀ = c⁻¹ * a₁ * c := by rw [ha₁def]; group
    rw [this, h1]
    group
  have ha₁x : a₁ ≠ x := by
    intro h1
    apply hne₀
    have : a₀ = c⁻¹ * a₁ * c := by rw [ha₁def]; group
    rw [this, h1, ← hc]
    group
  have hpow : (a₁ * x) ^ m = 1 := by
    have : a₁ * x = c * (a₀ * x₀) * c⁻¹ := by rw [ha₁def, ← hc]; group
    rw [this, conj_pow, hm₀]
    group
  obtain ⟨Q₁, hQ₁⟩ := sec33_exists_sylow_rootCenter_of_invol h ha₁ ha₁1
  have hQ₁P' : Q₁ ≠ P' := by
    intro hQ
    rw [hQ] at hQ₁
    have hcomm : a₁ * x = x * a₁ := (mem_rootCenter_iff.mp hx).2 a₁ (rootCenter_le _ hQ₁)
    have hsq : (a₁ * x) * (a₁ * x) = 1 := by
      calc (a₁ * x) * (a₁ * x) = a₁ * (x * a₁) * x := by group
        _ = a₁ * (a₁ * x) * x := by rw [← hcomm]
        _ = (a₁ * a₁) * (x * x) := by group
        _ = 1 := by rw [ha₁, hxx, one_mul]
    have h1 := sec33_eq_one_of_sq_of_pow hsq hm hpow
    apply ha₁x
    calc a₁ = a₁ * x * x := by rw [mul_assoc, hxx, mul_one]
      _ = x := by rw [h1, one_mul]
  obtain ⟨p, hpP', hpQ⟩ := sec33_exists_mem_smul_eq_of_ne h (Q := P') (R₁ := Q₁) (R₂ := P) hQ₁P'
    hPP
  refine ⟨p * a₁ * p⁻¹, ?_, ?_, ?_⟩
  · rw [mem_rootCenter_iff]
    obtain ⟨hQa, hQc⟩ := mem_rootCenter_iff.mp hQ₁
    refine ⟨?_, fun y hy => ?_⟩
    · rw [← hpQ, mem_smul_sylow_iff, show p⁻¹ * (p * a₁ * p⁻¹) * p = a₁ by group]
      exact hQa
    · rw [← hpQ, mem_smul_sylow_iff] at hy
      have := hQc _ hy
      calc y * (p * a₁ * p⁻¹) = p * ((p⁻¹ * y * p) * a₁) * p⁻¹ := by group
        _ = p * (a₁ * (p⁻¹ * y * p)) * p⁻¹ := by rw [this]
        _ = p * a₁ * p⁻¹ * y := by group
  · intro h1
    apply ha₁1
    have : a₁ = p⁻¹ * (p * a₁ * p⁻¹) * p := by group
    rw [this, h1]
    group
  · have hpx : p * x = x * p := (mem_rootCenter_iff.mp hx).2 p hpP'
    have : p * a₁ * p⁻¹ * x = p * (a₁ * x) * p⁻¹ := by
      calc p * a₁ * p⁻¹ * x = p * a₁ * (p⁻¹ * x * p) * p⁻¹ := by group
        _ = p * a₁ * x * p⁻¹ := by
          have : p⁻¹ * x * p = x := by
            calc p⁻¹ * x * p = p⁻¹ * (x * p) := by group
              _ = p⁻¹ * (p * x) := by rw [hpx]
              _ = x := by group
          rw [this]
        _ = p * (a₁ * x) * p⁻¹ := by group
    rw [this, conj_pow, hpow]
    group


omit [Finite K] in
theorem sec33_orderOf_mul_invol {m : ℕ} (hm : m.Prime) {a x : K} (hax : a ≠ x) (hx : x * x = 1)
    (hp : (a * x) ^ m = 1) : orderOf (a * x) = m := by
  haveI : Fact m.Prime := ⟨hm⟩
  refine orderOf_eq_prime hp fun h1 => hax ?_
  have : a = x⁻¹ := eq_inv_of_mul_eq_one_left h1
  rw [this]
  exact inv_eq_of_mul_eq_one_right hx

theorem sec33_exists_centralizes_conj_of_invert {m : ℕ} (hm : m.Prime) (hodd : Odd m)
    (hinvol : ∀ z : K, z * z = 1 → z ≠ 1 → IsPGroup 2 (centralizer ({z} : Set K)))
    {u x y : K} (hu : orderOf u = m) (hx : x * x = 1) (hy : y * y = 1) (hxu : x * u * x = u⁻¹)
    (hyu : y * u * y = u⁻¹) : ∃ c : K, c * u = u * c ∧ c * x * c⁻¹ = y := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have hxu' : x * u = u⁻¹ * x := by
    calc x * u = x * u * x * x := by rw [mul_assoc (x * u) x x, hx, mul_one]
      _ = u⁻¹ * x := by rw [hxu]
  have hyu' : y * u⁻¹ = u * y := by
    have h1 : y * u⁻¹ * y = u := by
      have := congrArg (· ⁻¹) hyu
      simpa [mul_assoc, hyi] using this
    calc y * u⁻¹ = y * u⁻¹ * y * y := by rw [mul_assoc (y * u⁻¹) y y, hy, mul_one]
      _ = u * y := by rw [h1]
  have hyu'' : y * u = u⁻¹ * y := by
    calc y * u = y * u * y * y := by rw [mul_assoc (y * u) y y, hy, mul_one]
      _ = u⁻¹ * y := by rw [hyu]
  set c := y * x with hc
  have hcu : c * u = u * c := by
    calc c * u = y * (x * u) := by rw [hc, mul_assoc]
      _ = y * (u⁻¹ * x) := by rw [hxu']
      _ = (y * u⁻¹) * x := by rw [mul_assoc]
      _ = (u * y) * x := by rw [hyu']
      _ = u * c := by rw [hc, mul_assoc]
  have hxc : x * c * x = c⁻¹ := by
    calc x * c * x = x * y * (x * x) := by rw [hc]; group
      _ = x * y := by rw [hx, mul_one]
      _ = c⁻¹ := by rw [hc, mul_inv_rev, hxi, hyi]
  have hcodd : Odd (orderOf c) := by
    by_contra hev
    have hev' : Even (orderOf c) := Nat.not_odd_iff_even.mp hev
    have hpos : orderOf c ≠ 0 := (orderOf_pos c).ne'
    have h2 : 2 ∣ orderOf c := even_iff_two_dvd.mp hev'
    set z := c ^ (orderOf c / 2) with hz
    have hz2 : orderOf z = 2 := orderOf_pow_orderOf_div hpos h2
    have hzz : z * z = 1 := by
      have := pow_orderOf_eq_one z
      rwa [hz2, sq] at this
    have hz1 : z ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hz2
      omega
    have hzu : u * z = z * u := (Commute.pow_left (show Commute c u from hcu)
      (orderOf c / 2)).symm.eq
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hP := hinvol z hzz hz1
    have huC : u ∈ centralizer ({z} : Set K) := Subgroup.mem_centralizer_singleton_iff.mpr hzu
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hP) ⟨u, huC⟩
    rw [Subgroup.orderOf_mk, hu] at hk
    rcases k with _ | j
    · rw [pow_zero] at hk
      exact hm.one_lt.ne' hk
    · obtain ⟨t, ht⟩ := hodd
      rw [hk, pow_succ] at ht
      omega
  obtain ⟨k, hk⟩ := exists_sq_eq_of_odd_orderOf hcodd
  refine ⟨c ^ k, (Commute.pow_left (show Commute c u from hcu) k).eq, ?_⟩
  have hxk : x * c ^ k * x = (c ^ k)⁻¹ := by
    have h1 := conj_pow (a := x) (b := c) (i := k)
    rw [hxi, show x * c * x = c⁻¹ from hxc, inv_pow] at h1
    exact h1.symm
  have hxk' : x * (c ^ k)⁻¹ * x = c ^ k := by
    have h1 : (x * c ^ k * x)⁻¹ = x * (c ^ k)⁻¹ * x := by
      rw [mul_inv_rev, mul_inv_rev, hxi, mul_assoc]
    rw [← h1, hxk, inv_inv]
  have hx3 : x * (c ^ k)⁻¹ = c ^ k * x := by
    calc x * (c ^ k)⁻¹ = x * (c ^ k)⁻¹ * x * x := by rw [mul_assoc (x * (c ^ k)⁻¹) x x, hx, mul_one]
      _ = c ^ k * x := by rw [hxk']
  calc c ^ k * x * (c ^ k)⁻¹ = c ^ k * (x * (c ^ k)⁻¹) := by rw [mul_assoc]
    _ = c ^ k * (c ^ k * x) := by rw [hx3]
    _ = (c ^ k * c ^ k) * x := by rw [mul_assoc]
    _ = c * x := by rw [hk]
    _ = y := by rw [hc, mul_assoc, hx, mul_one]


theorem sec33_dihTrans_of_data {m : ℕ} (hm : m.Prime) (hodd : Odd m)
    (hinvol : ∀ z : K, z * z = 1 → z ≠ 1 → IsPGroup 2 (centralizer ({z} : Set K)))
    (hG1 : ∀ u v : K, orderOf u = m → orderOf v = m → ∃ g : K, g * u * g⁻¹ ∈ zpowers v)
    (hG2 : ∀ a x : K, a * a = 1 → x * x = 1 → a ≠ x → (a * x) ^ m = 1 →
      ∀ w ∈ zpowers (a * x), w ≠ 1 → ∃ n : K, n * (a * x) * n⁻¹ = w) :
    Sec33DihTrans K m := by
  intro a x a' x' ha hx hax hpa ha' hx' hax' hpa'
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hai' : a'⁻¹ = a' := inv_eq_of_mul_eq_one_right ha'
  have hxi' : x'⁻¹ = x' := inv_eq_of_mul_eq_one_right hx'
  have hu : orderOf (a * x) = m := sec33_orderOf_mul_invol hm hax hx hpa
  have hu' : orderOf (a' * x') = m := sec33_orderOf_mul_invol hm hax' hx' hpa'
  obtain ⟨g₁, hg₁⟩ := hG1 _ _ hu hu'
  have hw1 : g₁ * (a * x) * g₁⁻¹ ≠ 1 := by
    intro h1
    have : a * x = 1 := by
      have h2 : a * x = g₁⁻¹ * (g₁ * (a * x) * g₁⁻¹) * g₁ := by group
      rw [h2, h1]
      group
    rw [this, orderOf_one] at hu
    exact hm.one_lt.ne hu
  obtain ⟨n, hn⟩ := hG2 a' x' ha' hx' hax' hpa' _ hg₁ hw1
  set h := n⁻¹ * g₁ with hh
  have hhu : h * (a * x) * h⁻¹ = a' * x' := by
    have : h * (a * x) * h⁻¹ = n⁻¹ * (g₁ * (a * x) * g₁⁻¹) * n := by rw [hh]; group
    rw [this, ← hn]
    group
  have hx₁ : (h * x * h⁻¹) * (h * x * h⁻¹) = 1 := by
    rw [show h * x * h⁻¹ * (h * x * h⁻¹) = h * (x * x) * h⁻¹ by group, hx]
    group
  have hxu : x * (a * x) * x = (a * x)⁻¹ := by
    rw [mul_inv_rev, hxi, hai]
    calc x * (a * x) * x = x * a * (x * x) := by group
      _ = x * a := by rw [hx, mul_one]
  have hxu' : x' * (a' * x') * x' = (a' * x')⁻¹ := by
    rw [mul_inv_rev, hxi', hai']
    calc x' * (a' * x') * x' = x' * a' * (x' * x') := by group
      _ = x' * a' := by rw [hx', mul_one]
  have hx₁u : (h * x * h⁻¹) * (a' * x') * (h * x * h⁻¹) = (a' * x')⁻¹ := by
    rw [← hhu]
    calc h * x * h⁻¹ * (h * (a * x) * h⁻¹) * (h * x * h⁻¹)
        = h * (x * (a * x) * x) * h⁻¹ := by group
      _ = (h * (a * x) * h⁻¹)⁻¹ := by rw [hxu]; group
  obtain ⟨c, hcu, hcx⟩ :=
    sec33_exists_centralizes_conj_of_invert hm hodd hinvol hu' hx₁ hx' hx₁u hxu'
  refine ⟨c * h, ?_, ?_⟩
  · have ha₁ : h * a * h⁻¹ = (a' * x') * (h * x * h⁻¹) := by
      calc h * a * h⁻¹ = (h * (a * x) * h⁻¹) * (h * x * h⁻¹) := by
            calc h * a * h⁻¹ = h * (a * x * x) * h⁻¹ := by rw [mul_assoc a x x, hx, mul_one]
              _ = (h * (a * x) * h⁻¹) * (h * x * h⁻¹) := by group
        _ = (a' * x') * (h * x * h⁻¹) := by rw [hhu]
    calc c * h * a * (c * h)⁻¹ = c * (h * a * h⁻¹) * c⁻¹ := by group
      _ = c * ((a' * x') * (h * x * h⁻¹)) * c⁻¹ := by rw [ha₁]
      _ = (c * (a' * x') * c⁻¹) * (c * (h * x * h⁻¹) * c⁻¹) := by group
      _ = (a' * x') * x' := by
        rw [hcx]
        congr 1
        calc c * (a' * x') * c⁻¹ = (a' * x') * c * c⁻¹ := by rw [hcu]
          _ = a' * x' := by group
      _ = a' := by rw [mul_assoc, hx', mul_one]
  · calc c * h * x * (c * h)⁻¹ = c * (h * x * h⁻¹) * c⁻¹ := by group
      _ = x' := hcx


theorem sec33_mem_smul_sylow_iff {p : ℕ} [Fact p.Prime] {P : Sylow p K} {k z : K} :
    z ∈ ((k • P : Sylow p K) : Subgroup K) ↔ k⁻¹ * z * k ∈ (P : Subgroup K) := by
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
    MulAut.smul_def, MulAut.conj_apply, inv_inv]

theorem sec33_g1_of_cyclic {m : ℕ} (hm : m.Prime) (hodd : Odd m)
    (hcyc : ∀ A : Subgroup K, Odd (Nat.card A) → A ≠ ⊥ → ∃ T : Subgroup K, A ≤ T ∧ IsCyclic T) :
    ∀ u v : K, orderOf u = m → orderOf v = m → ∃ g : K, g * u * g⁻¹ ∈ zpowers v := by
  haveI : Fact m.Prime := ⟨hm⟩
  intro u v hu hv
  have hzp : ∀ w : K, orderOf w = m → IsPGroup m (zpowers w) := fun w hw =>
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hw, pow_one])
  obtain ⟨Pu, hPu⟩ := (hzp u hu).exists_le_sylow
  obtain ⟨Pv, hPv⟩ := (hzp v hv).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K Pu Pv
  have huPv : g * u * g⁻¹ ∈ (Pv : Subgroup K) := by
    rw [← hg, sec33_mem_smul_sylow_iff, show g⁻¹ * (g * u * g⁻¹) * g = u by group]
    exact hPu (Subgroup.mem_zpowers u)
  have hPvodd : Odd (Nat.card (Pv : Subgroup K)) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card.mp Pv.isPGroup')
    rw [hk]
    exact Odd.pow hodd
  have hPvne : (Pv : Subgroup K) ≠ ⊥ := by
    intro hbot
    have : v ∈ (⊥ : Subgroup K) := hbot ▸ hPv (Subgroup.mem_zpowers v)
    rw [Subgroup.mem_bot] at this
    rw [this, orderOf_one] at hv
    exact hm.one_lt.ne hv
  obtain ⟨T, hPvT, hT⟩ := hcyc _ hPvodd hPvne
  have hord : ∀ w : K, orderOf w = m → Nat.card (zpowers w) = m := fun w hw => by
    rw [Nat.card_zpowers, hw]
  have hgu : orderOf (g * u * g⁻¹) = m := by
    rw [← hu]
    simpa using orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective u
  have hAB : zpowers (g * u * g⁻¹) = zpowers v := by
    refine eq_of_card_eq_of_cyclic hT ?_ ?_ ?_
    · exact (Subgroup.zpowers_le.mpr huPv).trans hPvT
    · exact (Subgroup.zpowers_le.mpr (hPv (Subgroup.mem_zpowers v))).trans hPvT
    · rw [hord _ hgu, hord _ hv]
  exact ⟨g, hAB ▸ Subgroup.mem_zpowers _⟩


omit [Finite K] in
theorem sec33_g2_three {a x : K} (ha : a * a = 1) (hx : x * x = 1) (hp : (a * x) ^ 3 = 1) :
    ∀ w ∈ zpowers (a * x), w ≠ 1 → ∃ n : K, n * (a * x) * n⁻¹ = w := by
  intro w hw hw1
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  have hp' : (a * x) ^ (3 : ℤ) = 1 := by exact_mod_cast hp
  rw [zpow_eq_zpow_emod k hp'] at hw1 ⊢
  have hk : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hk with hk | hk | hk
  · rw [hk, zpow_zero] at hw1
    exact absurd rfl hw1
  · refine ⟨1, ?_⟩
    rw [hk]
    simp
  · refine ⟨x, ?_⟩
    rw [hk]
    have h2 : (a * x) ^ (2 : ℤ) = (a * x)⁻¹ := by
      have : (a * x) ^ (2 : ℤ) * (a * x) = 1 := by
        rw [← zpow_add_one]
        simpa using hp'
      exact eq_inv_of_mul_eq_one_left this
    rw [h2, mul_inv_rev, hxi, hai]
    calc x * (a * x) * x = x * a * (x * x) := by group
      _ = x * a := by rw [hx, mul_one]

section Type1


theorem sec33_type1_cyclic {n : ℕ} (h : BenderType K n 1 1) :
    ∀ A : Subgroup K, Odd (Nat.card A) → A ≠ ⊥ → ∃ T : Subgroup K, A ≤ T ∧ IsCyclic T := by
  intro A hA hA1
  obtain ⟨T, w, hAT, hT, -⟩ := h.linear_odd_subgroup hA hA1
  exact ⟨T, hAT, hT⟩

theorem sec33_dihTrans_type1 {n : ℕ} (h : BenderType K n 1 1) : Sec33DihTrans K 3 :=
  sec33_dihTrans_of_data Nat.prime_three (by decide)
    (fun z hz hz1 => h.centralizer_involution_isPGroup hz hz1)
    (sec33_g1_of_cyclic Nat.prime_three (by decide) (sec33_type1_cyclic h))
    (fun _ _ ha hx _ hp => sec33_g2_three ha hx hp)

theorem sec33_exists_dih_type1 {n : ℕ} (h : BenderType K n 1 1) :
    ∃ a x : K, a * a = 1 ∧ x * x = 1 ∧ a ≠ x ∧ (a * x) ^ 3 = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd : 3 ∣ Nat.card K := by
    rw [h.card_eq]
    exact three_dvd_linear_card n
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
  have hu1 : u ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hu
    exact absurd hu (by decide)
  have hAodd : Odd (Nat.card (zpowers u)) := by
    rw [Nat.card_zpowers, hu]
    decide
  have hAne : zpowers u ≠ ⊥ := by
    intro hbot
    apply hu1
    have : u ∈ (⊥ : Subgroup K) := hbot ▸ Subgroup.mem_zpowers u
    exact Subgroup.mem_bot.mp this
  obtain ⟨T, w, hAT, hT, hTodd, hcard, hw2, hw1, hinv, -⟩ := h.linear_odd_subgroup hAodd hAne
  have huT : u ∈ T := hAT (Subgroup.mem_zpowers u)
  have hwu : w * u * w = u⁻¹ := by
    have := hinv u huT
    rwa [inv_eq_of_mul_eq_one_right hw2] at this
  refine ⟨u * w, w, ?_, hw2, ?_, ?_⟩
  · calc u * w * (u * w) = u * (w * u * w) := by group
      _ = 1 := by rw [hwu]; group
  · intro h1
    apply hu1
    have : u = 1 := by
      have h2 : u * w * w⁻¹ = w * w⁻¹ := by rw [h1]
      simpa using h2
    exact this
  · have : u * w * w = u := by rw [mul_assoc, hw2, mul_one]
    rw [this, ← hu]
    exact pow_orderOf_eq_one u

end Type1


section Type2


theorem sec33_type2_cyclic {n : ℕ} (h : BenderType K n 2 1) :
    ∀ A : Subgroup K, Odd (Nat.card A) → A ≠ ⊥ → ∃ T : Subgroup K, A ≤ T ∧ IsCyclic T := by
  intro A hA hA1
  obtain ⟨T, hAT, hT, -⟩ := h.suzuki_odd_subgroup hA hA1
  exact ⟨T, hAT, hT⟩

theorem sec33_five_dvd_sz {n : ℕ} (h : BenderType K n 2 1) : 5 ∣ (2 ^ n) ^ 2 + 1 := by
  rcases h.cases' with ⟨hi, -, -⟩ | ⟨-, -, a, -, hn⟩ | ⟨hi, -, -⟩
  · omega
  · subst hn
    obtain ⟨-, h5, -⟩ := sz_mod a
    omega
  · omega

theorem sec33_g2_five {n : ℕ} (h : BenderType K n 2 1) {a x : K} (ha : a * a = 1) (hx : x * x = 1)
    (hax : a ≠ x) (hp : (a * x) ^ 5 = 1) :
    ∀ w ∈ zpowers (a * x), w ≠ 1 → ∃ k : K, k * (a * x) * k⁻¹ = w := by
  classical
  set u := a * x with hu
  have hu5 : orderOf u = 5 := sec33_orderOf_mul_invol Nat.prime_five hax hx hp
  have hu1 : u ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hu5
    exact absurd hu5 (by decide)
  have hdiv : orderOf u ∣ (2 ^ n) ^ 2 + 1 := by rw [hu5]; exact sec33_five_dvd_sz h
  obtain ⟨hCcyc, hCodd, -, hN⟩ := h.suzuki_derangement_type hu1 hdiv
  set C := centralizer ({u} : Set K) with hC
  set N := normalizer ((C : Subgroup K) : Set K) with hNdef
  have huC : u ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hord : ∀ w : K, orderOf w = 5 → Nat.card (zpowers w) = 5 := fun w hw => by
    rw [Nat.card_zpowers, hw]
  have hNu : ∀ k : K, k ∈ N → k * u * k⁻¹ ∈ zpowers u := by
    intro k hk
    have hkuC : k * u * k⁻¹ ∈ C := (Subgroup.mem_normalizer_iff.mp hk u).mp huC
    have hko : orderOf (k * u * k⁻¹) = 5 := by
      rw [← hu5]
      simpa using orderOf_injective (MulAut.conj k).toMonoidHom (MulAut.conj k).injective u
    have h1 : zpowers (k * u * k⁻¹) = zpowers u := by
      refine eq_of_card_eq_of_cyclic hCcyc ?_ ?_ ?_
      · exact Subgroup.zpowers_le.mpr hkuC
      · exact Subgroup.zpowers_le.mpr huC
      · rw [hord _ hko, hord _ hu5]
    exact h1 ▸ Subgroup.mem_zpowers _
  set C' : Subgroup N := C.subgroupOf N with hC'
  have hCN : C ≤ N := Subgroup.le_normalizer
  have hcardQ : Nat.card (N ⧸ C') = 4 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup C'
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCN).toEquiv, hN] at h1
    have hpos : 0 < Nat.card C := Nat.card_pos
    exact (Nat.eq_of_mul_eq_mul_right hpos h1).symm
  let F : N ⧸ C' → K := Quotient.lift (s := QuotientGroup.leftRel C')
    (fun k => (k : K) * u * (k : K)⁻¹) (by
      intro k k' hkk
      have hmem : ((k⁻¹ * k' : N) : K) ∈ C := by
        have := (QuotientGroup.leftRel_apply).mp hkk
        exact this
      have hc : ((k : K)⁻¹ * k') * u = u * ((k : K)⁻¹ * k') := by
        have := Subgroup.mem_centralizer_singleton_iff.mp hmem
        simpa using this
      show (k : K) * u * (k : K)⁻¹ = (k' : K) * u * (k' : K)⁻¹
      calc (k : K) * u * (k : K)⁻¹ = (k : K) * (u * ((k : K)⁻¹ * k')) * (k' : K)⁻¹ := by group
        _ = (k : K) * (((k : K)⁻¹ * k') * u) * (k' : K)⁻¹ := by rw [hc]
        _ = (k' : K) * u * (k' : K)⁻¹ := by group)
  have hFinj : Function.Injective F := by
    intro q₁ q₂ hq
    induction q₁ using QuotientGroup.induction_on with
    | H k =>
      induction q₂ using QuotientGroup.induction_on with
      | H k' =>
        have hq' : (k : K) * u * (k : K)⁻¹ = (k' : K) * u * (k' : K)⁻¹ := hq
        apply QuotientGroup.eq.mpr
        change ((k⁻¹ * k' : N) : K) ∈ C
        rw [Subgroup.mem_centralizer_singleton_iff]
        simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
        calc (k : K)⁻¹ * k' * u = (k : K)⁻¹ * (k' * u * (k' : K)⁻¹) * k' := by group
          _ = (k : K)⁻¹ * (k * u * (k : K)⁻¹) * k' := by rw [← hq']
          _ = u * ((k : K)⁻¹ * k') := by group
  set Gen : Set K := {w | w ∈ zpowers u ∧ w ≠ 1} with hGen
  have hrange : Set.range F ⊆ Gen := by
    rintro _ ⟨q, rfl⟩
    induction q using QuotientGroup.induction_on with
    | H k =>
      refine ⟨hNu k k.2, ?_⟩
      intro h1
      have h1' : (k : K) * u * (k : K)⁻¹ = 1 := h1
      apply hu1
      calc u = (k : K)⁻¹ * ((k : K) * u * (k : K)⁻¹) * k := by group
        _ = 1 := by rw [h1']; group
  have hGenfin : Gen.Finite := Set.toFinite _
  have hGencard : Gen.ncard ≤ 4 := by
    have h1 : insert (1 : K) Gen ⊆ (zpowers u : Set K) := by
      intro w hw
      rcases hw with rfl | hw
      · exact Subgroup.one_mem _
      · exact hw.1
    have h2 := Set.ncard_le_ncard h1 (Set.toFinite _)
    have h3 : (insert (1 : K) Gen).ncard = Gen.ncard + 1 :=
      Set.ncard_insert_of_notMem (fun h' => h'.2 rfl) hGenfin
    have h4 : (zpowers u : Set K).ncard = 5 := by
      rw [← Nat.card_coe_set_eq]
      exact hord u hu5
    omega
  have hrangecard : (Set.range F).ncard = 4 := by
    rw [Set.ncard_range_of_injective hFinj, hcardQ]
  have heq : Set.range F = Gen := Set.eq_of_subset_of_ncard_le hrange (by omega) hGenfin
  intro w hw hw1
  have hwG : w ∈ Gen := ⟨hw, hw1⟩
  rw [← heq] at hwG
  obtain ⟨q, rfl⟩ := hwG
  induction q using QuotientGroup.induction_on with
  | H k => exact ⟨(k : K), rfl⟩

theorem sec33_dihTrans_type2 {n : ℕ} (h : BenderType K n 2 1) : Sec33DihTrans K 5 :=
  sec33_dihTrans_of_data Nat.prime_five (by decide)
    (fun z hz hz1 => h.centralizer_involution_isPGroup hz hz1)
    (sec33_g1_of_cyclic Nat.prime_five (by decide) (sec33_type2_cyclic h))
    (fun _ _ ha hx hax hp => sec33_g2_five h ha hx hax hp)

theorem sec33_exists_dih_type2 {n : ℕ} (h : BenderType K n 2 1) :
    ∃ a x : K, a * a = 1 ∧ x * x = 1 ∧ a ≠ x ∧ (a * x) ^ 5 = 1 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hdvd : 5 ∣ Nat.card K := by
    rw [h.card_eq]
    exact (sec33_five_dvd_sz h).mul_right _
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 5 hdvd
  have hu1 : u ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hu
    exact absurd hu (by decide)
  have hAodd : Odd (Nat.card (zpowers u)) := by
    rw [Nat.card_zpowers, hu]
    decide
  have hAne : zpowers u ≠ ⊥ := by
    intro hbot
    apply hu1
    have : u ∈ (⊥ : Subgroup K) := hbot ▸ Subgroup.mem_zpowers u
    exact Subgroup.mem_bot.mp this
  obtain ⟨T, hAT, hT, hTodd, -, -, -, ⟨w, hwN, hw2, hw1⟩, hinv, -⟩ :=
    h.suzuki_odd_subgroup hAodd hAne
  have huT : u ∈ T := hAT (Subgroup.mem_zpowers u)
  have hwu : w * u * w = u⁻¹ := by
    have := hinv w hwN hw2 hw1 u huT
    rwa [inv_eq_of_mul_eq_one_right hw2] at this
  refine ⟨u * w, w, ?_, hw2, ?_, ?_⟩
  · calc u * w * (u * w) = u * (w * u * w) := by group
      _ = 1 := by rw [hwu]; group
  · intro h1
    apply hu1
    have h2 : u * w * w⁻¹ = w * w⁻¹ := by rw [h1]
    simpa using h2
  · have : u * w * w = u := by rw [mul_assoc, hw2, mul_one]
    rw [this, ← hu]
    exact pow_orderOf_eq_one u

end Type2


section Unified


theorem sec33_bender_dihTrans {n i : ℕ} (h : BenderType K n i 1) (hi : i = 1 ∨ i = 2) :
    Sec33DihTrans K (2 * i + 1) := by
  rcases hi with rfl | rfl
  · exact sec33_dihTrans_type1 h
  · exact sec33_dihTrans_type2 h

theorem sec33_bender_partner_unique {n i : ℕ} (h : BenderType K n i 1) (hi : i = 1 ∨ i = 2)
    {S : Sylow 2 K} {a b x : K} (ha : a ∈ rootCenter (S : Subgroup K))
    (hb : b ∈ rootCenter (S : Subgroup K)) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hx : x * x = 1)
    (hx1 : x ≠ 1) (hxS : x ∉ (S : Subgroup K)) (hax : (a * x) ^ (2 * i + 1) = 1)
    (hbx : (b * x) ^ (2 * i + 1) = 1) : a = b :=
  sec33_partner_unique h (odd_two_mul_add_one i) (sec33_bender_dihTrans h hi) ha hb ha1 hb1 hx hx1
    hxS hax hbx

theorem sec33_bender_partner_exists {n i : ℕ} (h : BenderType K n i 1) (hi : i = 1 ∨ i = 2)
    {P P' : Sylow 2 K} (hPP : P ≠ P') {x : K} (hx : x ∈ rootCenter (P' : Subgroup K))
    (hx1 : x ≠ 1) :
    ∃ a ∈ rootCenter (P : Subgroup K), a ≠ 1 ∧ (a * x) ^ (2 * i + 1) = 1 := by
  have hne : ∃ a x : K, a * a = 1 ∧ x * x = 1 ∧ a ≠ x ∧ (a * x) ^ (2 * i + 1) = 1 := by
    rcases hi with rfl | rfl
    · exact sec33_exists_dih_type1 h
    · exact sec33_exists_dih_type2 h
  exact sec33_partner_exists h (odd_two_mul_add_one i) (sec33_bender_dihTrans h hi) hne hPP hx hx1

end Unified


section TypeMatch


theorem sec33_type_match {J : Type} [Group J] [Finite J] {f n j i : ℕ} (hJ : BenderType J f j 1)
    (hK : BenderType K n i 1) (hj : j = 1 ∨ j = 2) (hi : i = 1 ∨ i = 2) (φ : J →* K)
    (hφ : Function.Injective φ) : j = i := by
  rcases hj with rfl | rfl <;> rcases hi with rfl | rfl
  · rfl
  · exfalso
    have hd : Nat.card J ∣ Nat.card K := Subgroup.card_dvd_of_injective φ hφ
    rw [hJ.card_eq, hK.card_eq] at hd
    have h3 := (three_dvd_linear_card f).trans hd
    rcases hK.cases' with ⟨hi, -, -⟩ | ⟨-, -, a, -, hn⟩ | ⟨hi, -, -⟩
    · omega
    · subst hn
      exact not_three_dvd_sz_card a h3
    · omega
  · exfalso
    obtain ⟨P⟩ : Nonempty (Sylow 2 J) := inferInstance
    obtain ⟨tJ, hcJ⟩ := hJ.exists_benderCore P
    have hlt : rootCenter (P : Subgroup J) < (P : Subgroup J) := by
      refine lt_of_le_of_ne (rootCenter_le _) fun heq => ?_
      have h1 := hcJ.card_center
      rw [heq, hcJ.card_eq] at h1
      have hf : 2 ≤ f := hJ.two_le.2
      have h2 : 2 ^ f < (2 ^ f) ^ 2 := by
        have : 1 < 2 ^ f := Nat.one_lt_two_pow (by omega)
        nlinarith
      omega
    obtain ⟨y, hyP, hyc⟩ := SetLike.exists_of_lt hlt
    have hyc' : ¬ ∀ p ∈ (P : Subgroup J), p * y = y * p := fun h' =>
      hyc (mem_rootCenter_iff.mpr ⟨hyP, h'⟩)
    push Not at hyc'
    obtain ⟨p, hpP, hpy⟩ := hyc'
    have hp2 : IsPGroup 2 ((P : Subgroup J).map φ) := P.isPGroup'.map φ
    obtain ⟨Q, hQ⟩ := hp2.exists_le_sylow
    obtain ⟨tK, hcK⟩ := hK.exists_benderCore Q
    have hQZ : rootCenter (Q : Subgroup K) = (Q : Subgroup K) :=
      Subgroup.eq_of_le_of_card_ge (rootCenter_le _)
        (le_of_eq (by rw [hcK.card_center, hcK.card_eq, pow_one]))
    have hφy : φ y ∈ rootCenter (Q : Subgroup K) := by
      rw [hQZ]; exact hQ (Subgroup.mem_map_of_mem φ hyP)
    have hcomm := (mem_rootCenter_iff.mp hφy).2 (φ p)
      (hQ (Subgroup.mem_map_of_mem φ hpP))
    apply hpy
    apply hφ
    rw [map_mul, map_mul]
    exact hcomm
  · rfl

end TypeMatch


omit [Finite K] in
theorem sec33_mul_sq_of_comm_invol {a x : K} (ha : a * a = 1) (hx : x * x = 1)
    (hc : a * x = x * a) : (a * x) * (a * x) = 1 := by
  calc (a * x) * (a * x) = a * (x * a) * x := by group
    _ = a * (a * x) * x := by rw [← hc]
    _ = (a * a) * (x * x) := by group
    _ = 1 := by rw [ha, hx, one_mul]

omit [Finite K] in
theorem sec33_exists_sylow_centralizes [Finite K] {n i e : ℕ}
    (h : BenderType K n i e) {U : Subgroup K} (hU : ∀ t ∈ U, t * t = 1) (hUne : U ≠ ⊥) {b : K}
    (hb : b * b = 1) (hbU : ∀ t ∈ U, b * t = t * b) :
    ∃ S : Sylow 2 K, U ≤ rootCenter (S : Subgroup K) ∧ b ∈ rootCenter (S : Subgroup K) := by
  obtain ⟨S, hUS⟩ := (isPGroup_two_of_sq_eq_one hU).exists_le_sylow
  obtain ⟨tS, hcS⟩ := h.exists_benderCore S
  have hUR : U ≤ rootCenter (S : Subgroup K) := by
    intro t ht
    exact hcS.mem_rootCenter_of_mul_self (hUS ht) (hU t ht)
  refine ⟨S, hUR, ?_⟩
  by_cases hb1 : b = 1
  · rw [hb1]; exact (rootCenter _).one_mem
  obtain ⟨⟨t₀, ht₀U⟩, ht₀1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hUne
  have ht₀1 : t₀ ≠ 1 := fun h' => ht₀1' (Subtype.ext h')
  have hbC : b ∈ centralizer ({t₀} : Set K) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hbU t₀ ht₀U)
  rw [hcS.centralizer_eq (hUR ht₀U) ht₀1] at hbC
  have hbB : b ∈ borel (S : Subgroup K) :=
    (sup_le (le_borel _) ((fixCartan_le_cartan _ _).trans (cartan_le_borel _ _))) hbC
  have hb2 : orderOf b = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [sq]; exact hb) hb1
  exact hcS.center_of_involution b hbB hb2

section RootLe


theorem sec33_bender_root_le {n i : ℕ} (h : BenderType K n i 1) (hi : i = 1 ∨ i = 2)
    {T Tbar T₁ : Subgroup K} (hT : ∀ t ∈ T, t * t = 1) (hTbar : ∀ x ∈ Tbar, x * x = 1)
    (hT₁ : ∀ t ∈ T₁, t * t = 1) (hTne : T ≠ ⊥) (hcomm : ∀ b ∈ T₁, ∀ t ∈ T, b * t = t * b)
    (h4 : ∀ x ∈ Tbar, x ≠ 1 → ∃ a ∈ T, a ≠ 1 ∧ a ≠ x ∧ (a * x) ^ (2 * i + 1) = 1)
    (h5 : ∀ b ∈ T₁, b ≠ 1 → ∃ x ∈ Tbar, x ≠ 1 ∧ x ≠ b ∧ (x * b) ^ (2 * i + 1) = 1) :
    T₁ ≤ T := by
  intro b hb
  by_cases hb1 : b = 1
  · rw [hb1]; exact T.one_mem
  obtain ⟨x, hxT, hx1, hbx, hxbm⟩ := h5 b hb hb1
  have hbxm : (b * x) ^ (2 * i + 1) = 1 := by
    have h1 : b * x = b * (x * b) * b⁻¹ := by group
    rw [h1, conj_pow, hxbm]
    group
  obtain ⟨a, haT, ha1, hax, haxm⟩ := h4 x hxT hx1
  obtain ⟨S, hTS⟩ := (isPGroup_two_of_sq_eq_one hT).exists_le_sylow
  obtain ⟨tS, hcS⟩ := h.exists_benderCore S
  have haR : a ∈ rootCenter (S : Subgroup K) := hcS.mem_rootCenter_of_mul_self (hTS haT) (hT a haT)
  obtain ⟨⟨t₀, ht₀T⟩, ht₀1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hTne
  have ht₀1 : t₀ ≠ 1 := fun h' => ht₀1' (Subtype.ext h')
  have ht₀R : t₀ ∈ rootCenter (S : Subgroup K) :=
    hcS.mem_rootCenter_of_mul_self (hTS ht₀T) (hT t₀ ht₀T)
  have hbC : b ∈ centralizer ({t₀} : Set K) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm b hb t₀ ht₀T)
  rw [hcS.centralizer_eq ht₀R ht₀1] at hbC
  have hbB : b ∈ borel (S : Subgroup K) :=
    (sup_le (le_borel _) ((fixCartan_le_cartan _ _).trans (cartan_le_borel _ _))) hbC
  have hb2 : orderOf b = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [sq]; exact hT₁ b hb) hb1
  have hbR : b ∈ rootCenter (S : Subgroup K) := hcS.center_of_involution b hbB hb2
  have hxS : x ∉ (S : Subgroup K) := by
    intro hxS
    have hxR : x ∈ rootCenter (S : Subgroup K) :=
      hcS.mem_rootCenter_of_mul_self hxS (hTbar x hxT)
    have hcm : a * x = x * a := (mem_rootCenter_iff.mp hxR).2 a (rootCenter_le _ haR)
    have hsq := sec33_mul_sq_of_comm_invol (hT a haT) (hTbar x hxT) hcm
    have h1 := sec33_eq_one_of_sq_of_pow hsq (odd_two_mul_add_one i) haxm
    apply hax
    calc a = a * x * x := by rw [mul_assoc, hTbar x hxT, mul_one]
      _ = x := by rw [h1, one_mul]
  have := sec33_bender_partner_unique h hi haR hbR ha1 hb1 (hTbar x hxT) hx1 hxS haxm hbxm
  rw [← this]
  exact haT

theorem sec33_bender_centralizer_bot {n i : ℕ} (h : BenderType K n i 1) {T Tbar : Subgroup K}
    (hT : ∀ t ∈ T, t * t = 1) (hTbar : ∀ x ∈ Tbar, x * x = 1) (hTne : T ≠ ⊥) (hTbne : Tbar ≠ ⊥)
    (hnc : ∃ t ∈ T, ∃ x ∈ Tbar, t * x ≠ x * t) {b : K} (hb : b * b = 1)
    (hbT : ∀ t ∈ T, b * t = t * b) (hbTbar : ∀ x ∈ Tbar, b * x = x * b) : b = 1 := by
  by_contra hb1
  obtain ⟨S, hTS, hbS⟩ := sec33_exists_sylow_centralizes h hT hTne hb hbT
  obtain ⟨S', hTS', hbS'⟩ := sec33_exists_sylow_centralizes h hTbar hTbne hb hbTbar
  obtain ⟨tS, hcS⟩ := h.exists_benderCore S
  have hSS : S' = S := by
    refine hcS.sylow_eq_of_ne_bot (V := zpowers b) ?_ ?_ ?_
    · intro hbot
      apply hb1
      have : b ∈ (⊥ : Subgroup K) := hbot ▸ Subgroup.mem_zpowers b
      exact Subgroup.mem_bot.mp this
    · exact Subgroup.zpowers_le.mpr (rootCenter_le _ hbS)
    · exact Subgroup.zpowers_le.mpr (rootCenter_le _ hbS')
  obtain ⟨t, htT, x, hxT, htx⟩ := hnc
  apply htx
  have hxS : x ∈ rootCenter (S : Subgroup K) := by rw [← hSS]; exact hTS' hxT
  exact ((mem_rootCenter_iff.mp (hTS htT)).2 x (rootCenter_le _ hxS)).symm

end RootLe

omit [Finite K] in
theorem sec33_exists_invol_smul_eq [Finite K] {n i e : ℕ}
    (h : BenderType K n i e) {S S' : Sylow 2 K} (hne : S' ≠ S) :
    ∃ t : K, t * t = 1 ∧ t ∉ borel (S : Subgroup K) ∧ t • S = S' := by
  obtain ⟨t₀, hc⟩ := h.exists_benderCore S
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K S S'
  have hgB : g ∉ borel (S : Subgroup K) := fun hgN =>
    hne (by rw [← hg]; exact Sylow.smul_eq_iff_mem_normalizer.mpr hgN)
  obtain ⟨p, hp, m, hm, rfl⟩ := hc.bruhat hgB
  have e1 : m • S = S := Sylow.smul_eq_iff_mem_normalizer.mpr hm
  have e2 : p⁻¹ • S = S :=
    Sylow.smul_eq_iff_mem_normalizer.mpr ((borel (S : Subgroup K)).inv_mem (le_borel _ hp))
  have h1 : (p * t₀ * m) • S = (p * t₀ * p⁻¹) • S := by
    calc (p * t₀ * m) • S = (p * t₀) • (m • S) := mul_smul _ _ _
      _ = (p * t₀) • S := by rw [e1]
      _ = (p * t₀) • (p⁻¹ • S) := by rw [e2]
      _ = (p * t₀ * p⁻¹) • S := (mul_smul _ _ _).symm
  refine ⟨p * t₀ * p⁻¹, ?_, ?_, by rw [← h1, hg]⟩
  · rw [show p * t₀ * p⁻¹ * (p * t₀ * p⁻¹) = p * (t₀ * t₀) * p⁻¹ by group, hc.sq_eq_one]
    group
  · intro htB
    apply hne
    rw [← hg, h1]
    exact Sylow.smul_eq_iff_mem_normalizer.mpr htB

section Type3

theorem sec33_bender_type3_ne_top {n e : ℕ} (h : BenderType K n 3 e) {S S' : Sylow 2 K}
    (hSS : S ≠ S') {T T' : Subgroup K} (hT : T ≤ rootCenter (S : Subgroup K))
    (hT' : T' ≤ rootCenter (S' : Subgroup K)) (hTne : T ≠ ⊥) {g : K}
    (hg : g ∈ rootCenter (S : Subgroup K)) : T ⊔ T' ⊔ conjSubgroup g T' ≠ ⊤ := by
  obtain ⟨⟨z, hzT⟩, hz1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hTne
  have hz1 : z ≠ 1 := fun h' => hz1' (Subtype.ext h')
  have hzR : z ∈ rootCenter (S : Subgroup K) := hT hzT
  obtain ⟨t, ht2, htB, hts⟩ := sec33_exists_invol_smul_eq h (S := S) (S' := S') (Ne.symm hSS)
  have hne := h.lemma_3_2_h_unitary_ne_top S ht2 htB hzR hz1
  set L := Subgroup.closure ({z, t} : Set K) ⊔ ⁅cartan (S : Subgroup K) t, Subgroup.zpowers t⁆
    with hL
  have hzL : z ∈ L := Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
  have htL : t ∈ L := Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
  have hcore := h.benderCore S ht2 htB
  have hRS : ∀ y ∈ rootCenter (S : Subgroup K), y ∈ L := by
    intro y hy
    by_cases hy1 : y = 1
    · rw [hy1]; exact L.one_mem
    obtain ⟨d, ⟨hd, hdy⟩, -⟩ := hcore.existsUnique_commutator_conj hzR hz1 hy hy1
    have hdL : d ∈ L := Subgroup.mem_sup_right hd
    rw [hdy]
    exact L.mul_mem (L.mul_mem (L.inv_mem hdL) hzL) hdL
  have hRS' : ∀ y ∈ rootCenter (S' : Subgroup K), y ∈ L := by
    intro y hy
    rw [← hts] at hy
    obtain ⟨hyS, hyc⟩ := mem_rootCenter_iff.mp hy
    rw [mem_smul_sylow_iff] at hyS
    have hyR : t⁻¹ * y * t ∈ rootCenter (S : Subgroup K) := by
      rw [mem_rootCenter_iff]
      refine ⟨hyS, fun p hp => ?_⟩
      have hp' : t * p * t⁻¹ ∈ ((t • S : Sylow 2 K) : Subgroup K) := by
        rw [mem_smul_sylow_iff, show t⁻¹ * (t * p * t⁻¹) * t = p by group]
        exact hp
      have := hyc _ hp'
      calc p * (t⁻¹ * y * t) = t⁻¹ * ((t * p * t⁻¹) * y) * t := by group
        _ = t⁻¹ * (y * (t * p * t⁻¹)) * t := by rw [this]
        _ = (t⁻¹ * y * t) * p := by group
    have := hRS _ hyR
    have h2 : y = t * (t⁻¹ * y * t) * t⁻¹ := by group
    rw [h2]
    exact L.mul_mem (L.mul_mem htL this) (L.inv_mem htL)
  have hgL : g ∈ L := hRS g hg
  intro htop
  apply hne
  rw [eq_top_iff, ← htop]
  refine sup_le (sup_le (fun y hy => hRS y (hT hy)) (fun y hy => hRS' y (hT' hy))) ?_
  intro y hy
  have hy' : g⁻¹ * y * g ∈ T' := mem_conjSubgroup.mp hy
  have := hRS' _ (hT' hy')
  have h2 : y = g * (g⁻¹ * y * g) * g⁻¹ := by group
  rw [h2]
  exact L.mul_mem (L.mul_mem hgL this) (L.inv_mem hgL)

end Type3


end Generic

end CFSG.RankThree.GF2n.Tim77
