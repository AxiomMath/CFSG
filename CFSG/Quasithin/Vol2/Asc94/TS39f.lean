module

public import CFSG.Quasithin.Vol2.Asc94.TS39e

public section

namespace CFSG.Quasithin.A94

open CFSG.CGT.Timmesfeld75 CFSG.Open

variable {G : Type} [Group G] [Finite G] {z : G}

theorem Frame2.not_mem_H_of_order (F : Frame2 G z) (p : ℕ) [Fact p.Prime] (hpH : ¬ p ∣ 21504)
    {x : G} (hx : orderOf x = p) : x ∉ Cz z := by
  intro hxH
  have hord : orderOf (⟨x, hxH⟩ : ↥(Cz z)) = p := by
    rw [← Subgroup.orderOf_coe]
    exact hx
  apply hpH
  have := orderOf_dvd_natCard (⟨x, hxH⟩ : ↥(Cz z))
  rwa [hord, F.card_H] at this

theorem Frame2.R_inf_Cz (F : Frame2 G z) {R : Subgroup G} (hAR : F.A ≤ R)
    (hRc : Nat.card R = 31 * 64) : R ⊓ Cz z = F.A := by
  haveI : Fact (Nat.Prime 31) := ⟨by norm_num⟩
  have hAle : F.A ≤ R ⊓ Cz z := fun a ha =>
    ⟨hAR ha, Subgroup.mem_centralizer_singleton_iff.2 (F.comm_A ha F.z_mem_A)⟩
  have hdvd1 : Nat.card ↥(R ⊓ Cz z) ∣ 31 * 64 := by
    rw [← hRc]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨k₁, hk₁⟩ : 64 ∣ Nat.card ↥(R ⊓ Cz z) := by
    rw [← F.card_A]
    exact Subgroup.card_dvd_of_le hAle
  have hk₁d : k₁ ∣ 31 := by
    rw [hk₁] at hdvd1
    have : 64 * k₁ ∣ 64 * 31 := by simpa [mul_comm] using hdvd1
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 31)).1 hk₁d with h | h
  · have hc : Nat.card ↥(R ⊓ Cz z) = 64 := by rw [hk₁, h]
    exact (Subgroup.eq_of_le_of_card_ge hAle (by rw [hc, F.card_A])).symm
  · exfalso
    have hc : Nat.card ↥(R ⊓ Cz z) = Nat.card R := by rw [hk₁, h, hRc]
    have hReq : R ⊓ Cz z = R := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hc])
    have hRH : R ≤ Cz z := inf_eq_left.1 hReq
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥R) 31 (by rw [hRc]; exact dvd_mul_right 31 64)
    have hxo : orderOf (x : G) = 31 := by rw [Subgroup.orderOf_coe]; exact hx
    exact F.not_mem_H_of_order 31 (by norm_num) hxo (hRH x.2)

theorem Frame2.fix_all (F : Frame2 G z) {R : Subgroup G} (hRL : R ≤ Subgroup.normalizer (F.A : Set G))
    (hAR : F.A ≤ R) (hRn : ∀ l ∈ Subgroup.normalizer (F.A : Set G), ∀ r ∈ R, l⁻¹ * r * l ∈ R)
    (hRc : Nat.card R = 31 * 64) {γ : G} (hγ : γ ∈ F.NA) {r₁ : G} (hr₁ : r₁ ∈ R)
    (hr₁A : r₁ ∉ F.A) (hfix : γ⁻¹ * (r₁⁻¹ * z * r₁) * γ = r₁⁻¹ * z * r₁) :
    ∀ r ∈ R, γ⁻¹ * (r⁻¹ * z * r) * γ = r⁻¹ * z * r := by
  haveI : Fact (Nat.Prime 31) := ⟨by norm_num⟩
  have hγN : γ ∈ Subgroup.normalizer (F.A : Set G) := hγ.2
  have hγz : γ⁻¹ * z * γ = z := by
    have h := Subgroup.mem_centralizer_singleton_iff.1 hγ.1
    calc γ⁻¹ * z * γ = γ⁻¹ * (z * γ) := by group
      _ = γ⁻¹ * (γ * z) := by rw [h]
      _ = z := by group
  have hconjA : ∀ l ∈ Subgroup.normalizer (F.A : Set G), ∀ x ∈ F.A, l * x * l⁻¹ ∈ F.A :=
    fun l hl x hx => (Subgroup.mem_normalizer_iff.1 hl x).1 hx
  let Fg : Subgroup G :=
    { carrier := {r | r ∈ R ∧ γ⁻¹ * r * γ * r⁻¹ ∈ F.A}
      mul_mem' := fun {a b} ha hb => by
        refine ⟨R.mul_mem ha.1 hb.1, ?_⟩
        have e : γ⁻¹ * (a * b) * γ * (a * b)⁻¹ =
            (γ⁻¹ * a * γ * a⁻¹) * (a * (γ⁻¹ * b * γ * b⁻¹) * a⁻¹) := by group
        rw [e]
        exact F.A.mul_mem ha.2 (hconjA a (hRL ha.1) _ hb.2)
      one_mem' := ⟨R.one_mem, by simpa using F.A.one_mem⟩
      inv_mem' := fun {a} ha => by
        refine ⟨R.inv_mem ha.1, ?_⟩
        have e : γ⁻¹ * a⁻¹ * γ * a⁻¹⁻¹ = a⁻¹ * (γ⁻¹ * a * γ * a⁻¹)⁻¹ * a := by group
        rw [e]
        have := hconjA a⁻¹ (hRL (R.inv_mem ha.1)) _ (F.A.inv_mem ha.2)
        simpa using this }
  have hAF : F.A ≤ Fg := by
    intro a ha
    refine ⟨hAR ha, ?_⟩
    exact F.A.mul_mem (F.conj_mem_A ha hγN) (F.A.inv_mem ha)
  have hFR : Fg ≤ R := fun r hr => hr.1
  have hdvd1 : Nat.card ↥Fg ∣ 31 * 64 := by
    rw [← hRc]
    exact Subgroup.card_dvd_of_le hFR
  obtain ⟨k₁, hk₁⟩ : 64 ∣ Nat.card ↥Fg := by
    rw [← F.card_A]
    exact Subgroup.card_dvd_of_le hAF
  have hk₁d : k₁ ∣ 31 := by
    rw [hk₁] at hdvd1
    have : 64 * k₁ ∣ 64 * 31 := by simpa [mul_comm] using hdvd1
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
  have hr₁F : r₁ ∈ Fg := by
    refine ⟨hr₁, ?_⟩
    set w : G := γ⁻¹ * r₁ * γ * r₁⁻¹ with hw
    have hwR : w ∈ R := R.mul_mem (hRn γ hγN r₁ hr₁) (R.inv_mem hr₁)
    have h1 : γ⁻¹ * (r₁⁻¹ * z * r₁) * γ = (w * r₁)⁻¹ * z * (w * r₁) := by
      calc γ⁻¹ * (r₁⁻¹ * z * r₁) * γ
          = (γ⁻¹ * r₁ * γ)⁻¹ * (γ⁻¹ * z * γ) * (γ⁻¹ * r₁ * γ) := by group
        _ = (γ⁻¹ * r₁ * γ)⁻¹ * z * (γ⁻¹ * r₁ * γ) := by rw [hγz]
        _ = (w * r₁)⁻¹ * z * (w * r₁) := by rw [hw]; group
    rw [h1] at hfix
    have hwz : w⁻¹ * z * w = z := by
      calc w⁻¹ * z * w = r₁ * ((w * r₁)⁻¹ * z * (w * r₁)) * r₁⁻¹ := by group
        _ = r₁ * (r₁⁻¹ * z * r₁) * r₁⁻¹ := by rw [hfix]
        _ = z := by group
    have hwH : w ∈ Cz z := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc w * z = w * (w⁻¹ * z * w) := by rw [hwz]
        _ = z * w := by group
    have hwA : w ∈ R ⊓ Cz z := ⟨hwR, hwH⟩
    rwa [F.R_inf_Cz hAR hRc] at hwA
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 31)).1 hk₁d with h | h
  · exfalso
    have hc : Nat.card ↥Fg = 64 := by rw [hk₁, h]
    have hFA : F.A = Fg := Subgroup.eq_of_le_of_card_ge hAF (by rw [hc, F.card_A])
    exact hr₁A (by rw [hFA]; exact hr₁F)
  · have hc : Nat.card ↥Fg = Nat.card R := by rw [hk₁, h, hRc]
    have hFReq : Fg = R := Subgroup.eq_of_le_of_card_ge hFR (by rw [hc])
    intro r hr
    have hrF : r ∈ Fg := by rw [hFReq]; exact hr
    obtain ⟨-, ha⟩ := hrF
    set a : G := γ⁻¹ * r * γ * r⁻¹ with ha_def
    have hcomm' : a * z = z * a := F.comm_A ha F.z_mem_A
    have hcomm : a⁻¹ * z * a = z := by
      calc a⁻¹ * z * a = a⁻¹ * (z * a) := by group
        _ = a⁻¹ * (a * z) := by rw [← hcomm']
        _ = z := by group
    have hγr : γ⁻¹ * r * γ = a * r := by rw [ha_def]; group
    calc γ⁻¹ * (r⁻¹ * z * r) * γ = (γ⁻¹ * r * γ)⁻¹ * (γ⁻¹ * z * γ) * (γ⁻¹ * r * γ) := by group
      _ = (a * r)⁻¹ * z * (a * r) := by rw [hγz, hγr]
      _ = r⁻¹ * (a⁻¹ * z * a) * r := by group
      _ = r⁻¹ * z * r := by rw [hcomm]

theorem Frame3.orbit_R_eq (F : Frame3 G z) (h31 : F.Sz.ncard = 31) {R : Subgroup G}
    (hRL : R ≤ Subgroup.normalizer (F.A : Set G)) (hAR : F.A ≤ R) (hRc : Nat.card R = 31 * 64) :
    {x : G | ∃ l ∈ R, x = l⁻¹ * z * l} = F.Sz := by
  have hsub : {x : G | ∃ l ∈ R, x = l⁻¹ * z * l} ⊆ F.Sz := by
    rintro _ ⟨l, hl, rfl⟩
    exact F.conj_mem_Sz ⟨F.z_mem_A, F.z_ne_one, 1, by simp⟩ (hRL hl)
  have hcard := card_orbit_eq_ncard R z _ rfl
  rw [Frame2.R_inf_Cz F.toFrame2 hAR hRc, F.card_A, hRc] at hcard
  have h31' : {x : G | ∃ l ∈ R, x = l⁻¹ * z * l}.ncard = 31 := by omega
  exact Set.eq_of_subset_of_ncard_le hsub (by rw [h31, h31']) (Set.toFinite _)

theorem conj_eq_iff {γ s : G} : γ⁻¹ * s * γ = s ↔ γ * s = s * γ := by
  constructor
  · intro h
    calc γ * s = γ * (γ⁻¹ * s * γ) := by rw [h]
      _ = s * γ := by group
  · intro h
    calc γ⁻¹ * s * γ = γ⁻¹ * (s * γ) := by group
      _ = γ⁻¹ * (γ * s) := by rw [h]
      _ = s := by group

theorem Frame3.false_of_card_31 (F : Frame3 G z) (hU1 : ∀ u ∈ F.U, u ≠ 1 → InZG z u)
    (h31 : F.Sz.ncard = 31) (hj : ∃ j : Fin 7, 4 ≤ j.val ∧ F.Δ j ⊆ F.Sz) : False := by
  obtain ⟨R, hRL, hAR, hRn, hRc⟩ := F.exists_R h31
  have hO := F.orbit_R_eq h31 hRL hAR hRc
  obtain ⟨j, hj4, hjS⟩ := hj
  have hne : ∀ i : Fin 7, (F.Δ i).Nonempty := fun i =>
    Set.nonempty_of_ncard_ne_zero (by rw [F.Δ_card i]; fin_cases i <;> simp)
  obtain ⟨s₁, hs₁⟩ := hne 1
  obtain ⟨s₂, hs₂⟩ := hne j
  have hj0 : j ≠ 0 := by
    intro h
    rw [h] at hj4
    simp at hj4
  have hj1 : j ≠ 1 := by
    intro h
    rw [h] at hj4
    simp at hj4
  have hs₁' : s₁ ∈ (F.A ⊓ F.U : Subgroup G) ∧ s₁ ≠ 1 ∧ s₁ ≠ z := by
    rw [F.Δ1] at hs₁
    obtain ⟨h1, h2⟩ := hs₁
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at h2
    exact ⟨h1, h2.1, h2.2⟩
  have hs₁S : s₁ ∈ F.Sz := ⟨(Subgroup.mem_inf.1 hs₁'.1).1, hs₁'.2.1,
    hU1 _ (Subgroup.mem_inf.1 hs₁'.1).2 hs₁'.2.1⟩
  have hs₂S : s₂ ∈ F.Sz := hjS hs₂
  have hs₂z : s₂ ≠ z := by
    intro h
    have h0 : s₂ ∈ F.Δ 0 := by rw [F.Δ0, h]; rfl
    exact Set.disjoint_left.1 (F.Δ_disj 0 j (Ne.symm hj0)) h0 hs₂
  obtain ⟨r₁, hr₁, hs₁r⟩ := (hO ▸ hs₁S : s₁ ∈ {x : G | ∃ l ∈ R, x = l⁻¹ * z * l})
  obtain ⟨r₂, hr₂, hs₂r⟩ := (hO ▸ hs₂S : s₂ ∈ {x : G | ∃ l ∈ R, x = l⁻¹ * z * l})
  have hr₁A : r₁ ∉ F.A := by
    intro h
    apply hs₁'.2.2
    rw [hs₁r]
    have := F.comm_A h F.z_mem_A
    calc r₁⁻¹ * z * r₁ = r₁⁻¹ * (z * r₁) := by group
      _ = r₁⁻¹ * (r₁ * z) := by rw [← this]
      _ = z := by group
  have hr₂A : r₂ ∉ F.A := by
    intro h
    apply hs₂z
    rw [hs₂r]
    have := F.comm_A h F.z_mem_A
    calc r₂⁻¹ * z * r₂ = r₂⁻¹ * (z * r₂) := by group
      _ = r₂⁻¹ * (r₂ * z) := by rw [← this]
      _ = z := by group
  have hstab12 : ∀ γ ∈ F.NA, γ⁻¹ * s₁ * γ = s₁ → γ⁻¹ * s₂ * γ = s₂ := by
    intro γ hγ hfix
    rw [hs₁r] at hfix
    have := F.fix_all hRL hAR hRn hRc hγ hr₁ hr₁A hfix r₂ hr₂
    rw [hs₂r]
    exact this
  have hstab21 : ∀ γ ∈ F.NA, γ⁻¹ * s₂ * γ = s₂ → γ⁻¹ * s₁ * γ = s₁ := by
    intro γ hγ hfix
    rw [hs₂r] at hfix
    have := F.fix_all hRL hAR hRn hRc hγ hr₂ hr₂A hfix r₁ hr₁
    rw [hs₁r]
    exact this
  have hCeq : F.NA ⊓ Subgroup.centralizer ({s₁} : Set G) =
      F.NA ⊓ Subgroup.centralizer ({s₂} : Set G) := by
    ext γ
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨hγ, h⟩
      exact ⟨hγ, conj_eq_iff.1 (hstab12 γ hγ (conj_eq_iff.2 h))⟩
    · rintro ⟨hγ, h⟩
      exact ⟨hγ, conj_eq_iff.1 (hstab21 γ hγ (conj_eq_iff.2 h))⟩
  have horb : ∀ (i : Fin 7) (s : G), s ∈ F.Δ i →
      {x : G | ∃ l ∈ F.NA, x = l⁻¹ * s * l} = F.Δ i := by
    intro i s hs
    ext x
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact F.Δ_inv i s hs l hl
    · intro hx
      obtain ⟨l, hl, hxl⟩ := F.Δ_trans i s hs x hx
      exact ⟨l, hl, hxl⟩
  have c1 := card_orbit_eq_ncard F.NA s₁ (F.Δ 1) (horb 1 s₁ hs₁)
  have c2 := card_orbit_eq_ncard F.NA s₂ (F.Δ j) (horb j s₂ hs₂)
  rw [← hCeq] at c2
  have hk : 0 < Nat.card ↥(F.NA ⊓ Subgroup.centralizer ({s₁} : Set G)) := Nat.card_pos
  have hcc : (F.Δ 1).ncard = (F.Δ j).ncard := by
    have := c1.trans c2.symm
    exact Nat.eq_of_mul_eq_mul_right hk this
  rw [F.Δ_card 1, F.Δ_card j] at hcc
  revert hcc
  fin_cases j <;> simp_all

end CFSG.Quasithin.A94
