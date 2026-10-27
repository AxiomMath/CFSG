module

public import CFSG.Quasithin.EmptyFaithful.S153Odd
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement

namespace S153D

section Model

variable {W : Type*} [CommGroup W] [Finite W] {X L₁ L₂ : Subgroup (MulAut W)} {t : MulAut W}

theorem oTwoUpper_inf_L₂_eq (h : OfourStruct X L₁ L₂ t) {T' : Subgroup (MulAut W)}
    (hT : IsSylowTwoOf T' X) {x : MulAut W} (hxL : x ∈ L₂) (hx3 : orderOf x = 3) :
    oTwoUpper X ⊓ L₂ = Subgroup.zpowers x := by
  have hodd : ∀ {y : MulAut W}, y ^ 3 = 1 → Odd (orderOf y) := fun hy =>
    Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one hy)
  have hxO : x ∈ oTwoUpper X :=
    mem_oTwoUpper_of_odd (h.L₂_le hxL) (by rw [hx3]; decide)
  have hle : Subgroup.zpowers x ≤ oTwoUpper X ⊓ L₂ :=
    Subgroup.zpowers_le.mpr ⟨hxO, hxL⟩
  have hc3 : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hx3]
  have h9 : Nat.card (oTwoUpper X) = 9 := h.card_oTwoUpper hT
  have hdvd9 : Nat.card ↥(oTwoUpper X ⊓ L₂) ∣ 9 := by
    rw [← h9]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hge : 3 ∣ Nat.card ↥(oTwoUpper X ⊓ L₂) := by
    rw [← hc3]
    exact Subgroup.card_dvd_of_le hle
  have hne9 : Nat.card ↥(oTwoUpper X ⊓ L₂) ≠ 9 := by
    intro h9'
    have heq : oTwoUpper X ⊓ L₂ = oTwoUpper X :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h9, h9'])
    obtain ⟨x₁, hx₁L, hx₁3, hx₁1⟩ := exists_orderThree h.nat₁
    have hx₁A : x₁ ∈ oTwoUpper X := mem_oTwoUpper_of_odd (h.L₁_le hx₁L) (hodd hx₁3)
    have hx₁L₂ : x₁ ∈ L₂ := by
      have : x₁ ∈ oTwoUpper X ⊓ L₂ := by rw [heq]; exact hx₁A
      exact this.2
    have : x₁ ∈ L₁ ⊓ L₂ := ⟨hx₁L, hx₁L₂⟩
    rw [h.Linf, Subgroup.mem_bot] at this
    exact hx₁1 this
  obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (by simpa using hdvd9 :
    Nat.card ↥(oTwoUpper X ⊓ L₂) ∣ 3 ^ 2)
  have hc : Nat.card ↥(oTwoUpper X ⊓ L₂) = 3 := by
    interval_cases k
    · rw [hkeq] at hge
      norm_num at hge
    · simpa using hkeq
    · exact absurd (by simpa using hkeq) hne9
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hc, hc3])).symm

theorem oTwoUpper_inf_L₁_eq (h : OfourStruct X L₁ L₂ t) {T' : Subgroup (MulAut W)}
    (hT : IsSylowTwoOf T' X) {x : MulAut W} (hxL : x ∈ L₁) (hx3 : orderOf x = 3) :
    oTwoUpper X ⊓ L₁ = Subgroup.zpowers x :=
  oTwoUpper_inf_L₂_eq h.symm hT hxL hx3

theorem zpowers_sup_eq_oTwoUpper (h : OfourStruct X L₁ L₂ t) {T' : Subgroup (MulAut W)}
    (hT : IsSylowTwoOf T' X) {x₁ x₂ : MulAut W} (h₁ : x₁ ∈ L₁) (h₂ : x₂ ∈ L₂)
    (o₁ : orderOf x₁ = 3) (o₂ : orderOf x₂ = 3) :
    Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ = oTwoUpper X := by
  have hx₁O : x₁ ∈ oTwoUpper X := mem_oTwoUpper_of_odd (h.L₁_le h₁) (by rw [o₁]; decide)
  have hx₂O : x₂ ∈ oTwoUpper X := mem_oTwoUpper_of_odd (h.L₂_le h₂) (by rw [o₂]; decide)
  have hAle : Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ ≤ oTwoUpper X :=
    sup_le (Subgroup.zpowers_le.mpr hx₁O) (Subgroup.zpowers_le.mpr hx₂O)
  have h9 : Nat.card (oTwoUpper X) = 9 := h.card_oTwoUpper hT
  have hc3 : Nat.card (Subgroup.zpowers x₂) = 3 := by rw [Nat.card_zpowers, o₂]
  have hdvd : Nat.card ↥(Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂) ∣ 9 := by
    rw [← h9]
    exact Subgroup.card_dvd_of_le hAle
  have hge : 3 ∣ Nat.card ↥(Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂) := by
    rw [← hc3]
    exact Subgroup.card_dvd_of_le le_sup_right
  have hx₁ : x₁ ∉ Subgroup.zpowers x₂ := by
    intro hmem
    have hL₂ : x₁ ∈ L₂ := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
      rw [← hk]
      exact Subgroup.zpow_mem _ h₂ k
    have : x₁ ∈ L₁ ⊓ L₂ := ⟨h₁, hL₂⟩
    rw [h.Linf, Subgroup.mem_bot] at this
    rw [this, orderOf_one] at o₁
    exact absurd o₁ (by decide)
  have hne3 : Nat.card ↥(Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂) ≠ 3 := by
    intro h3
    have heq : Subgroup.zpowers x₂ = Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ :=
      Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [h3, hc3])
    exact hx₁ (heq ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers x₁))
  obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (by simpa using hdvd :
    Nat.card ↥(Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂) ∣ 3 ^ 2)
  have hc : Nat.card ↥(Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂) = 9 := by
    interval_cases k
    · rw [hkeq] at hge
      norm_num at hge
    · exact absurd (by simpa using hkeq) hne3
    · simpa using hkeq
  exact Subgroup.eq_of_le_of_card_ge hAle (by rw [hc, h9])

theorem eq_one_of_centralizes_oTwoUpper (h : OfourStruct X L₁ L₂ t) {T' : Subgroup (MulAut W)}
    (hT : IsSylowTwoOf T' X) {s : MulAut W} (hsT : s ∈ T')
    (hc : ∀ y ∈ oTwoUpper X, s * y = y * s) : s = 1 := by
  set C : Subgroup (MulAut W) :=
    T' ⊓ Subgroup.centralizer (oTwoUpper X : Set (MulAut W)) with hC
  have hCX : C ≤ X := inf_le_left.trans hT.1
  have hCp : IsPGroup 2 C := hT.2.1.to_le inf_le_left
  have hXN : X ≤ Subgroup.normalizer (C : Set (MulAut W)) := by
    rw [← h.sup_oTwoUpper_eq hT]
    refine sup_le (fun g hg => A4.mem_normalizer_of_conj_mem fun x hx => ?_)
      (fun g hg => A4.mem_normalizer_of_conj_mem fun x hx => ?_)
    · have h1 := Subgroup.mem_centralizer_iff.mp hx.2 g hg
      have : g * x * g⁻¹ = x := by
        rw [h1]
        group
      rw [this]
      exact hx
    · refine ⟨T'.mul_mem (T'.mul_mem hg hx.1) (T'.inv_mem hg), ?_⟩
      refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
      have hgn : g ∈ Subgroup.normalizer (oTwoUpper X : Set (MulAut W)) :=
        le_normalizer_oTwoUpper X (hT.1 hg)
      have hy' : g⁻¹ * y * g ∈ oTwoUpper X := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgn) y).mp hy
        simpa using this
      have h1 := Subgroup.mem_centralizer_iff.mp hx.2 _ hy'
      calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
        _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
        _ = g * x * g⁻¹ * y := by group
  have hbot : C = ⊥ := h.eq_bot_of_normal_isPGroup hT hCX hXN hCp
  have hsC : s ∈ C := ⟨hsT, Subgroup.mem_centralizer_iff.mpr fun y hy => (hc y hy).symm⟩
  rw [hbot, Subgroup.mem_bot] at hsC
  exact hsC

theorem model_signs (h : OfourStruct X L₁ L₂ t) {T' : Subgroup (MulAut W)}
    (hT : IsSylowTwoOf T' X) {x₁ x₂ : MulAut W} (hx₁L : x₁ ∈ L₁) (hx₂L : x₂ ∈ L₂)
    (hx₁3 : x₁ ^ 3 = 1) (hx₂3 : x₂ ^ 3 = 1) {g : MulAut W} (hg : g ∈ T' ⊓ (L₁ ⊔ L₂)) :
    ∃ e₁ e₂ : ℤ, (e₁ = 1 ∨ e₁ = -1) ∧ (e₂ = 1 ∨ e₂ = -1) ∧ g * x₁ * g⁻¹ = x₁ ^ e₁ ∧
      g * x₂ * g⁻¹ = x₂ ^ e₂ ∧ (e₁ = 1 → e₂ = 1 → g = 1) := by
  obtain ⟨s₁, s₂, τ, a₁, a₂, hF⟩ := h.exists_sylowFacts hT
  have hs₁L : s₁ ∈ L₁ := hF.sylow.s₁_mem_L
  have hs₂L : s₂ ∈ L₂ := hF.sylow.s₂_mem_L
  have hs₁2 : s₁ ^ 2 = 1 := by rw [pow_two]; exact hF.s₁_sq
  have hs₂2 : s₂ ^ 2 = 1 := by rw [pow_two]; exact hF.s₂_sq
  have hi₁ : ∀ {x : MulAut W}, x ∈ L₁ → x ^ 3 = 1 → s₁ * x * s₁⁻¹ = x⁻¹ := fun hx hx3 =>
    OfourStruct.conj_inv_cube h.nat₁ hs₁L hs₁2 hF.sylow.s₁_ne hx hx3
  have hi₂ : ∀ {x : MulAut W}, x ∈ L₂ → x ^ 3 = 1 → s₂ * x * s₂⁻¹ = x⁻¹ := fun hx hx3 =>
    OfourStruct.conj_inv_cube h.nat₂ hs₂L hs₂2 hF.sylow.s₂_ne hx hx3
  have hc₁ : s₁ * x₂ * s₁⁻¹ = x₂ := by
    rw [h.comm s₁ hs₁L x₂ hx₂L]
    group
  have hc₂ : s₂ * x₁ * s₂⁻¹ = x₁ := by
    rw [← h.comm x₁ hx₁L s₂ hs₂L]
    group
  rcases (hF.S_eq g).1 hg with rfl | rfl | rfl | rfl
  · exact ⟨1, 1, Or.inl rfl, Or.inl rfl, by simp, by simp, fun _ _ => rfl⟩
  · refine ⟨-1, 1, Or.inr rfl, Or.inl rfl, ?_, ?_, fun h1 => absurd h1 (by norm_num)⟩
    · rw [zpow_neg_one]; exact hi₁ hx₁L hx₁3
    · rw [zpow_one]; exact hc₁
  · refine ⟨1, -1, Or.inl rfl, Or.inr rfl, ?_, ?_, fun _ h2 => absurd h2 (by norm_num)⟩
    · rw [zpow_one]; exact hc₂
    · rw [zpow_neg_one]; exact hi₂ hx₂L hx₂3
  · refine ⟨-1, -1, Or.inr rfl, Or.inr rfl, ?_, ?_, fun h1 => absurd h1 (by norm_num)⟩
    · have : s₁ * s₂ * x₁ * (s₁ * s₂)⁻¹ = s₁ * (s₂ * x₁ * s₂⁻¹) * s₁⁻¹ := by group
      rw [this, hc₂, zpow_neg_one]
      exact hi₁ hx₁L hx₁3
    · have : s₁ * s₂ * x₂ * (s₁ * s₂)⁻¹ = s₁ * (s₂ * x₂ * s₂⁻¹) * s₁⁻¹ := by group
      rw [this, hi₂ hx₂L hx₂3, zpow_neg_one]
      have h3 : s₁ * x₂⁻¹ * s₁⁻¹ = (s₁ * x₂ * s₁⁻¹)⁻¹ := by group
      rw [h3, hc₁]

theorem model_inverting (h : OfourStruct X L₁ L₂ t) {T' : Subgroup (MulAut W)}
    (hT : IsSylowTwoOf T' X) {x₁ x₂ : MulAut W} (hx₁L : x₁ ∈ L₁) (hx₂L : x₂ ∈ L₂)
    (hx₁3 : x₁ ^ 3 = 1) (hx₂3 : x₂ ^ 3 = 1) :
    ∃ s₁ s₂ : MulAut W, s₁ ∈ T' ⊓ (L₁ ⊔ L₂) ∧ s₂ ∈ T' ⊓ (L₁ ⊔ L₂) ∧
      s₁ * x₁ * s₁⁻¹ = x₁⁻¹ ∧ s₁ * x₂ * s₁⁻¹ = x₂ ∧ s₂ * x₁ * s₂⁻¹ = x₁ ∧
        s₂ * x₂ * s₂⁻¹ = x₂⁻¹ := by
  obtain ⟨s₁, s₂, τ, a₁, a₂, hF⟩ := h.exists_sylowFacts hT
  have hs₁L : s₁ ∈ L₁ := hF.sylow.s₁_mem_L
  have hs₂L : s₂ ∈ L₂ := hF.sylow.s₂_mem_L
  have hs₁2 : s₁ ^ 2 = 1 := by rw [pow_two]; exact hF.s₁_sq
  have hs₂2 : s₂ ^ 2 = 1 := by rw [pow_two]; exact hF.s₂_sq
  refine ⟨s₁, s₂, hF.sylow.s₁_mem_S, hF.sylow.s₂_mem_S,
    OfourStruct.conj_inv_cube h.nat₁ hs₁L hs₁2 hF.sylow.s₁_ne hx₁L hx₁3, ?_, ?_,
    OfourStruct.conj_inv_cube h.nat₂ hs₂L hs₂2 hF.sylow.s₂_ne hx₂L hx₂3⟩
  · rw [h.comm s₁ hs₁L x₂ hx₂L]
    group
  · rw [← h.comm x₁ hx₁L s₂ hs₂L]
    group

end Model

end S153D

end CFSG.Quasithin
