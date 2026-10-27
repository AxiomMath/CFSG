module

public import CFSG.Timmesfeld.Bridge.Asc72YCount
public import CFSG.Timmesfeld.Bridge.Asc72Theorem

public section

namespace CFSG.Timmesfeld.Bridge.Asc72

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
  CFSG.Timmesfeld.Bridge.OddTransp

section Group

variable {G : Type*} [Group G]

@[expose] def InSq (D : Set G) (x : G) : Prop :=
  ∃ r ∈ D, ∃ s ∈ D, r ≠ s ∧ Commute r s ∧ x = r * s

theorem InSq.conj {D : Set G} (hN : IsNormalSet D) {x : G} (h : InSq D x) (g : G) :
    InSq D (g * x * g⁻¹) := by
  obtain ⟨r, hr, s, hs, hrs, hc, rfl⟩ := h
  refine ⟨g * r * g⁻¹, hN g r hr, g * s * g⁻¹, hN g s hs, fun h => hrs ?_,
    (Commute.conj_iff g).mpr hc, by group⟩
  calc r = g⁻¹ * (g * r * g⁻¹) * g := by group
    _ = g⁻¹ * (g * s * g⁻¹) * g := by rw [h]
    _ = s := by group

theorem inv_pow_mul_mul_pow {s t : G} (hs : s * s = 1) (ht : t * t = 1) (k : ℕ) :
    ((s * t) ^ k)⁻¹ * t * (s * t) ^ k = s * (s * t) ^ (2 * k + 1) := by
  set p := s * t with hp
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hts : t = s * p := by rw [hp, ← mul_assoc, hs, one_mul]
  have hsp : s * p * s⁻¹ = p⁻¹ := by
    rw [hp, hsi, mul_inv_rev, hsi, hti, ← mul_assoc, hs, one_mul]
  have hspk : s * p ^ k * s⁻¹ = (p ^ k)⁻¹ := by rw [← conj_pow, hsp, inv_pow]
  have h1 : (p ^ k)⁻¹ * s = s * p ^ k := by
    calc (p ^ k)⁻¹ * s = s * p ^ k * s⁻¹ * s := by rw [hspk]
      _ = s * p ^ k := by group
  calc (p ^ k)⁻¹ * t * p ^ k = (p ^ k)⁻¹ * s * (p * p ^ k) := by
        rw [hts]
        simp only [mul_assoc]
    _ = s * (p ^ k * (p * p ^ k)) := by rw [h1, mul_assoc]
    _ = s * p ^ (2 * k + 1) := by
        rw [← pow_succ', ← pow_add, show k + (k + 1) = 2 * k + 1 by ring]

theorem exists_fix_swap {a u v d z : G} (haa : a * a = 1) (huv : u ≠ v) (hud : u ≠ d)
    (hvd : v ≠ d) (hcuv : Commute u v) (hcud : Commute u d) (hcvd : Commute v d)
    (hzu : z * u = v * d) (hzv : z * v = u * d) (hzd : z * d = u * v)
    (hmem : ∀ x, (x = u ∨ x = v ∨ x = d) →
      (a * x * a⁻¹ = u ∨ a * x * a⁻¹ = v ∨ a * x * a⁻¹ = d))
    (hfix : ∀ x y, (x = u ∨ x = v ∨ x = d) → (y = u ∨ y = v ∨ y = d) → x ≠ y →
      Commute a x → Commute a y → False) :
    ∃ c e₁ e₂ : G, (c = u ∨ c = v ∨ c = d) ∧ (e₁ = u ∨ e₁ = v ∨ e₁ = d) ∧
      (e₂ = u ∨ e₂ = v ∨ e₂ = d) ∧ c ≠ e₁ ∧ c ≠ e₂ ∧ e₁ ≠ e₂ ∧ Commute c e₁ ∧
      Commute c e₂ ∧ Commute e₁ e₂ ∧ Commute a c ∧ a * e₁ * a⁻¹ = e₂ ∧ z * c = e₁ * e₂ := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hcomm : ∀ x, a * x * a⁻¹ = x → Commute a x := fun x h => by
    show a * x = x * a
    calc a * x = a * x * a⁻¹ * a := by group
      _ = x * a := by rw [h]
  have hinj : ∀ x y, a * x * a⁻¹ = a * y * a⁻¹ → x = y := fun x y h => by
    calc x = a⁻¹ * (a * x * a⁻¹) * a := by group
      _ = a⁻¹ * (a * y * a⁻¹) * a := by rw [h]
      _ = y := by group
  have hback : ∀ x y, a * x * a⁻¹ = y → a * y * a⁻¹ = x := fun x y h => by
    rw [← h, hai, show a * (a * x * a) * a = (a * a) * x * (a * a) by group, haa, one_mul,
      mul_one]
  rcases hmem u (Or.inl rfl) with h | h | h
  ·
    have hv : a * v * a⁻¹ = d := by
      rcases hmem v (Or.inr (Or.inl rfl)) with h' | h' | h'
      · exact absurd (hinj _ _ (h'.trans h.symm)) huv.symm
      · exact (hfix u v (Or.inl rfl) (Or.inr (Or.inl rfl)) huv (hcomm u h) (hcomm v h')).elim
      · exact h'
    exact ⟨u, v, d, Or.inl rfl, Or.inr (Or.inl rfl), Or.inr (Or.inr rfl), huv, hud, hvd, hcuv,
      hcud, hcvd, hcomm u h, hv, hzu⟩
  ·
    have hv := hback u v h
    have hd : a * d * a⁻¹ = d := by
      rcases hmem d (Or.inr (Or.inr rfl)) with h' | h' | h'
      · exact absurd (hinj _ _ (h'.trans hv.symm)) hvd.symm
      · exact absurd (hinj _ _ (h'.trans h.symm)) hud.symm
      · exact h'
    exact ⟨d, u, v, Or.inr (Or.inr rfl), Or.inl rfl, Or.inr (Or.inl rfl), hud.symm, hvd.symm, huv,
      hcud.symm, hcvd.symm, hcuv, hcomm d hd, h, hzd⟩
  ·
    have hd := hback u d h
    have hv : a * v * a⁻¹ = v := by
      rcases hmem v (Or.inr (Or.inl rfl)) with h' | h' | h'
      · exact absurd (hinj _ _ (h'.trans hd.symm)) hvd
      · exact h'
      · exact absurd (hinj _ _ (h'.trans h.symm)) huv.symm
    exact ⟨v, u, d, Or.inr (Or.inl rfl), Or.inl rfl, Or.inr (Or.inr rfl), huv.symm, hvd, hud,
      hcuv.symm, hcvd, hcud, hcomm v hv, h, hzv⟩

end Group

namespace CentralQuot

theorem isPGroup_zpowers_of_pow {Y : Type*} [Group Y] {q : Y} {k : ℕ} (h : q ^ 2 ^ k = 1) :
    IsPGroup 2 (Subgroup.zpowers q) := by
  rintro ⟨y, hy⟩
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  refine ⟨k, Subtype.ext ?_⟩
  change (q ^ j) ^ 2 ^ k = 1
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h, one_zpow]

variable {X : Type} [Group X] [Finite X] {z : X} [(Subgroup.zpowers z).Normal]

variable (hzz : z * z = 1) {E : Set X} (hE : IsOddTransp E) (hzE : z ∉ E)
  (hO2 : CFSG.pCore 2 X ≤ Subgroup.zpowers z)
  (hz2 : ∀ r ∈ E, ∀ s ∈ E, r ≠ s → Commute r s → z ≠ r * s)
include hzz hO2

theorem exists_odd_pow_mem {p : X} (hp : p ∈ zStar X) :
    ∃ m : ℕ, Odd m ∧ p ^ m ∈ Subgroup.zpowers z := by
  have hO2' := pCore_quot_eq_bot hzz hO2
  have hcen : mk z p ∈ Subgroup.center (X ⧸ Subgroup.zpowers z) := by
    rw [← zStar_eq_center_of_pCore_eq_bot hO2']
    rw [zStar_eq_comap hzz] at hp
    exact hp
  refine ⟨orderOf (mk z p), ?_, ?_⟩
  · have h1 := orderOf_dvd_natCard (⟨mk z p, hcen⟩ : Subgroup.center (X ⧸ Subgroup.zpowers z))
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat (odd_card_center hO2') h1
  · have h1 : mk z (p ^ orderOf (mk z p)) = 1 := by rw [map_pow, pow_orderOf_eq_one]
    exact (QuotientGroup.eq_one_iff _).mp h1

include hE hzE in
theorem mk_zStar_ne_one {x : X} (hx : x ∈ E) : QuotientGroup.mk' (zStar X) x ≠ 1 := by
  intro h
  have hxS : x ∈ zStar X := (QuotientGroup.eq_one_iff x).mp h
  have hxx : x ^ 2 ^ 1 = 1 := by rw [pow_one, pow_two, hE.mul_self_eq_one hx]
  have hmem := mem_zpowers_of_mem_zStar hzz hO2 (isPGroup_zpowers_of_pow hxx)
    (Subgroup.mem_zpowers x) hxS
  rcases (mem_zpowers_of_mul_self hzz).mp hmem with h1 | h1
  · exact hE.ne_one hx h1
  · exact hzE (h1 ▸ hx)

include hE hz2 in
theorem eq_of_mk_zStar_eq {x y : X} (hx : x ∈ E) (hy : y ∈ E)
    (h : QuotientGroup.mk' (zStar X) x = QuotientGroup.mk' (zStar X) y) : x = y := by
  have hxx := hE.mul_self_eq_one hx
  have hyy := hE.mul_self_eq_one hy
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  have hq : x * y ∈ zStar X := by
    have h1 := QuotientGroup.eq.mp h
    rwa [hxi] at h1
  have hO2' := pCore_quot_eq_bot hzz hO2
  by_cases hc : Commute x y
  · have hqq : (x * y) ^ 2 ^ 1 = 1 := by
      rw [pow_one, pow_two, show x * y * (x * y) = x * (y * x) * y by group, ← hc.eq,
        show x * (x * y) * y = (x * x) * (y * y) by group, hxx, hyy, one_mul]
    have hmem := mem_zpowers_of_mem_zStar hzz hO2 (isPGroup_zpowers_of_pow hqq)
      (Subgroup.mem_zpowers _) hq
    rcases (mem_zpowers_of_mul_self hzz).mp hmem with h1 | h1
    · exact hE.eq_of_mul_eq_one hx h1
    · by_contra hne
      exact hz2 x hx y hy hne hc h1.symm
  · exfalso
    apply hc
    have hodd := hE.odd_of_not_commute hx hy hc
    have hcen : mk z (x * y) ∈ Subgroup.center (X ⧸ Subgroup.zpowers z) := by
      rw [← zStar_eq_center_of_pCore_eq_bot hO2']
      rw [zStar_eq_comap hzz] at hq
      exact hq
    have hinv : x * (x * y) * x⁻¹ = (x * y)⁻¹ := by
      rw [hxi, mul_inv_rev, hxi, hyi, ← mul_assoc, hxx, one_mul]
    have h2 : mk z ((x * y) * (x * y)) = 1 := by
      have e1 : mk z (x * (x * y) * x⁻¹) = mk z (x * y) := by
        rw [map_mul, map_mul, map_inv, (Subgroup.mem_center_iff.mp hcen (mk z x)),
          mul_inv_cancel_right]
      rw [hinv, map_inv] at e1
      have e2 : mk z (x * y) * mk z (x * y) = mk z (x * y) * (mk z (x * y))⁻¹ := by rw [e1]
      rw [map_mul, e2, mul_inv_cancel]
    have h3 : (x * y) * (x * y) ∈ Subgroup.zpowers z := (QuotientGroup.eq_one_iff _).mp h2
    have h4 : (x * y) ^ 2 ^ 2 = 1 := by
      rw [show (2 : ℕ) ^ 2 = 2 * 2 by norm_num, pow_mul, sq (x * y)]
      rcases (mem_zpowers_of_mul_self hzz).mp h3 with h5 | h5
      · rw [h5, one_pow]
      · rw [h5, sq z, hzz]
    have h6 := eq_one_of_isPGroup_of_odd (isPGroup_zpowers_of_pow h4) (Subgroup.mem_zpowers _)
      hodd
    rw [hE.eq_of_mul_eq_one hx h6]

include hE hz2 in
theorem commute_of_mk_zStar {x y : X} (hx : x ∈ E) (hy : y ∈ E)
    (h : Commute (QuotientGroup.mk' (zStar X) x) (QuotientGroup.mk' (zStar X) y)) :
    Commute x y := by
  by_contra hc
  have h1 := eq_of_commute_of_odd hE hx hy h (hE.odd_of_not_commute hx hy hc)
  exact hc (eq_of_mk_zStar_eq hzz hE hO2 hz2 hx hy h1 ▸ Commute.refl x)

end CentralQuot

end CFSG.Timmesfeld.Bridge.Asc72
