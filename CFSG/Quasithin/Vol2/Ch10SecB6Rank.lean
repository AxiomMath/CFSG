module

public import CFSG.Quasithin.Vol2.Ch10SecB6Bar
public import CFSG.Quasithin.Vol2.Ch1Rank

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13
open scoped commutatorElement

section Rank

variable {X : Type*} [Group X] [Finite X]

theorem pRank_add_le_pRank_sup' {p : ℕ} (hp : p.Prime) {A B : Subgroup X}
    (hc : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) (hAB : A ⊓ B = ⊥) :
    CFSG.Open.pRank p A + CFSG.Open.pRank p B ≤ CFSG.Open.pRank p (A ⊔ B) := by
  have hp1 : 1 < p := hp.one_lt
  obtain ⟨E₁, hE₁A, hE₁, hc₁⟩ := CFSG.SectionRank.exists_pRank hp1 A
  obtain ⟨E₂, hE₂B, hE₂, hc₂⟩ := CFSG.SectionRank.exists_pRank hp1 B
  let f : E₁ × E₂ →* X := MonoidHom.noncommCoprod E₁.subtype E₂.subtype
    (fun x y => hc x (hE₁A x.2) y (hE₂B y.2))
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨x, y⟩ hxy
    have h : (x : X) * y = 1 := hxy
    have hx : (x : X) ∈ A ⊓ B := Subgroup.mem_inf.2 ⟨hE₁A x.2, by
      rw [eq_inv_of_mul_eq_one_left h]
      exact B.inv_mem (hE₂B y.2)⟩
    rw [hAB, Subgroup.mem_bot] at hx
    have hy : (y : X) = 1 := by rw [hx, one_mul] at h; exact h
    rw [Subgroup.mem_bot, Prod.mk_eq_one]
    exact ⟨Subtype.ext hx, Subtype.ext hy⟩
  have hc₁' := hE₁.1
  have hc₂' := hE₂.1
  refine CFSG.SectionRank.le_pRank_of_injective hp1 (A := E₁ × E₂) ?_ ?_ ?_ f hf ?_
  · rintro ⟨a, b⟩ ⟨c, d⟩
    exact Prod.ext (mul_comm' a c) (mul_comm' b d)
  · rintro ⟨a, b⟩
    exact Prod.ext (Subtype.ext (hE₁.2 a a.2)) (Subtype.ext (hE₂.2 b b.2))
  · rw [Nat.card_prod, hc₁, hc₂, pow_add]
  · rintro _ ⟨⟨a, b⟩, rfl⟩
    exact (A ⊔ B).mul_mem (Subgroup.mem_sup_left (hE₁A a.2)) (Subgroup.mem_sup_right (hE₂B b.2))

theorem one_le_pRank_zpowers {p : ℕ} (hp : p.Prime) {c : X} (hc : orderOf c = p) :
    1 ≤ CFSG.Open.pRank p (Subgroup.zpowers c) := by
  refine CFSG.SectionRank.le_pRank hp.one_lt le_rfl ⟨inferInstance, fun x hx => ?_⟩ (k := 1)
    (by rw [Nat.card_zpowers, hc, pow_one])
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hc, pow_orderOf_eq_one,
    one_zpow]

end Rank

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem modO2Image_commute' {H K₁ K₂ : Subgroup G} (hc : ⁅K₁, K₂⁆ ≤ pCoreOf 2 H) :
    ∀ x ∈ modO2Image H K₁, ∀ y ∈ modO2Image H K₂, x * y = y * x := by
  intro x hx y hy
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
  obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
  have ha' : (a : G) ∈ K₁ := ha
  have hb' : (b : G) ∈ K₂ := hb
  have hmem : (⁅(a : G), (b : G)⁆ : G) ∈ pCoreOf 2 H :=
    hc (Subgroup.commutator_mem_commutator ha' hb')
  obtain ⟨c, hcP, hcc⟩ := Subgroup.mem_map.mp hmem
  have hcab : c = a * b * a⁻¹ * b⁻¹ :=
    Subtype.ext (by simpa [commutatorElement_def] using hcc)
  have h1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) (a * b * a⁻¹ * b⁻¹) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (hcab ▸ (by exact hcP))
  simp only [map_mul, map_inv] at h1
  exact (commutatorElement_eq_one_iff_mul_comm.mp (by simpa [commutatorElement_def] using h1))

theorem pRank_modO2Image_le_one (hqtke : quasithinIsQTKECat G) {H K K' Y : Subgroup G}
    (hH : pCoreOf 2 H ≠ ⊥) (hc : ⁅K, K'⁆ ≤ pCoreOf 2 H) (hYK' : Y ≤ K') (hYH : Y ≤ H)
    (hs : IsSimpleGroup (ModO2 Y)) (hnab : ∃ a b : ModO2 Y, a * b ≠ b * a) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpY : p ∣ Nat.card (ModO2 Y)) :
    CFSG.Open.pRank p (modO2Image H K) ≤ 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hcomm := modO2Image_commute' hc
  obtain ⟨e⟩ := nonempty_modO2_modO2Image hYH
  have hpY' : p ∣ Nat.card ↥(modO2Image H Y) := by
    refine dvd_trans ?_ (Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥(modO2Image H Y)))
    rw [Nat.card_congr e.toEquiv]
    exact hpY
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' p hpY'
  have hy' : orderOf (y : ↥H ⧸ CFSG.pCore 2 ↥H) = p := by rw [Subgroup.orderOf_coe, hy]
  have hinf : Subgroup.zpowers (y : ↥H ⧸ CFSG.pCore 2 ↥H) ⊓ modO2Image H K = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx1
    have hyY : (y : ↥H ⧸ CFSG.pCore 2 ↥H) ^ k ∈ modO2Image H Y := (modO2Image H Y).zpow_mem y.2 k
    have hcen : ∀ z ∈ modO2Image H Y, (y : ↥H ⧸ CFSG.pCore 2 ↥H) ^ k * z =
        z * (y : ↥H ⧸ CFSG.pCore 2 ↥H) ^ k := fun z hz =>
      hcomm _ hx2 z (modO2Image_mono' hYK' hz)
    obtain ⟨j, hj⟩ := isPGroup_of_mem_center hYH hs hnab hyY hcen
    have h1 : orderOf ((y : ↥H ⧸ CFSG.pCore 2 ↥H) ^ k) ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hj
    have h2 : orderOf ((y : ↥H ⧸ CFSG.pCore 2 ↥H) ^ k) ∣ p := by
      rw [← hy']
      exact orderOf_dvd_of_pow_eq_one (by rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
        zpow_natCast, pow_orderOf_eq_one, one_zpow])
    have h3 : orderOf ((y : ↥H ⧸ CFSG.pCore 2 ↥H) ^ k) = 1 := by
      rcases (Nat.dvd_prime hp).mp h2 with h | h
      · exact h
      · rw [h] at h1
        exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
          (hp.dvd_of_dvd_pow h1)) hp2
    rw [orderOf_eq_one_iff] at h3
    rw [h3]
    exact Subgroup.one_mem _
  have hc' : ∀ x ∈ Subgroup.zpowers (y : ↥H ⧸ CFSG.pCore 2 ↥H), ∀ z ∈ modO2Image H K,
      x * z = z * x := by
    intro x hx z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact (hcomm z hz _ (modO2Image_mono' hYK' ((modO2Image H Y).zpow_mem y.2 k))).symm
  have h1 := pRank_add_le_pRank_sup' hp hc' hinf
  have h2 := CFSG.SectionRank.pRank_mono (p := p) hp.one_lt
    (le_top : Subgroup.zpowers (y : ↥H ⧸ CFSG.pCore 2 ↥H) ⊔ modO2Image H K ≤ ⊤)
  have h3 := pRank_modO2_eq H hp hp2
  have h4 := pRank_le_two_of_pCoreOf_ne_bot hqtke hH hp hp2
  have h5 := one_le_pRank_zpowers hp hy'
  omega

end CFSG.Quasithin.Vol2.Ch10.SecB
