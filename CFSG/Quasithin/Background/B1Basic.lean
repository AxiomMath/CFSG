module

public import CFSG.Quasithin.Background.FFStarTransport
public import CFSG.Quasithin.Background.D2Params
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Quasithin

variable {V : Type*} [CommGroup V]

@[expose] def FFLe (X B A : Subgroup (MulAut V)) : Prop :=
  IsA2 X B ∧ IsA2 X A ∧ B ≤ A ∧
    Nat.card B * Nat.card (fixV B) = Nat.card A * Nat.card (fixV A)

@[expose] def IsFFStarMin (X A : Subgroup (MulAut V)) : Prop :=
  IsFFStarOffender X A ∧
    ∀ B : Subgroup (MulAut V), IsFFStarOffender X B → FFLe X B A → B = A

@[expose] def IsStrongFFStarOffender (X A : Subgroup (MulAut V)) : Prop :=
  IsFFStarOffender X A ∧ rAV A < 1

theorem IsFFStarOffender.isA2 {X A : Subgroup (MulAut V)} (h : IsFFStarOffender X A) :
    IsA2 X A :=
  ⟨h.1, h.2.1, h.2.2.1⟩

theorem isFFStarOffender_iff {X A : Subgroup (MulAut V)} :
    IsFFStarOffender X A ↔ IsA2 X A ∧ ∀ B : Subgroup (MulAut V), B ≤ A →
      Nat.card B * Nat.card (fixV B) ≤ Nat.card A * Nat.card (fixV A) :=
  ⟨fun h => ⟨h.isA2, h.2.2.2⟩, fun h => ⟨h.1.1, h.1.2.1, h.1.2.2, h.2⟩⟩

theorem IsFFStarOffender.card_le {X A B : Subgroup (MulAut V)} (h : IsFFStarOffender X A)
    (hB : B ≤ A) : Nat.card B * Nat.card (fixV B) ≤ Nat.card A * Nat.card (fixV A) :=
  h.2.2.2 B hB

theorem IsFFStarMin.isFFStarOffender {X A : Subgroup (MulAut V)} (h : IsFFStarMin X A) :
    IsFFStarOffender X A :=
  h.1

namespace B1

theorem fixV_bot : fixV (⊥ : Subgroup (MulAut V)) = ⊤ := by
  ext v
  simp only [mem_fixV, Subgroup.mem_top, iff_true]
  intro x hx
  rw [Subgroup.mem_bot] at hx
  rw [hx]
  rfl

theorem fixV_le_fixV {A B : Subgroup (MulAut V)} (h : B ≤ A) : fixV A ≤ fixV B :=
  fun _ hv x hx => hv x (h hx)

theorem card_fixV_pos [Finite V] (A : Subgroup (MulAut V)) : 0 < Nat.card (fixV A) :=
  Nat.card_pos

theorem card_bot_mul_card_fixV [Finite V] :
    Nat.card (⊥ : Subgroup (MulAut V)) * Nat.card (fixV (⊥ : Subgroup (MulAut V))) =
      Nat.card V := by
  rw [fixV_bot, Subgroup.card_bot, one_mul, Subgroup.card_top]

theorem card_eq_index_mul [Finite V] (A : Subgroup (MulAut V)) :
    Nat.card V = (fixV A).index * Nat.card (fixV A) :=
  (Subgroup.index_mul_card _).symm

theorem index_eq_two_pow [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (H : Subgroup V) :
    H.index = 2 ^ rkIdx H := by
  have hV2 : Nat.card V = 2 ^ rk V :=
    card_eq_two_pow_of_isPGroup (isPGroup_two_of_sq_eq_one hV)
  have hd : H.index ∣ Nat.card V := Subgroup.index_dvd_card H
  rw [hV2] at hd
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
  unfold rkIdx
  rw [hk, padicValNat.prime_pow]

theorem card_elemAbelian [Finite V] {A : Subgroup (MulAut V)} (h : IsElemAbelian2 A) :
    Nat.card A = 2 ^ rk A :=
  card_eq_two_pow_of_isPGroup h.isPGroup

theorem card_le_iff [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {A : Subgroup (MulAut V)}
    (h : IsElemAbelian2 A) :
    Nat.card V ≤ Nat.card A * Nat.card (fixV A) ↔ rkIdx (fixV A) ≤ rk A := by
  rw [card_eq_index_mul A, index_eq_two_pow hV, card_elemAbelian h,
    Nat.mul_le_mul_right_iff (card_fixV_pos A), Nat.pow_le_pow_iff_right (by norm_num)]

theorem card_lt_iff [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {A : Subgroup (MulAut V)}
    (h : IsElemAbelian2 A) :
    Nat.card V < Nat.card A * Nat.card (fixV A) ↔ rkIdx (fixV A) < rk A := by
  rw [card_eq_index_mul A, index_eq_two_pow hV, card_elemAbelian h,
    Nat.mul_lt_mul_right (card_fixV_pos A), Nat.pow_lt_pow_iff_right (by norm_num)]

theorem card_eq_iff [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {A : Subgroup (MulAut V)}
    (h : IsElemAbelian2 A) :
    Nat.card V = Nat.card A * Nat.card (fixV A) ↔ rkIdx (fixV A) = rk A := by
  rw [card_eq_index_mul A, index_eq_two_pow hV, card_elemAbelian h,
    Nat.mul_left_inj (card_fixV_pos A).ne', Nat.pow_right_inj (by norm_num)]

end B1

theorem rAV_le_one_iff [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)}
    (h : IsA2 X A) :
    rAV A ≤ 1 ↔ Nat.card V ≤ Nat.card A * Nat.card (fixV A) := by
  have hr : (0 : ℚ) < (rk A : ℚ) := by exact_mod_cast h.rk_pos
  rw [B1.card_le_iff hV h.2.2]
  unfold rAV
  rw [div_le_one hr]
  exact_mod_cast Iff.rfl

theorem rAV_lt_one_iff [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)}
    (h : IsA2 X A) :
    rAV A < 1 ↔ Nat.card V < Nat.card A * Nat.card (fixV A) := by
  have hr : (0 : ℚ) < (rk A : ℚ) := by exact_mod_cast h.rk_pos
  rw [B1.card_lt_iff hV h.2.2]
  unfold rAV
  rw [div_lt_one hr]
  exact_mod_cast Iff.rfl

theorem rAV_eq_one_iff [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)}
    (h : IsA2 X A) :
    rAV A = 1 ↔ Nat.card V = Nat.card A * Nat.card (fixV A) := by
  have hr : (rk A : ℚ) ≠ 0 := by exact_mod_cast h.rk_pos.ne'
  rw [B1.card_eq_iff hV h.2.2]
  unfold rAV
  rw [div_eq_one_iff_eq hr]
  exact_mod_cast Iff.rfl

theorem isFFModule_iff [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)} :
    IsFFModule X ↔ ∃ A, IsA2 X A ∧ rAV A ≤ 1 := by
  constructor
  · rintro ⟨A, hAX, hA0, hAe, hle⟩
    exact ⟨A, ⟨hAX, hA0, hAe⟩, (rAV_le_one_iff hV ⟨hAX, hA0, hAe⟩).2 hle⟩
  · rintro ⟨A, hA, hr⟩
    exact ⟨A, hA.1, hA.2.1, hA.2.2, (rAV_le_one_iff hV hA).1 hr⟩

theorem isStrongFFModule_iff [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)} :
    IsStrongFFModule X ↔ ∃ A, IsA2 X A ∧ rAV A < 1 := by
  constructor
  · rintro ⟨A, hAX, hA0, hAe, hlt⟩
    exact ⟨A, ⟨hAX, hA0, hAe⟩, (rAV_lt_one_iff hV ⟨hAX, hA0, hAe⟩).2 hlt⟩
  · rintro ⟨A, hA, hr⟩
    exact ⟨A, hA.1, hA.2.1, hA.2.2, (rAV_lt_one_iff hV hA).1 hr⟩

theorem B1_4_1 [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)}
    (hA : IsFFStarOffender X A) : rAV A ≤ 1 := by
  rw [rAV_le_one_iff hV hA.isA2]
  have := hA.card_le (bot_le : (⊥ : Subgroup (MulAut V)) ≤ A)
  rwa [B1.card_bot_mul_card_fixV] at this

theorem B1_4_2 {X A B : Subgroup (MulAut V)} (hA : IsFFStarOffender X A) (hB : FFLe X B A) :
    IsFFStarOffender X B := by
  obtain ⟨hB2, -, hBA, heq⟩ := hB
  refine isFFStarOffender_iff.2 ⟨hB2, fun B' hB' => ?_⟩
  rw [heq]
  exact hA.card_le (hB'.trans hBA)


namespace B1

def cv (v : V) (a : MulAut V) : V := a v * v⁻¹

theorem cv_mul (v : V) (a b : MulAut V) : cv v (a * b) = a (cv v b) * cv v a := by
  simp only [cv, MulAut.mul_apply, map_mul, map_inv]
  group

theorem cv_one (v : V) : cv v (1 : MulAut V) = 1 := by
  simp [cv]

theorem cv_inv_mul (v : V) (a b : MulAut V) : cv v (a⁻¹ * b) = a⁻¹ (cv v b * (cv v a)⁻¹) := by
  simp only [cv, MulAut.mul_apply, map_mul, map_inv]
  simp

def Bv (A : Subgroup (MulAut V)) (v : V) : Subgroup (MulAut V) where
  carrier := {a | a ∈ A ∧ cv v a ∈ fixV A}
  one_mem' := ⟨A.one_mem, by rw [cv_one]; exact (fixV A).one_mem⟩
  mul_mem' := by
    rintro a b ⟨ha, hca⟩ ⟨hb, hcb⟩
    refine ⟨A.mul_mem ha hb, ?_⟩
    rw [cv_mul, hcb a ha]
    exact (fixV A).mul_mem hcb hca
  inv_mem' := by
    rintro a ⟨ha, hca⟩
    refine ⟨A.inv_mem ha, ?_⟩
    have h1 : a (cv v a⁻¹) * cv v a = 1 := by
      rw [← cv_mul, mul_inv_cancel, cv_one]
    have h3 : a (cv v a⁻¹) = (cv v a)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h4 : a⁻¹ (cv v a)⁻¹ = (cv v a)⁻¹ := (fixV A).inv_mem hca a⁻¹ (A.inv_mem ha)
    have h2 : cv v a⁻¹ = (cv v a)⁻¹ := by
      calc cv v a⁻¹ = a⁻¹ (a (cv v a⁻¹)) := by simp
        _ = a⁻¹ (cv v a)⁻¹ := by rw [h3]
        _ = (cv v a)⁻¹ := h4
    rw [h2]
    exact (fixV A).inv_mem hca

theorem Bv_le (A : Subgroup (MulAut V)) (v : V) : Bv A v ≤ A := fun _ h => h.1

theorem mem_Bv {A : Subgroup (MulAut V)} {v : V} {a : MulAut V} :
    a ∈ Bv A v ↔ a ∈ A ∧ cv v a ∈ fixV A := Iff.rfl

theorem Bv_fix_cv {A : Subgroup (MulAut V)} (hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {v : V}
    {b : MulAut V} (hb : b ∈ Bv A v) {a : MulAut V} (ha : a ∈ A) : b (cv v a) = cv v a := by
  have h1 := cv_mul v b a
  have h2 := cv_mul v a b
  rw [hc b hb.1 a ha] at h1
  have h3 : a (cv v b) = cv v b := hb.2 a ha
  rw [h3] at h2
  have h4 : b (cv v a) * cv v b = cv v a * cv v b := by
    rw [← h1, h2, mul_comm]
  exact mul_right_cancel h4

theorem cv_mem_fixV_Bv {A : Subgroup (MulAut V)} (hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (v : V)
    {a : MulAut V} (ha : a ∈ A) : cv v a ∈ fixV (Bv A v) :=
  fun _ hb => Bv_fix_cv hc hb ha

noncomputable def Fmap {A : Subgroup (MulAut V)} (hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (v : V) :
    (↥A ⧸ (Bv A v).subgroupOf A) × ↥(fixV A) → ↥(fixV (Bv A v)) := fun p =>
  ⟨cv v ((Quotient.out p.1 : ↥A) : MulAut V) * p.2,
    (fixV (Bv A v)).mul_mem (cv_mem_fixV_Bv hc v (Quotient.out p.1 : ↥A).2)
      (fixV_le_fixV (Bv_le A v) p.2.2)⟩

theorem mem_Bv_of_cv_div {A : Subgroup (MulAut V)} {v : V} {a a' : MulAut V} (ha : a ∈ A)
    (ha' : a' ∈ A) (h : cv v a' * (cv v a)⁻¹ ∈ fixV A) : a⁻¹ * a' ∈ Bv A v := by
  refine ⟨A.mul_mem (A.inv_mem ha) ha', ?_⟩
  rw [cv_inv_mul]
  have h5 : a⁻¹ (cv v a' * (cv v a)⁻¹) = cv v a' * (cv v a)⁻¹ := h a⁻¹ (A.inv_mem ha)
  rw [h5]
  exact h

theorem Fmap_injective {A : Subgroup (MulAut V)} (hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (v : V) : Function.Injective (Fmap hc v) := by
  rintro ⟨q, u⟩ ⟨q', u'⟩ h
  have h1 : cv v ((Quotient.out q : ↥A) : MulAut V) * (u : V) =
      cv v ((Quotient.out q' : ↥A) : MulAut V) * (u' : V) := congrArg Subtype.val h
  have ha : ((Quotient.out q : ↥A) : MulAut V) ∈ A := (Quotient.out q : ↥A).2
  have ha' : ((Quotient.out q' : ↥A) : MulAut V) ∈ A := (Quotient.out q' : ↥A).2
  have hdiv : cv v ((Quotient.out q' : ↥A) : MulAut V) * (cv v ((Quotient.out q : ↥A) : MulAut V))⁻¹ =
      (u : V) * (u' : V)⁻¹ := by
    rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul]
    calc cv v ((Quotient.out q' : ↥A) : MulAut V) * (u' : V)
        = cv v ((Quotient.out q : ↥A) : MulAut V) * u := h1.symm
      _ = u * cv v ((Quotient.out q : ↥A) : MulAut V) := mul_comm _ _
  have hfix : (u : V) * (u' : V)⁻¹ ∈ fixV A := (fixV A).mul_mem u.2 ((fixV A).inv_mem u'.2)
  have hmem := mem_Bv_of_cv_div ha ha' (hdiv ▸ hfix)
  have hq : q = q' := by
    have h3 : (Quotient.out q : ↥A)⁻¹ * Quotient.out q' ∈ (Bv A v).subgroupOf A := hmem
    have h2 := QuotientGroup.eq.2 h3
    rwa [QuotientGroup.out_eq', QuotientGroup.out_eq'] at h2
  subst hq
  exact Prod.ext rfl (Subtype.ext (mul_left_cancel h1))

theorem relIndex_mul_card_Bv (A : Subgroup (MulAut V)) (v : V) :
    (Bv A v).relIndex A * Nat.card (Bv A v) = Nat.card A := by
  have := Subgroup.relIndex_mul_card (Bv A v) A
  rwa [inf_eq_left.2 (Bv_le A v)] at this

theorem card_Fmap_domain [Finite V] {A : Subgroup (MulAut V)} :
    ∀ v : V, Nat.card ((↥A ⧸ (Bv A v).subgroupOf A) × ↥(fixV A)) =
      (Bv A v).relIndex A * Nat.card (fixV A) := by
  intro v
  rw [Nat.card_prod]
  rfl

theorem card_index_mul_le [Finite V] {A : Subgroup (MulAut V)}
    (hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (v : V) :
    (Bv A v).relIndex A * Nat.card (fixV A) ≤ Nat.card (fixV (Bv A v)) := by
  rw [← card_Fmap_domain v]
  exact Nat.card_le_card_of_injective _ (Fmap_injective hc v)

theorem card_mul_le_Bv [Finite V] {A : Subgroup (MulAut V)}
    (hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (v : V) :
    Nat.card A * Nat.card (fixV A) ≤ Nat.card (Bv A v) * Nat.card (fixV (Bv A v)) := by
  have h1 := card_index_mul_le hc v
  have h2 := relIndex_mul_card_Bv A v
  calc Nat.card A * Nat.card (fixV A)
      = (Bv A v).relIndex A * Nat.card (Bv A v) * Nat.card (fixV A) := by rw [h2]
    _ = Nat.card (Bv A v) * ((Bv A v).relIndex A * Nat.card (fixV A)) := by ring
    _ ≤ Nat.card (Bv A v) * Nat.card (fixV (Bv A v)) := Nat.mul_le_mul_left _ h1

theorem Bv_eq_of_mem_fixV {A : Subgroup (MulAut V)} {v : V} (hv : v ∈ fixV A) : Bv A v = A := by
  refine le_antisymm (Bv_le A v) fun a ha => ⟨ha, ?_⟩
  have : cv v a = 1 := by simp [cv, hv a ha]
  rw [this]
  exact (fixV A).one_mem

theorem Bv_ne_bot [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)}
    (hA : IsFFStarOffender X A) {v : V} (hv : v ∉ fixV A) : Bv A v ≠ ⊥ := by
  intro hbot
  have hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := hA.2.2.1.1
  have hcard1 : Nat.card (Bv A v) = 1 := by rw [hbot, Subgroup.card_bot]
  have hcard2 : Nat.card (fixV (Bv A v)) = Nat.card V := by
    rw [hbot, fixV_bot, Subgroup.card_top]
  have hrel : (Bv A v).relIndex A = Nat.card A := by
    have := relIndex_mul_card_Bv A v
    rwa [hcard1, mul_one] at this
  have hle : Nat.card V ≤ Nat.card A * Nat.card (fixV A) := by
    have := hA.card_le (bot_le : (⊥ : Subgroup (MulAut V)) ≤ A)
    rwa [card_bot_mul_card_fixV] at this
  have hbij : Function.Bijective (Fmap hc v) := by
    refine Function.Injective.bijective_of_nat_card_le (Fmap_injective hc v) ?_
    rw [card_Fmap_domain v, hrel, hcard2]
    exact hle
  have hvmem : v ∈ fixV (Bv A v) := by
    intro b hb
    rw [hbot, Subgroup.mem_bot] at hb
    rw [hb]
    rfl
  obtain ⟨⟨q, u⟩, hqu⟩ := hbij.2 ⟨v, hvmem⟩
  have h1 : cv v ((Quotient.out q : ↥A) : MulAut V) * (u : V) = v := congrArg Subtype.val hqu
  set a : MulAut V := ((Quotient.out q : ↥A) : MulAut V) with ha_def
  have ha : a ∈ A := (Quotient.out q : ↥A).2
  have h2 : a v = (u : V)⁻¹ := by
    have h3 : a v * v⁻¹ * (u : V) = v := h1
    have h4 : a v = v * v * (u : V)⁻¹ := by
      calc a v = (a v * v⁻¹ * (u : V)) * (u : V)⁻¹ * v := by group
        _ = v * (u : V)⁻¹ * v := by rw [h3]
        _ = v * v * (u : V)⁻¹ := mul_right_comm _ _ _
    rw [h4, ← sq, hV v, one_mul]
  have h5 : v = (u : V)⁻¹ := by
    have h6 : a⁻¹ (a v) = v := by simp
    rw [h2] at h6
    have h7 : a⁻¹ (u : V)⁻¹ = (u : V)⁻¹ := (fixV A).inv_mem u.2 a⁻¹ (A.inv_mem ha)
    rw [h7] at h6
    exact h6.symm
  exact hv (h5 ▸ (fixV A).inv_mem u.2)

end B1

theorem B1_4_3 [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)}
    (hA : IsFFStarMin X A) : IsQuadratic A := by
  have hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := hA.1.2.2.1.1
  have hA2 : IsA2 X A := hA.1.isA2
  have key : ∀ v : V, B1.Bv A v = A := by
    intro v
    by_contra hne
    have hv : v ∉ fixV A := fun hv => hne (B1.Bv_eq_of_mem_fixV hv)
    have hbot : B1.Bv A v ≠ ⊥ := B1.Bv_ne_bot hV hA.1 hv
    have hle : B1.Bv A v ≤ A := B1.Bv_le A v
    have heq : Nat.card (B1.Bv A v) * Nat.card (fixV (B1.Bv A v)) =
        Nat.card A * Nat.card (fixV A) :=
      le_antisymm (hA.1.card_le hle) (B1.card_mul_le_Bv hc v)
    have hBv2 : IsA2 X (B1.Bv A v) := hA2.mono hle hbot
    have hFF : FFLe X (B1.Bv A v) A := ⟨hBv2, hA2, hle, heq⟩
    exact hne (hA.2 _ (B1_4_2 hA.1 hFF) hFF)
  unfold IsQuadratic commV
  rw [Subgroup.closure_le]
  rintro _ ⟨x, hx, v, rfl⟩
  have hxB : x ∈ B1.Bv A v := by rw [key v]; exact hx
  exact hxB.2

theorem B1_4_3_of_minimal [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)}
    (hA : IsFFStarOffender X A)
    (hmin : ∀ B : Subgroup (MulAut V), IsFFStarOffender X B → B ≤ A → B = A) :
    IsQuadratic A :=
  B1_4_3 hV ⟨hA, fun B hB hBA => hmin B hB hBA.2.2.1⟩


namespace B1

theorem exists_offender_below [Finite V] {X A : Subgroup (MulAut V)} (hA : IsA2 X A) (c : ℕ)
    (hr : Nat.card V + c ≤ Nat.card A * Nat.card (fixV A)) :
    ∃ B, B ≤ A ∧ IsFFStarOffender X B ∧ Nat.card V + c ≤ Nat.card B * Nat.card (fixV B) := by
  let S : Set (Subgroup (MulAut V)) :=
    {B | B ≤ A ∧ B ≠ ⊥ ∧ Nat.card V + c ≤ Nat.card B * Nat.card (fixV B)}
  have hSne : S.Nonempty := ⟨A, le_rfl, hA.2.1, hr⟩
  obtain ⟨B, hB, hmin⟩ := Set.exists_min_image S (fun B => Nat.card B) (Set.toFinite S) hSne
  refine ⟨B, hB.1, isFFStarOffender_iff.2 ⟨hA.mono hB.1 hB.2.1, fun B' hB' => ?_⟩, hB.2.2⟩
  by_cases hbot : B' = ⊥
  · subst hbot
    rw [card_bot_mul_card_fixV]
    have := hB.2.2
    omega
  · by_contra hlt
    push Not at hlt
    have hB'S : B' ∈ S := ⟨hB'.trans hB.1, hbot, by have := hB.2.2; omega⟩
    have hcard : Nat.card B ≤ Nat.card B' := hmin B' hB'S
    have : B' = B := Subgroup.eq_of_le_of_card_ge hB' hcard
    subst this
    exact lt_irrefl _ hlt

end B1

theorem B1_4_4_le [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)}
    (hA : IsA2 X A) (hr : rAV A ≤ 1) :
    ∃ B, B ≤ A ∧ IsFFStarOffender X B ∧ rAV B ≤ 1 := by
  have h0 : Nat.card V + 0 ≤ Nat.card A * Nat.card (fixV A) := by
    simpa using (rAV_le_one_iff hV hA).1 hr
  obtain ⟨B, hBA, hB, hBc⟩ := B1.exists_offender_below hA 0 h0
  exact ⟨B, hBA, hB, (rAV_le_one_iff hV hB.isA2).2 (by simpa using hBc)⟩

theorem B1_4_4_lt [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)}
    (hA : IsA2 X A) (hr : rAV A < 1) :
    ∃ B, B ≤ A ∧ IsFFStarOffender X B ∧ rAV B < 1 := by
  have h0 : Nat.card V + 1 ≤ Nat.card A * Nat.card (fixV A) :=
    (rAV_lt_one_iff hV hA).1 hr
  obtain ⟨B, hBA, hB, hBc⟩ := B1.exists_offender_below hA 1 h0
  exact ⟨B, hBA, hB, (rAV_lt_one_iff hV hB.isA2).2 hBc⟩

theorem B1_4_5 [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (X : Subgroup (MulAut V)) :
    List.TFAE [IsFFModule X, {A | IsFFStarOffender X A}.Nonempty, qOf X ≤ 1] := by
  tfae_have 1 → 2 := by
    intro h
    obtain ⟨A, hA, hr⟩ := (isFFModule_iff hV).1 h
    obtain ⟨B, -, hB, -⟩ := B1_4_4_le hV hA hr
    exact ⟨B, hB⟩
  tfae_have 2 → 3 := by
    rintro ⟨A₀, hA₀⟩
    obtain ⟨A, hA, hmin⟩ := Set.exists_min_image {A | IsFFStarOffender X A}
      (fun B => Nat.card B) (Set.toFinite _) ⟨A₀, hA₀⟩
    have hquad : IsQuadratic A := B1_4_3_of_minimal hV hA fun B hB hBA =>
      Subgroup.eq_of_le_of_card_ge hBA (hmin B hB)
    have h := qOf_le_iff (X := X) (r := 1)
    rw [WithTop.coe_one] at h
    exact h.2 ⟨A, hA.isA2, hquad, B1_4_1 hV hA⟩
  tfae_have 3 → 1 := by
    intro h
    have h' := qOf_le_iff (X := X) (r := 1)
    rw [WithTop.coe_one] at h'
    obtain ⟨A, hA, -, hr⟩ := h'.1 h
    exact (isFFModule_iff hV).2 ⟨A, hA, hr⟩
  tfae_finish

theorem B1_4_6 [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)}
    (hX : ¬ IsStrongFFModule X) :
    {A | IsFFStarOffender X A} = {A | IsA2 X A ∧ rAV A = 1} := by
  ext A
  constructor
  · intro hA
    refine ⟨hA.isA2, le_antisymm (B1_4_1 hV hA) (not_lt.1 fun hlt => hX ?_)⟩
    exact (isStrongFFModule_iff hV).2 ⟨A, hA.isA2, hlt⟩
  · rintro ⟨hA2, hr⟩
    have heq := (rAV_eq_one_iff hV hA2).1 hr
    refine isFFStarOffender_iff.2 ⟨hA2, fun B hB => ?_⟩
    by_cases hbot : B = ⊥
    · subst hbot
      rw [B1.card_bot_mul_card_fixV]
      exact heq.le
    · have hB2 : IsA2 X B := hA2.mono hB hbot
      by_contra hlt
      push Not at hlt
      have : Nat.card V < Nat.card B * Nat.card (fixV B) := by omega
      exact hX ((isStrongFFModule_iff hV).2 ⟨B, hB2, (rAV_lt_one_iff hV hB2).2 this⟩)

@[expose] def IsStableFF (X : Subgroup (MulAut V)) (P : Set (Subgroup (MulAut V))) : Prop :=
  P.Nonempty ∧ (∀ A ∈ P, IsFFStarOffender X A) ∧
    (∀ A ∈ P, ∀ g ∈ X, A.map (MulAut.conj g).toMonoidHom ∈ P) ∧
    ∀ A ∈ P, ∀ B : Subgroup (MulAut V), FFLe X B A → B ∈ P

@[expose] def ffJP (P : Set (Subgroup (MulAut V))) (H : Subgroup (MulAut V)) :
    Subgroup (MulAut V) :=
  ⨆ (A : Subgroup (MulAut V)) (_ : A ∈ P) (_ : A ≤ H), A

namespace B1

def conjAut (g : MulAut V) (A : Subgroup (MulAut V)) : Subgroup (MulAut V) :=
  A.map (MulAut.conj g).toMonoidHom

theorem mem_conjAut {g x : MulAut V} {A : Subgroup (MulAut V)} :
    x ∈ conjAut g A ↔ g⁻¹ * x * g ∈ A := by
  unfold conjAut
  rw [Subgroup.mem_map_equiv]
  simp

theorem conjAut_le_iff {g : MulAut V} {A B : Subgroup (MulAut V)} :
    conjAut g B ≤ conjAut g A ↔ B ≤ A := by
  unfold conjAut
  exact Subgroup.map_le_map_iff_of_injective (MulAut.conj g).injective

theorem conjAut_conjAut_inv (g : MulAut V) (A : Subgroup (MulAut V)) :
    conjAut g (conjAut g⁻¹ A) = A := by
  ext x
  simp [mem_conjAut, mul_assoc]

theorem conjAut_inv_conjAut (g : MulAut V) (A : Subgroup (MulAut V)) :
    conjAut g⁻¹ (conjAut g A) = A := by
  ext x
  simp [mem_conjAut, mul_assoc]

theorem card_conjAut (g : MulAut V) (A : Subgroup (MulAut V)) :
    Nat.card (conjAut g A) = Nat.card A :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem fixV_conjAut (g : MulAut V) (A : Subgroup (MulAut V)) :
    fixV (conjAut g A) = (fixV A).map g.toMonoidHom := by
  ext v
  simp only [mem_fixV, Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
  constructor
  · intro h
    refine ⟨g⁻¹ v, fun a ha => ?_, by simp⟩
    have := h (g * a * g⁻¹) (mem_conjAut.2 (by simpa [mul_assoc] using ha))
    simp only [MulAut.mul_apply] at this
    have h3 : g (a (g⁻¹ v)) = g (g⁻¹ v) := by simpa using this
    exact g.injective h3
  · rintro ⟨w, hw, rfl⟩ x hx
    have := hw (g⁻¹ * x * g) (mem_conjAut.1 hx)
    simp only [MulAut.mul_apply] at this
    have h2 := congrArg g this
    simpa using h2

theorem card_fixV_conjAut (g : MulAut V) (A : Subgroup (MulAut V)) :
    Nat.card (fixV (conjAut g A)) = Nat.card (fixV A) := by
  rw [fixV_conjAut]
  exact Subgroup.card_map_of_injective g.injective

theorem isElemAbelian2_conjAut {g : MulAut V} {A : Subgroup (MulAut V)} (h : IsElemAbelian2 A) :
    IsElemAbelian2 (conjAut g A) := by
  refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
  · have := h.1 _ (mem_conjAut.1 hx) _ (mem_conjAut.1 hy)
    have h2 := congrArg (fun t => g * t * g⁻¹) this
    simpa [mul_assoc] using h2
  · have := h.2 _ (mem_conjAut.1 hx)
    have h2 := congrArg (fun t => g * t * g⁻¹) this
    simp only [mul_assoc, mul_one] at h2
    have h3 : (g⁻¹ * x * g) ^ 2 = g⁻¹ * x ^ 2 * g := by
      simp [pow_two, mul_assoc]
    rw [h3] at this
    have h4 : g * (g⁻¹ * x ^ 2 * g) * g⁻¹ = x ^ 2 := by simp [mul_assoc]
    rw [← h4, this]
    simp

theorem conjAut_ne_bot {g : MulAut V} {A : Subgroup (MulAut V)} (h : A ≠ ⊥) :
    conjAut g A ≠ ⊥ := by
  intro hb
  apply h
  have := conjAut_inv_conjAut g A
  rw [hb] at this
  rw [← this]
  ext x
  simp [mem_conjAut]

theorem conjAut_le {X : Subgroup (MulAut V)} {g : MulAut V} (hg : g ∈ X) {A : Subgroup (MulAut V)}
    (h : A ≤ X) : conjAut g A ≤ X := by
  intro x hx
  have h1 := h (mem_conjAut.1 hx)
  have h2 : g * (g⁻¹ * x * g) * g⁻¹ ∈ X := X.mul_mem (X.mul_mem hg h1) (X.inv_mem hg)
  simpa [mul_assoc] using h2

theorem isA2_conjAut {X A : Subgroup (MulAut V)} (h : IsA2 X A) {g : MulAut V} (hg : g ∈ X) :
    IsA2 X (conjAut g A) :=
  ⟨conjAut_le hg h.1, conjAut_ne_bot h.2.1, isElemAbelian2_conjAut h.2.2⟩

theorem isFFStarOffender_conjAut {X A : Subgroup (MulAut V)} (h : IsFFStarOffender X A)
    {g : MulAut V} (hg : g ∈ X) : IsFFStarOffender X (conjAut g A) :=
  isFFStarOffender_map_conj h hg

theorem ffLe_conjAut {X A B : Subgroup (MulAut V)} (h : FFLe X B A) {g : MulAut V}
    (hg : g ∈ X) : FFLe X (conjAut g B) (conjAut g A) := by
  obtain ⟨hB, hA, hBA, heq⟩ := h
  refine ⟨isA2_conjAut hB hg, isA2_conjAut hA hg, conjAut_le_iff.2 hBA, ?_⟩
  rw [card_conjAut, card_conjAut, card_fixV_conjAut, card_fixV_conjAut]
  exact heq

end B1

theorem B1_7 [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)}
    (hX : IsFFModule X) : IsStableFF X {A | IsFFStarMin X A} := by
  refine ⟨?_, fun A hA => hA.1, ?_, ?_⟩
  · obtain ⟨A₀, hA₀⟩ : {A | IsFFStarOffender X A}.Nonempty := by
      obtain ⟨A, hA, hr⟩ := (isFFModule_iff hV).1 hX
      obtain ⟨B, -, hB, -⟩ := B1_4_4_le hV hA hr
      exact ⟨B, hB⟩
    obtain ⟨A, hA, hmin⟩ := Set.exists_min_image {A | IsFFStarOffender X A}
      (fun B => Nat.card B) (Set.toFinite _) ⟨A₀, hA₀⟩
    refine ⟨A, hA, fun B hB hBA => ?_⟩
    exact Subgroup.eq_of_le_of_card_ge hBA.2.2.1 (hmin B hB)
  · intro A hA g hg
    show IsFFStarMin X (B1.conjAut g A)
    refine ⟨B1.isFFStarOffender_conjAut hA.1 hg, fun B hB hBA => ?_⟩
    have hB' : IsFFStarOffender X (B1.conjAut g⁻¹ B) := B1.isFFStarOffender_conjAut hB (X.inv_mem hg)
    have hBA' : FFLe X (B1.conjAut g⁻¹ B) A := by
      have := B1.ffLe_conjAut hBA (X.inv_mem hg)
      rwa [B1.conjAut_inv_conjAut] at this
    have := hA.2 _ hB' hBA'
    rw [← B1.conjAut_conjAut_inv g B, this]
  · intro A hA B hBA
    refine ⟨B1_4_2 hA.1 hBA, fun C hC hCB => ?_⟩
    have hCA : FFLe X C A := by
      obtain ⟨hC2, hB2, hCB', heqCB⟩ := hCB
      obtain ⟨-, hA2, hBA', heqBA⟩ := hBA
      exact ⟨hC2, hA2, hCB'.trans hBA', heqCB.trans heqBA⟩
    have hCA' := hA.2 C hC hCA
    have hBA2 : B = A := hA.2 B (B1_4_2 hA.1 hBA) hBA
    have hCB2 : C ≤ B := hCB.2.2.1
    rw [hBA2] at hCB2 ⊢
    exact hCA'

end CFSG.Quasithin
