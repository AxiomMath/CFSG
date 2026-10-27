module

public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item2113Proof

open Subgroup

section Exp

variable {A : Type*} [CommGroup A]

theorem orderOf_eq_three (h3 : ∀ x : A, x ^ 3 = 1) {x : A} (hx : x ≠ 1) : orderOf x = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime (h3 x) hx

theorem card_zpowers_three (h3 : ∀ x : A, x ^ 3 = 1) {x : A} (hx : x ≠ 1) :
    Nat.card (zpowers x) = 3 := by
  rw [Nat.card_zpowers, orderOf_eq_three h3 hx]

theorem mem_zpowers_three (h3 : ∀ x : A, x ^ 3 = 1) {x y : A} :
    y ∈ zpowers x ↔ y = 1 ∨ y = x ∨ y = x ^ 2 := by
  constructor
  · intro hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
    have h3' : x ^ (3 : ℤ) = 1 := by exact_mod_cast h3 x
    rw [zpow_eq_zpow_emod k h3']
    have h0 : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
    have h1 : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
    obtain h | h | h : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    · left; rw [h, zpow_zero]
    · right; left; rw [h, zpow_one]
    · right; right; rw [h]; exact zpow_natCast x 2
  · rintro (rfl | rfl | rfl)
    · exact one_mem _
    · exact mem_zpowers _
    · exact pow_mem (mem_zpowers _) 2

theorem sq_eq_inv (h3 : ∀ x : A, x ^ 3 = 1) (x : A) : x ^ 2 = x⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← pow_succ, h3 x]

variable [Finite A]

omit [Finite A] in
theorem card_subgroup_cases (h27 : Nat.card A = 27) (H : Subgroup A) :
    Nat.card H = 1 ∨ Nat.card H = 3 ∨ Nat.card H = 9 ∨ Nat.card H = 27 := by
  have hdvd : Nat.card H ∣ 3 ^ 3 := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← h27]
    exact H.card_subgroup_dvd_card
  obtain ⟨k, hk, hH⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  interval_cases k <;> simp_all

theorem eq_zpowers_of_card_three (h3 : ∀ x : A, x ^ 3 = 1) {H : Subgroup A}
    (hH : Nat.card H = 3) {x : A} (hx : x ∈ H) (hx1 : x ≠ 1) : H = zpowers x :=
  (eq_of_le_of_card_ge (zpowers_le.mpr hx) (by rw [hH, card_zpowers_three h3 hx1])).symm

theorem zpowers_inf_eq_bot (h3 : ∀ x : A, x ^ 3 = 1) {H : Subgroup A} {x : A} (hx : x ∉ H) :
    zpowers x ⊓ H = ⊥ := by
  have hx1 : x ≠ 1 := fun h => hx (h ▸ one_mem H)
  have hdvd : Nat.card ↥(zpowers x ⊓ H) ∣ 3 := by
    rw [← card_zpowers_three h3 hx1]
    exact card_dvd_of_le inf_le_left
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
  · exact card_eq_one.mp h
  · exfalso
    have heq : zpowers x ⊓ H = zpowers x :=
      eq_of_le_of_card_ge inf_le_left (by rw [h, card_zpowers_three h3 hx1])
    exact hx ((heq ▸ inf_le_right : zpowers x ≤ H) (mem_zpowers x))

theorem nine_le_card_closure (h3 : ∀ x : A, x ^ 3 = 1) (h27 : Nat.card A = 27) {x y : A}
    (hx : x ≠ 1) (hy : y ∉ zpowers x) : 9 ≤ Nat.card (closure ({x, y} : Set A)) := by
  have hle : zpowers x ≤ closure ({x, y} : Set A) :=
    zpowers_le.mpr (subset_closure (Set.mem_insert x _))
  have h3le : 3 ≤ Nat.card (closure ({x, y} : Set A)) := by
    rw [← card_zpowers_three h3 hx]
    exact card_le_of_le hle
  have hne : Nat.card (closure ({x, y} : Set A)) ≠ 3 := by
    intro h
    have heq : zpowers x = closure ({x, y} : Set A) :=
      eq_of_le_of_card_ge hle (by rw [h, card_zpowers_three h3 hx])
    exact hy (heq ▸ subset_closure (Set.mem_insert_of_mem x rfl))
  rcases card_subgroup_cases h27 (closure ({x, y} : Set A)) with h | h | h | h <;> omega

theorem eq_closure_of_card_nine (h3 : ∀ x : A, x ^ 3 = 1) (h27 : Nat.card A = 27)
    {H : Subgroup A} (hH : Nat.card H = 9) {x y : A} (hxH : x ∈ H) (hyH : y ∈ H) (hx : x ≠ 1)
    (hy : y ∉ zpowers x) : H = closure ({x, y} : Set A) := by
  have hle : closure ({x, y} : Set A) ≤ H := by
    rw [closure_le]
    rintro z (rfl | rfl)
    · exact hxH
    · exact hyH
  exact (eq_of_le_of_card_ge hle (by rw [hH]; exact nine_le_card_closure h3 h27 hx hy)).symm

theorem card_inf_of_card_nine (h27 : Nat.card A = 27) {B D : Subgroup A} (hB : Nat.card B = 9)
    (hD : Nat.card D = 9) (hne : B ≠ D) : Nat.card ↥(B ⊓ D) = 3 := by
  have hBi : B.index = 3 := by
    have h := B.card_mul_index
    rw [hB, h27] at h
    omega
  have hDi : D.index = 3 := by
    have h := D.card_mul_index
    rw [hD, h27] at h
    omega
  have hi : (B ⊓ D).index ≤ 9 := by
    have h := index_inf_le (H := B) (K := D)
    rw [hBi, hDi] at h
    exact h
  have hc := (B ⊓ D).card_mul_index
  rw [h27] at hc
  have hdvd : Nat.card ↥(B ⊓ D) ∣ 9 := hB ▸ card_dvd_of_le inf_le_left
  have hne9 : Nat.card ↥(B ⊓ D) ≠ 9 := by
    intro h
    have heq : B ⊓ D = B := eq_of_le_of_card_ge inf_le_left (by rw [h, hB])
    have hle : B ≤ D := heq ▸ inf_le_right
    exact hne (eq_of_le_of_card_ge hle (by rw [hB, hD]))
  have hpos : 0 < (B ⊓ D).index := Nat.pos_of_ne_zero (by intro h; rw [h] at hc; omega)
  have h3 : (3 : ℕ) ≤ Nat.card ↥(B ⊓ D) := by
    by_contra h
    have : Nat.card ↥(B ⊓ D) * (B ⊓ D).index ≤ 2 * 9 :=
      Nat.mul_le_mul (by omega) hi
    omega
  have : Nat.card ↥(B ⊓ D) ≤ 9 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases h : Nat.card ↥(B ⊓ D) <;> simp_all

omit [Finite A] in
theorem card_le_three_of_inf_eq_bot (h27 : Nat.card A = 27) {F B : Subgroup A}
    (hB : Nat.card B = 9) (h : F ⊓ B = ⊥) : Nat.card F ≤ 3 := by
  have hBi : B.index = 3 := by
    have h := B.card_mul_index
    rw [hB, h27] at h
    omega
  have hi := index_inf_le (H := F) (K := B)
  rw [h, index_bot, h27, hBi] at hi
  have hc := F.card_mul_index
  rw [h27] at hc
  by_contra hF
  have : Nat.card F * F.index ≥ 4 * 9 := Nat.mul_le_mul (by omega) (by omega)
  omega

theorem sup_zpowers_eq_top (h27 : Nat.card A = 27) {B : Subgroup A} (hB : Nat.card B = 9)
    {x : A} (hx : x ∉ B) : B ⊔ zpowers x = ⊤ := by
  have hle : B ≤ B ⊔ zpowers x := le_sup_left
  have hne : Nat.card ↥(B ⊔ zpowers x) ≠ 9 := by
    intro h
    have heq : B = B ⊔ zpowers x := eq_of_le_of_card_ge hle (by rw [h, hB])
    exact hx (heq ▸ (le_sup_right : zpowers x ≤ B ⊔ zpowers x) (mem_zpowers x))
  have h9 : 9 ≤ Nat.card ↥(B ⊔ zpowers x) := hB ▸ card_le_of_le hle
  apply eq_top_of_card_eq
  rcases card_subgroup_cases h27 (B ⊔ zpowers x) with h | h | h | h
  · omega
  · omega
  · exact absurd h hne
  · rw [h, h27]

end Exp

section Aut

variable {A : Type*} [Group A]

theorem map_zpowers_eq (σ : MulAut A) (x : A) :
    (zpowers x).map σ.toMonoidHom = zpowers (σ x) :=
  MonoidHom.map_zpowers σ.toMonoidHom x

theorem map_closure_pair (σ : MulAut A) (x y : A) :
    (closure ({x, y} : Set A)).map σ.toMonoidHom = closure ({σ x, σ y} : Set A) := by
  rw [MonoidHom.map_closure, Set.image_pair]
  rfl

theorem map_eq_of_le [Finite A] {σ : MulAut A} {H : Subgroup A}
    (h : H.map σ.toMonoidHom ≤ H) : H.map σ.toMonoidHom = H :=
  eq_of_le_of_card_ge h (by rw [card_map_of_injective σ.injective])

theorem apply_mem_of_map_eq {σ : MulAut A} {H : Subgroup A} (h : H.map σ.toMonoidHom = H)
    {x : A} (hx : x ∈ H) : σ x ∈ H :=
  h ▸ mem_map_of_mem σ.toMonoidHom hx

theorem inv_apply_mem_of_map_eq {σ : MulAut A} {H : Subgroup A} (h : H.map σ.toMonoidHom = H)
    {x : A} (hx : x ∈ H) : σ⁻¹ x ∈ H := by
  rw [← h] at hx
  obtain ⟨y, hy, hyx⟩ := mem_map.mp hx
  have : σ⁻¹ x = y := by
    rw [← hyx]
    exact σ.symm_apply_apply y
  rw [this]
  exact hy

@[expose] def fixSub (σ : MulAut A) : Subgroup A :=
  σ.toMonoidHom.eqLocus (MonoidHom.id A)

theorem mem_fixSub {σ : MulAut A} {x : A} : x ∈ fixSub σ ↔ σ x = x :=
  Iff.rfl

@[expose] def fixing (X : Set A) : Subgroup (MulAut A) where
  carrier := {σ | ∀ x ∈ X, σ x = x}
  mul_mem' {σ τ} hσ hτ x hx := by
    rw [MulAut.mul_apply, hτ x hx, hσ x hx]
  one_mem' x _ := rfl
  inv_mem' {σ} hσ x hx := by
    have h := congrArg (σ⁻¹ : MulAut A) (hσ x hx)
    rw [MulAut.inv_apply_self] at h
    exact h.symm

@[expose] def trivMod (B : Subgroup A) : Subgroup (MulAut A) where
  carrier := {σ | ∀ x, x⁻¹ * σ x ∈ B}
  mul_mem' {σ τ} hσ hτ x := by
    have h := B.mul_mem (hτ x) (hσ (τ x))
    rwa [mul_assoc, mul_inv_cancel_left] at h
  one_mem' x := by
    show x⁻¹ * x ∈ B
    rw [inv_mul_cancel]
    exact B.one_mem
  inv_mem' {σ} hσ x := by
    have h := B.inv_mem (hσ ((σ⁻¹ : MulAut A) x))
    rwa [MulAut.apply_inv_self, mul_inv_rev, inv_inv] at h

end Aut

section CommAut

variable {A : Type*} [CommGroup A]

@[expose] def invSub (σ : MulAut A) : Subgroup A :=
  σ.toMonoidHom.eqLocus (invMonoidHom : A →* A)

theorem mem_invSub {σ : MulAut A} {x : A} : x ∈ invSub σ ↔ σ x = x⁻¹ :=
  Iff.rfl

theorem eq_one_of_inv_eq (h3 : ∀ x : A, x ^ 3 = 1) {x : A} (h : x⁻¹ = x) : x = 1 := by
  have h2 : x * x = 1 := by
    have h' := mul_inv_cancel x
    rwa [h] at h'
  have := h3 x
  rwa [pow_succ, sq, h2, one_mul] at this

end CommAut

section Word

variable {A : Type*} [CommGroup A]

theorem mul_sq_sq (h3 : ∀ x : A, x ^ 3 = 1) (d d₂ : A) : d₂ * d ^ 2 * d ^ 2 = d₂ * d := by
  rw [mul_assoc, ← pow_add, show 2 + 2 = 3 + 1 by norm_num, pow_add, h3, one_mul, pow_one]

theorem mul_mul_sq (h3 : ∀ x : A, x ^ 3 = 1) (d d₂ : A) : d * (d₂ * d) ^ 2 = d₂ ^ 2 := by
  rw [mul_pow, mul_left_comm, ← pow_succ', h3, mul_one]

theorem mul_mul_sq' (h3 : ∀ x : A, x ^ 3 = 1) (d d₂ : A) : d₂ * (d * d₂ ^ 2) = d := by
  rw [mul_left_comm, ← pow_succ', h3, mul_one]

theorem exists_inv_pair (h3 : ∀ x : A, x ^ 3 = 1) {t t₂ : MulAut A} {d d₂ : A}
    (htd : t d = d) (ht : t d₂ = d₂ * d ∨ t d₂ = d₂ * d ^ 2) (ht₂d₂ : t₂ d₂ = d₂)
    (ht₂ : t₂ d = d * d₂ ∨ t₂ d = d * d₂ ^ 2) :
    ∃ z ∈ closure ({t, t₂} : Set (MulAut A)), z d = d⁻¹ ∧ z d₂ = d₂⁻¹ := by
  have htS : t ∈ closure ({t, t₂} : Set (MulAut A)) := subset_closure (Set.mem_insert t _)
  have ht₂S : t₂ ∈ closure ({t, t₂} : Set (MulAut A)) :=
    subset_closure (Set.mem_insert_of_mem t rfl)
  obtain ⟨t', ht'S, ht'd, ht'd₂⟩ : ∃ t' ∈ closure ({t, t₂} : Set (MulAut A)),
      t' d = d ∧ t' d₂ = d₂ * d := by
    rcases ht with h | h
    · exact ⟨t, htS, htd, h⟩
    · refine ⟨t ^ 2, pow_mem htS 2, ?_, ?_⟩
      · rw [pow_two, MulAut.mul_apply, htd, htd]
      · rw [pow_two, MulAut.mul_apply, h, map_mul, map_pow, h, htd, mul_sq_sq h3]
  obtain ⟨y, hyS, hyd₂, hyd⟩ : ∃ y ∈ closure ({t, t₂} : Set (MulAut A)),
      y d₂ = d₂ ∧ y d = d * d₂ ^ 2 := by
    rcases ht₂ with h | h
    · refine ⟨t₂ ^ 2, pow_mem ht₂S 2, ?_, ?_⟩
      · rw [pow_two, MulAut.mul_apply, ht₂d₂, ht₂d₂]
      · rw [pow_two, MulAut.mul_apply, h, map_mul, h, ht₂d₂, mul_assoc, ← pow_two]
    · exact ⟨t₂, ht₂S, ht₂d₂, h⟩
  have hsd : (t' * y * t') d = d₂ ^ 2 := by
    rw [MulAut.mul_apply, MulAut.mul_apply, ht'd, hyd, map_mul, map_pow, ht'd, ht'd₂,
      mul_mul_sq h3]
  have hsd₂ : (t' * y * t') d₂ = d := by
    rw [MulAut.mul_apply, MulAut.mul_apply, ht'd₂, map_mul, hyd₂, hyd, mul_mul_sq' h3, ht'd]
  refine ⟨(t' * y * t') * (t' * y * t'),
    mul_mem (mul_mem (mul_mem ht'S hyS) ht'S) (mul_mem (mul_mem ht'S hyS) ht'S), ?_, ?_⟩
  · rw [MulAut.mul_apply, hsd, map_pow, hsd₂, sq_eq_inv h3]
  · rw [MulAut.mul_apply, hsd₂, hsd, sq_eq_inv h3]

end Word

section Transvection

variable {A : Type*} [CommGroup A] [Finite A]

theorem fixSub_eq_closure (h3 : ∀ x : A, x ^ 3 = 1) (h27 : Nat.card A = 27) {c d : A}
    {t : MulAut A} (hc : c ≠ 1) (hdc : d ∉ zpowers c) (htc : t c = c) (htd : t d = d)
    (ht1 : t ≠ 1) :
    fixSub t = closure ({c, d} : Set A) ∧ Nat.card (closure ({c, d} : Set A)) = 9 := by
  have hle : closure ({c, d} : Set A) ≤ fixSub t := by
    rw [closure_le]
    rintro x (rfl | rfl)
    · exact htc
    · exact htd
  have hne : fixSub t ≠ ⊤ := by
    intro h
    apply ht1
    ext x
    have hx : x ∈ fixSub t := h ▸ mem_top x
    exact hx
  have h9 := nine_le_card_closure h3 h27 hc hdc
  have hF : Nat.card (fixSub t) = 9 := by
    have hle' := card_le_of_le hle
    have hne' : Nat.card (fixSub t) ≠ 27 := by
      intro h
      exact hne (eq_top_of_card_eq _ (by rw [h, h27]))
    rcases card_subgroup_cases h27 (fixSub t) with h | h | h | h <;> omega
  have hD : Nat.card (closure ({c, d} : Set A)) = 9 := by
    have := card_le_of_le hle
    omega
  exact ⟨(eq_of_le_of_card_ge hle (by rw [hF, hD])).symm, hD⟩

omit [Finite A] in
theorem apply_eq_mul_of_ne (h3 : ∀ x : A, x ^ 3 = 1) {d : A} {t : MulAut A}
    (htcomm : ∀ x, x⁻¹ * t x ∈ zpowers d) {x : A} (hx : t x ≠ x) :
    t x = x * d ∨ t x = x * d ^ 2 := by
  rcases (mem_zpowers_three h3).mp (htcomm x) with h | h | h
  · exact absurd (inv_mul_eq_one.mp h).symm hx
  · left
    rw [← h, mul_inv_cancel_left]
  · right
    rw [← h, mul_inv_cancel_left]

omit [Finite A] in
theorem conj_comm_mem {d : A} {t g : MulAut A} (htcomm : ∀ x, x⁻¹ * t x ∈ zpowers d) (x : A) :
    x⁻¹ * (g * t * g⁻¹) x ∈ zpowers (g d) := by
  have h := mem_map_of_mem g.toMonoidHom (htcomm ((g⁻¹ : MulAut A) x))
  rw [map_zpowers_eq] at h
  simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv, MulAut.apply_inv_self] at h
  simpa only [MulAut.mul_apply] using h

end Transvection

section Cases

variable {A : Type*} [CommGroup A] [Finite A] {S : Subgroup (MulAut A)} {c d : A} {t : MulAut A}

omit [Finite A] in
theorem eq_or_eq_inv_of_mem_zpowers (h3 : ∀ x : A, x ^ 3 = 1) {x y : A} (hy : y ∈ zpowers x)
    (hy1 : y ≠ 1) : y = x ∨ y = x⁻¹ := by
  rcases (mem_zpowers_three h3).mp hy with h | h | h
  · exact absurd h hy1
  · exact Or.inl h
  · exact Or.inr (h.trans (sq_eq_inv h3 x))

theorem false_of_card_three (h3 : ∀ x : A, x ^ 3 = 1) (h27 : Nat.card A = 27) (hc : c ≠ 1)
    (hdc : d ∉ zpowers c) (htS : t ∈ S) (htc : t c = c) (htd : t d = d) (ht1 : t ≠ 1)
    (htcomm : ∀ x, x⁻¹ * t x ∈ zpowers d)
    (hDc : ∀ σ ∈ S, (closure ({c, d} : Set A)).map σ.toMonoidHom = closure ({c, d} : Set A) →
      (zpowers c).map σ.toMonoidHom = zpowers c)
    {B : Subgroup A} (hB : Nat.card B = 3) (hBS : ∀ σ ∈ S, B.map σ.toMonoidHom = B)
    (hBc : B ≠ zpowers c) (hBd : B ≠ zpowers d) {g : MulAut A} (hgS : g ∈ S)
    (hgD : (closure ({c, d} : Set A)).map g.toMonoidHom ≠ closure ({c, d} : Set A)) :
    False := by
  obtain ⟨hFix, hD9⟩ := fixSub_eq_closure h3 h27 hc hdc htc htd ht1
  set D := closure ({c, d} : Set A) with hDdef
  have hd1 : d ≠ 1 := fun h => hdc (h ▸ one_mem _)
  have hcD : c ∈ D := subset_closure (Set.mem_insert c _)
  have hdD : d ∈ D := subset_closure (Set.mem_insert_of_mem c rfl)
  obtain ⟨b, hbB, hb1⟩ : ∃ b ∈ B, b ≠ 1 := by
    by_contra h
    have hbot : B = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      by_contra hx1
      exact h ⟨x, hx, hx1⟩
    rw [hbot, card_bot] at hB
    omega
  have hBb : B = zpowers b := eq_zpowers_of_card_three h3 hB hbB hb1
  have hdB : d ∉ B := fun h => hBd (eq_zpowers_of_card_three h3 hB h hd1)
  have hBD : B ≤ D := by
    intro x hx
    have htx : t x ∈ B := apply_mem_of_map_eq (hBS t htS) hx
    have hmem : x⁻¹ * t x ∈ zpowers d ⊓ B := ⟨htcomm x, B.mul_mem (B.inv_mem hx) htx⟩
    rw [zpowers_inf_eq_bot h3 hdB, mem_bot] at hmem
    rw [← hFix]
    exact (inv_mul_eq_one.mp hmem).symm
  set D₂ := D.map g.toMonoidHom with hD₂def
  have hD₂9 : Nat.card D₂ = 9 := by rw [hD₂def, card_map_of_injective g.injective, hD9]
  have hBD₂ : B ≤ D₂ := by
    rw [← hBS g hgS]
    exact map_mono hBD
  have hinter : D ⊓ D₂ = B := by
    have h := card_inf_of_card_nine h27 hD9 hD₂9 (Ne.symm hgD)
    exact (eq_of_le_of_card_ge (le_inf hBD hBD₂) (by rw [h, hB])).symm
  set d₂ := g d with hd₂def
  have hd₂D₂ : d₂ ∈ D₂ := mem_map_of_mem g.toMonoidHom hdD
  have hd₂D : d₂ ∉ D := by
    intro h
    have h' : d₂ ∈ B := hinter ▸ ⟨h, hd₂D₂⟩
    apply hdB
    have := inv_apply_mem_of_map_eq (hBS g hgS) h'
    rwa [hd₂def, MulAut.inv_apply_self] at this
  have hdD₂ : d ∉ D₂ := fun h => hdB (hinter ▸ ⟨hdD, h⟩)
  have htd₂ : t d₂ = d₂ * d ∨ t d₂ = d₂ * d ^ 2 :=
    apply_eq_mul_of_ne h3 htcomm (fun h => hd₂D (hFix ▸ h))
  set t₂ := g * t * g⁻¹ with ht₂def
  have ht₂S : t₂ ∈ S := mul_mem (mul_mem hgS htS) (inv_mem hgS)
  have ht₂d₂ : t₂ d₂ = d₂ := by
    rw [ht₂def, MulAut.mul_apply, MulAut.mul_apply, hd₂def, MulAut.inv_apply_self, htd]
  have ht₂d : t₂ d = d * d₂ ∨ t₂ d = d * d₂ ^ 2 := by
    have hne : t₂ d ≠ d := by
      intro h
      apply hdD₂
      have h' : t ((g⁻¹ : MulAut A) d) = (g⁻¹ : MulAut A) d := by
        have := congrArg (g⁻¹ : MulAut A) h
        simpa [ht₂def, MulAut.mul_apply] using this
      have hmem : (g⁻¹ : MulAut A) d ∈ D := hFix ▸ h'
      exact ⟨(g⁻¹ : MulAut A) d, hmem, by simp⟩
    exact apply_eq_mul_of_ne h3 (conj_comm_mem htcomm) hne
  obtain ⟨z, hzcl, hzd, hzd₂⟩ := exists_inv_pair h3 htd htd₂ ht₂d₂ ht₂d
  have hcl : closure ({t, t₂} : Set (MulAut A)) ≤ S := by
    rw [closure_le]
    rintro σ (rfl | rfl)
    exacts [htS, ht₂S]
  have hzS : z ∈ S := hcl hzcl
  have hzb : z b = b := by
    have hfix : closure ({t, t₂} : Set (MulAut A)) ≤ fixing ({b} : Set A) := by
      rw [closure_le]
      rintro σ (rfl | rfl) x hx
      · rw [Set.mem_singleton_iff.mp hx]
        exact (hFix ▸ hBD hbB : b ∈ fixSub σ)
      · rw [Set.mem_singleton_iff.mp hx]
        have hgb : (g⁻¹ : MulAut A) b ∈ B := inv_apply_mem_of_map_eq (hBS g hgS) hbB
        have h' : t ((g⁻¹ : MulAut A) b) = (g⁻¹ : MulAut A) b :=
          (hFix ▸ hBD hgb : (g⁻¹ : MulAut A) b ∈ fixSub t)
        rw [ht₂def, MulAut.mul_apply, MulAut.mul_apply, h', MulAut.apply_inv_self]
    exact hfix hzcl b rfl
  have hdb : d ∉ zpowers b := fun h => hdB (by rw [hBb]; exact h)
  have hDbd : D = closure ({b, d} : Set A) :=
    eq_closure_of_card_nine h3 h27 hD9 (hBD hbB) hdD hb1 hdb
  have hzD : D.map z.toMonoidHom = D := by
    apply map_eq_of_le
    rw [hDbd, map_closure_pair, hzb, hzd, closure_le]
    rintro x (rfl | rfl)
    · exact subset_closure (Set.mem_insert _ _)
    · exact inv_mem (subset_closure (Set.mem_insert_of_mem _ rfl))
  have hzc : z c ∈ zpowers c := by
    have h := mem_map_of_mem z.toMonoidHom (mem_zpowers c)
    rwa [hDc z hzS hzD] at h
  have hzc1 : z c ≠ 1 := fun h => hc (z.injective (h.trans (map_one z).symm))
  have hcb : c ∉ zpowers b := fun h =>
    hBc (eq_zpowers_of_card_three h3 hB (by rw [hBb]; exact h) hc)
  have hDbc : D = closure ({b, c} : Set A) :=
    eq_closure_of_card_nine h3 h27 hD9 (hBD hbB) hcD hb1 hcb
  rcases eq_or_eq_inv_of_mem_zpowers h3 hzc hzc1 with h1 | h1
  · have hfixD : D ≤ fixSub z := by
      rw [hDbc, closure_le]
      rintro x (rfl | rfl)
      exacts [hzb, h1]
    have h := hfixD hdD
    rw [mem_fixSub, hzd] at h
    exact hd1 (eq_one_of_inv_eq h3 h)
  · have hinvD : D ≤ invSub z := by
      rw [hDdef, closure_le]
      rintro x (rfl | rfl)
      exacts [h1, hzd]
    have h := hinvD (hBD hbB)
    rw [mem_invSub, hzb] at h
    exact hb1 (eq_one_of_inv_eq h3 h.symm)

theorem normalizes_of_card_nine (h3 : ∀ x : A, x ^ 3 = 1) (h27 : Nat.card A = 27) (hc : c ≠ 1)
    (hdc : d ∉ zpowers c) (htS : t ∈ S) (htc : t c = c) (htd : t d = d) (ht1 : t ≠ 1)
    (htcomm : ∀ x, x⁻¹ * t x ∈ zpowers d)
    (hdD : ∀ σ ∈ S, (zpowers d).map σ.toMonoidHom = zpowers d →
      (closure ({c, d} : Set A)).map σ.toMonoidHom = closure ({c, d} : Set A))
    (hDc : ∀ σ ∈ S, (closure ({c, d} : Set A)).map σ.toMonoidHom = closure ({c, d} : Set A) →
      (zpowers c).map σ.toMonoidHom = zpowers c)
    {B : Subgroup A} (hB : Nat.card B = 9) (hBS : ∀ σ ∈ S, B.map σ.toMonoidHom = B)
    (hBD : B ≠ closure ({c, d} : Set A)) {g : MulAut A} (hgS : g ∈ S)
    (hgd : (zpowers d).map g.toMonoidHom ≠ zpowers d) :
    ∀ σ ∈ S, (zpowers c).map σ.toMonoidHom = zpowers c := by
  obtain ⟨hFix, hD9⟩ := fixSub_eq_closure h3 h27 hc hdc htc htd ht1
  set D := closure ({c, d} : Set A) with hDdef
  have hd1 : d ≠ 1 := fun h => hdc (h ▸ one_mem _)
  have hdD' : d ∈ D := subset_closure (Set.mem_insert_of_mem c rfl)
  have hdB : d ∈ B := by
    have hBnle : ¬ B ≤ D := fun h => hBD (eq_of_le_of_card_ge h (by rw [hB, hD9]))
    obtain ⟨x, hxB, hxD⟩ := Set.not_subset.mp hBnle
    have htx : t x ≠ x := fun h => hxD (hFix ▸ h)
    have hmem : x⁻¹ * t x ∈ B :=
      B.mul_mem (B.inv_mem hxB) (apply_mem_of_map_eq (hBS t htS) hxB)
    rcases apply_eq_mul_of_ne h3 htcomm htx with h | h
    · rwa [h, inv_mul_cancel_left] at hmem
    · rw [h, inv_mul_cancel_left] at hmem
      have h' := B.mul_mem hmem hmem
      rwa [← pow_add, show 2 + 2 = 3 + 1 by norm_num, pow_add, h3, one_mul, pow_one] at h'
  have hBDinter : B ⊓ D = zpowers d :=
    eq_zpowers_of_card_three h3 (card_inf_of_card_nine h27 hB hD9 hBD) ⟨hdB, hdD'⟩ hd1
  have hcB : c ∉ B := by
    intro h
    apply hBD
    have hle : D ≤ B := by
      rw [hDdef, closure_le]
      rintro x (rfl | rfl)
      exacts [h, hdB]
    exact (eq_of_le_of_card_ge hle (by rw [hB, hD9])).symm
  set d₂ := g d with hd₂def
  have hd₂B : d₂ ∈ B := apply_mem_of_map_eq (hBS g hgS) hdB
  have hd₂1 : d₂ ≠ 1 := fun h => hd1 (g.injective (h.trans (map_one g).symm))
  have hd₂d : d₂ ∉ zpowers d := by
    intro h
    apply hgd
    rw [map_zpowers_eq]
    exact eq_of_le_of_card_ge (zpowers_le.mpr h)
      (by rw [card_zpowers_three h3 hd1, card_zpowers_three h3 hd₂1])
  have hd₂D : d₂ ∉ D := fun h => hd₂d (hBDinter ▸ ⟨hd₂B, h⟩)
  have htd₂ := apply_eq_mul_of_ne h3 htcomm (fun h => hd₂D (hFix ▸ h))
  set t₂ := g * t * g⁻¹ with ht₂def
  have ht₂S : t₂ ∈ S := mul_mem (mul_mem hgS htS) (inv_mem hgS)
  have ht₂d₂ : t₂ d₂ = d₂ := by
    rw [ht₂def, MulAut.mul_apply, MulAut.mul_apply, hd₂def, MulAut.inv_apply_self, htd]
  have ht₂d : t₂ d = d * d₂ ∨ t₂ d = d * d₂ ^ 2 := by
    have hne : t₂ d ≠ d := by
      intro h
      have h' : t ((g⁻¹ : MulAut A) d) = (g⁻¹ : MulAut A) d := by
        have := congrArg (g⁻¹ : MulAut A) h
        simpa [ht₂def, MulAut.mul_apply] using this
      have hyB : (g⁻¹ : MulAut A) d ∈ B := inv_apply_mem_of_map_eq (hBS g hgS) hdB
      have hyd : (g⁻¹ : MulAut A) d ∈ zpowers d := hBDinter ▸ ⟨hyB, hFix ▸ h'⟩
      apply hgd
      have hle : zpowers d ≤ (zpowers d).map g.toMonoidHom :=
        zpowers_le.mpr ⟨(g⁻¹ : MulAut A) d, hyd, by simp⟩
      exact (eq_of_le_of_card_ge hle (by rw [card_map_of_injective g.injective])).symm
    exact apply_eq_mul_of_ne h3 (conj_comm_mem htcomm) hne
  obtain ⟨z, hzcl, hzd, hzd₂⟩ := exists_inv_pair h3 htd htd₂ ht₂d₂ ht₂d
  have hzS : z ∈ S := by
    have hcl : closure ({t, t₂} : Set (MulAut A)) ≤ S := by
      rw [closure_le]
      rintro σ (rfl | rfl)
      exacts [htS, ht₂S]
    exact hcl hzcl
  have hzB : z ∈ trivMod B := by
    have htB : t ∈ trivMod B := fun x => (zpowers_le.mpr hdB) (htcomm x)
    have ht₂B : t₂ ∈ trivMod B := fun x => (zpowers_le.mpr hd₂B) (conj_comm_mem htcomm x)
    have hcl : closure ({t, t₂} : Set (MulAut A)) ≤ trivMod B := by
      rw [closure_le]
      rintro σ (rfl | rfl)
      exacts [htB, ht₂B]
    exact hcl hzcl
  have hBdd : B = closure ({d, d₂} : Set A) :=
    eq_closure_of_card_nine h3 h27 hB hdB hd₂B hd1 hd₂d
  have hzinv : ∀ x ∈ B, z x = x⁻¹ := by
    have hle : B ≤ invSub z := by
      rw [hBdd, closure_le]
      rintro x (rfl | rfl)
      exacts [hzd, hzd₂]
    exact fun x hx => hle hx
  have hR0 : ∀ r ∈ S, (∀ x ∈ B, r x = x) → r ∈ trivMod B → r = 1 := by
    intro r hrS hrB hrA
    have hrd : (zpowers d).map r.toMonoidHom = zpowers d := by
      rw [map_zpowers_eq, hrB d hdB]
    have hrc := hDc r hrS (hdD r hrS hrd)
    have hrc' : r c ∈ zpowers c := by
      have h := mem_map_of_mem r.toMonoidHom (mem_zpowers c)
      rwa [hrc] at h
    have hrc'' : c⁻¹ * r c ∈ zpowers c ⊓ B :=
      mem_inf.mpr ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ (mem_zpowers c)) hrc', hrA c⟩
    rw [zpowers_inf_eq_bot h3 hcB, mem_bot] at hrc''
    have hrcc : r c = c := (inv_mul_eq_one.mp hrc'').symm
    have htop : B ⊔ zpowers c ≤ fixSub r := sup_le (fun x hx => hrB x hx) (zpowers_le.mpr hrcc)
    rw [sup_zpowers_eq_top h27 hB hcB] at htop
    ext x
    exact htop (mem_top x)
  have hzcent : ∀ σ ∈ S, σ * z = z * σ := by
    intro σ hσ
    have hconj : σ * z * σ⁻¹ ∈ trivMod B := by
      intro x
      have h := apply_mem_of_map_eq (hBS σ hσ) (hzB ((σ⁻¹ : MulAut A) x))
      simpa [MulAut.mul_apply, map_mul, map_inv] using h
    have hr : σ * z * σ⁻¹ * z⁻¹ = 1 := by
      refine hR0 _ (mul_mem (mul_mem (mul_mem hσ hzS) (inv_mem hσ)) (inv_mem hzS)) ?_
        (mul_mem hconj (inv_mem hzB))
      intro x hx
      have hzx : (z⁻¹ : MulAut A) x = x⁻¹ := by
        have h := hzinv x⁻¹ (B.inv_mem hx)
        rw [inv_inv] at h
        have h' := congrArg (z⁻¹ : MulAut A) h
        rw [MulAut.inv_apply_self] at h'
        exact h'.symm
      have hσx : (σ⁻¹ : MulAut A) x⁻¹ ∈ B :=
        inv_apply_mem_of_map_eq (hBS σ hσ) (B.inv_mem hx)
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.mul_apply, hzx, hzinv _ hσx, map_inv,
        MulAut.apply_inv_self, inv_inv]
    have h := mul_inv_eq_one.mp hr
    calc σ * z = σ * z * σ⁻¹ * σ := by rw [inv_mul_cancel_right]
      _ = z * σ := by rw [h]
  have hzdmap : (zpowers d).map z.toMonoidHom = zpowers d := by
    rw [map_zpowers_eq, hzd, zpowers_inv]
  have hzcmap := hDc z hzS (hdD z hzS hzdmap)
  have hzc : z c = c := by
    have hzc' : z c ∈ zpowers c := by
      have h := mem_map_of_mem z.toMonoidHom (mem_zpowers c)
      rwa [hzcmap] at h
    have h : c⁻¹ * z c ∈ zpowers c ⊓ B :=
      mem_inf.mpr ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ (mem_zpowers c)) hzc', hzB c⟩
    rw [zpowers_inf_eq_bot h3 hcB, mem_bot] at h
    exact (inv_mul_eq_one.mp h).symm
  have hFz : fixSub z = zpowers c := by
    have hinf : fixSub z ⊓ B = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hx1, hx2⟩
      rw [mem_bot]
      exact eq_one_of_inv_eq h3 ((hzinv x hx2).symm.trans hx1)
    have hle : zpowers c ≤ fixSub z := zpowers_le.mpr hzc
    exact (eq_of_le_of_card_ge hle (by
      rw [card_zpowers_three h3 hc]
      exact card_le_three_of_inf_eq_bot h27 hB hinf)).symm
  intro σ hσ
  rw [← hFz]
  apply map_eq_of_le
  rintro _ ⟨x, hx, rfl⟩
  show z (σ x) = σ x
  have h := congrArg (fun φ : MulAut A => φ x) (hzcent σ hσ)
  simp only [MulAut.mul_apply] at h
  rw [← h, mem_fixSub.mp hx]

theorem normalizes_of_reducible (h3 : ∀ x : A, x ^ 3 = 1) (h27 : Nat.card A = 27) (hc : c ≠ 1)
    (hdc : d ∉ zpowers c) (htS : t ∈ S) (htc : t c = c) (htd : t d = d) (ht1 : t ≠ 1)
    (htcomm : ∀ x, x⁻¹ * t x ∈ zpowers d)
    (hred : ∃ B : Subgroup A, B ≠ ⊥ ∧ B ≠ ⊤ ∧ ∀ σ ∈ S, B.map σ.toMonoidHom = B)
    (hdD : ∀ σ ∈ S, (zpowers d).map σ.toMonoidHom = zpowers d →
      (closure ({c, d} : Set A)).map σ.toMonoidHom = closure ({c, d} : Set A))
    (hDc : ∀ σ ∈ S, (closure ({c, d} : Set A)).map σ.toMonoidHom = closure ({c, d} : Set A) →
      (zpowers c).map σ.toMonoidHom = zpowers c) :
    ∀ σ ∈ S, (zpowers c).map σ.toMonoidHom = zpowers c := by
  obtain ⟨B, hB1, hBA, hBS⟩ := hred
  have hdS : (∀ σ ∈ S, (zpowers d).map σ.toMonoidHom = zpowers d) →
      ∀ σ ∈ S, (zpowers c).map σ.toMonoidHom = zpowers c :=
    fun h σ hσ => hDc σ hσ (hdD σ hσ (h σ hσ))
  have hB1' : Nat.card B ≠ 1 := fun h => hB1 (card_eq_one.mp h)
  have hB27 : Nat.card B ≠ 27 := fun h => hBA (eq_top_of_card_eq _ (by rw [h, h27]))
  rcases card_subgroup_cases h27 B with h | h | h | h
  · exact absurd h hB1'
  · by_cases hBc : B = zpowers c
    · exact hBc ▸ hBS
    by_cases hBd : B = zpowers d
    · exact hdS (hBd ▸ hBS)
    intro σ hσ
    by_contra hne
    exact false_of_card_three h3 h27 hc hdc htS htc htd ht1 htcomm hDc h hBS hBc hBd hσ
      (fun h' => hne (hDc σ hσ h'))
  · by_cases hBD : B = closure ({c, d} : Set A)
    · exact fun σ hσ => hDc σ hσ (hBD ▸ hBS σ hσ)
    by_cases hd : ∃ g ∈ S, (zpowers d).map g.toMonoidHom ≠ zpowers d
    · obtain ⟨g, hgS, hgd⟩ := hd
      exact normalizes_of_card_nine h3 h27 hc hdc htS htc htd ht1 htcomm hdD hDc h hBS hBD hgS
        hgd
    · push Not at hd
      exact hdS hd
  · exact absurd h hB27

end Cases

end CFSG.RankThree.PartTwo.Sec21.Item2113Proof
