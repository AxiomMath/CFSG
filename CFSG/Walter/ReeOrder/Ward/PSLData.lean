module

public import CFSG.CharacterTheory.Blocks.VirtualCharacterRing

public section

open scoped BigOperators Classical

namespace CFSG.Walter.Ward

open CFSG

structure PSLData (L : Type) [Group L] [Fintype L] (q : ℕ) (e : ℤ) where
  e_eq : e = 1 ∨ e = -1
  q_mod : (q : ℤ) % 8 = 4 + e
  q_ge : 7 ≤ q
  card : 2 * Nat.card L = q * (q ^ 2 - 1)
  p : ℕ
  p_prime : p.Prime
  p_dvd : p ∣ q
  O : Subgroup L
  E : Subgroup L
  U : Subgroup L
  O_cyclic : IsCyclic O
  E_cyclic : IsCyclic E
  O_card : 2 * (Nat.card O : ℤ) = q + e
  E_card : 2 * (Nat.card E : ℤ) = q - e
  U_order : ∀ x ∈ U, x ≠ 1 → orderOf x = p
  classes : ∀ g : L, g = 1 ∨ (∃ x ∈ U, x ≠ 1 ∧ IsConj g x) ∨ (∃ x ∈ O, x ≠ 1 ∧ IsConj g x) ∨
    (∃ x ∈ E, x ≠ 1 ∧ IsConj g x)
  U_O : ∀ x ∈ U, x ≠ 1 → ∀ y ∈ O, y ≠ 1 → ¬ IsConj x y
  O_centralizer : ∀ x ∈ O, x ≠ 1 →
    Nat.card (Subgroup.centralizer ({x} : Set L)) = Nat.card O
  E_centralizer : ∀ x ∈ E, orderOf x = 2 →
    Nat.card (Subgroup.centralizer ({x} : Set L)) = 2 * Nat.card E
  u : L
  u_mem : u ∈ U
  u_ne : u ≠ 1
  St : L → ℂ
  ηp : L → ℂ
  ηm : L → ℂ
  XO : (O →* ℂˣ) → L → ℂ
  XE : (E →* ℂˣ) → L → ℂ
  RFam : Finset (L → ℂ)
  SFam : Finset (L → ℂ)
  mem_RFam : ∀ θ, θ ∈ RFam ↔ ∃ α : O →* ℂˣ, α ^ 2 ≠ 1 ∧ XO α = θ
  mem_SFam : ∀ θ, θ ∈ SFam ↔ ∃ β : E →* ℂˣ, β ^ 2 ≠ 1 ∧ XE β = θ
  card_RFam : 4 * (RFam.card : ℤ) = q + e - 2
  card_SFam : 4 * (SFam.card : ℤ) = q - e - 4
  irr : BlocksIrr L =
    insert 1 (insert ηp (insert ηm (insert St ((RFam : Set (L → ℂ)) ∪ SFam))))
  ηp_ne_ηm : ηp ≠ ηm
  XE_eq_iff : ∀ β β' : E →* ℂˣ, β ^ 2 ≠ 1 → (XE β' = XE β ↔ β' = β ∨ β' = β⁻¹)
  χ₀ : E →* ℂˣ
  χ₀_ne : χ₀ ≠ 1
  χ₀_sq : χ₀ ^ 2 = 1
  St_one : St 1 = q
  ηp_one : ηp 1 = ((q : ℂ) + e) / 2
  ηm_one : ηm 1 = ((q : ℂ) + e) / 2
  XO_one : ∀ α, XO α 1 = q - e
  XE_one : ∀ β, XE β 1 = q + e
  St_U : ∀ x ∈ U, x ≠ 1 → St x = 0
  η_U : ∀ x ∈ U, x ≠ 1 → ηp x + ηm x = e
  XO_U : ∀ α, ∀ x ∈ U, x ≠ 1 → XO α x = -e
  XE_U : ∀ β, ∀ x ∈ U, x ≠ 1 → XE β x = e
  St_O : ∀ x ∈ O, x ≠ 1 → St x = -e
  ηp_O : ∀ x ∈ O, x ≠ 1 → ηp x = 0
  ηm_O : ∀ x ∈ O, x ≠ 1 → ηm x = 0
  XO_O : ∀ α (x : L) (hx : x ∈ O), x ≠ 1 →
    XO α x = -e * (((α ⟨x, hx⟩ : ℂˣ) : ℂ) + (((α ⟨x, hx⟩)⁻¹ : ℂˣ) : ℂ))
  XE_O : ∀ β, ∀ x ∈ O, x ≠ 1 → XE β x = 0
  St_E : ∀ x ∈ E, x ≠ 1 → St x = e
  ηp_E : ∀ (x : L) (hx : x ∈ E), x ≠ 1 → ηp x = e * ((χ₀ ⟨x, hx⟩ : ℂˣ) : ℂ)
  ηm_E : ∀ (x : L) (hx : x ∈ E), x ≠ 1 → ηm x = e * ((χ₀ ⟨x, hx⟩ : ℂˣ) : ℂ)
  XO_E : ∀ α, ∀ x ∈ E, x ≠ 1 → XO α x = 0
  XE_E : ∀ β (x : L) (hx : x ∈ E), x ≠ 1 →
    XE β x = e * (((β ⟨x, hx⟩ : ℂˣ) : ℂ) + (((β ⟨x, hx⟩)⁻¹ : ℂˣ) : ℂ))
  conj_ηp : ∀ x ∈ U, x ≠ 1 → starRingEnd ℂ (ηp x) = if e = -1 then ηm x else ηp x
  conj_ηm : ∀ x ∈ U, x ≠ 1 → starRingEnd ℂ (ηm x) = if e = -1 then ηp x else ηm x
  galois_U : ∀ N : ℕ, 0 < N → ∃ k : ℕ, k.Coprime N ∧
    ∀ x ∈ U, x ≠ 1 → ηp (x ^ k) = ηm x ∧ ηm (x ^ k) = ηp x
  principal : ∀ m : Ideal BlocksAlgInt, m.IsMaximal → (2 : BlocksAlgInt) ∈ m →
    BlocksPrincipalBlock m L = {1, ηp, ηm, St}

namespace PSLData

variable {L : Type} [Group L] [Fintype L] {q : ℕ} {e : ℤ} (D : PSLData L q e)

include D in
theorem e_sq : e * e = 1 := by rcases D.e_eq with rfl | rfl <;> norm_num

theorem O_odd : Odd (Nat.card D.O) := by
  have h1 := D.O_card
  have h2 := D.q_mod
  have h3 := D.e_eq
  exact Nat.odd_iff.mpr (by omega)

theorem p_ne_two : D.p ≠ 2 := by
  intro h2
  have h := D.p_dvd
  rw [h2] at h
  have h3 := D.q_mod
  have h4 := D.e_eq
  obtain ⟨k, hk⟩ := h
  omega

theorem not_p_dvd_O : ¬ D.p ∣ Nat.card D.O := by
  intro h
  obtain ⟨a, ha⟩ := h
  obtain ⟨b, hb⟩ := D.p_dvd
  have ha' : (Nat.card D.O : ℤ) = D.p * a := by exact_mod_cast ha
  have hb' : (q : ℤ) = D.p * b := by exact_mod_cast hb
  have h1 := D.O_card
  have hpe : (D.p : ℤ) ∣ e := ⟨2 * a - b, by linear_combination -h1 + 2 * ha' - hb'⟩
  have hp1 : (D.p : ℤ) = 1 :=
    Int.eq_one_of_dvd_one (by positivity) (hpe.trans ⟨e, D.e_sq.symm⟩)
  have := D.p_prime.two_le
  omega

theorem not_p_dvd_E : ¬ D.p ∣ Nat.card D.E := by
  intro h
  obtain ⟨a, ha⟩ := h
  obtain ⟨b, hb⟩ := D.p_dvd
  have ha' : (Nat.card D.E : ℤ) = D.p * a := by exact_mod_cast ha
  have hb' : (q : ℤ) = D.p * b := by exact_mod_cast hb
  have h1 := D.E_card
  have hpe : (D.p : ℤ) ∣ e := ⟨b - 2 * a, by linear_combination h1 - 2 * ha' + hb'⟩
  have hp1 : (D.p : ℤ) = 1 :=
    Int.eq_one_of_dvd_one (by positivity) (hpe.trans ⟨e, D.e_sq.symm⟩)
  have := D.p_prime.two_le
  omega

theorem coprime_O_E : (Nat.card D.O).Coprime (Nat.card D.E) := by
  have h1 := D.O_card
  have h2 := D.E_card
  rw [Nat.coprime_iff_gcd_eq_one]
  have hd1 : (Nat.gcd (Nat.card D.O) (Nat.card D.E) : ℤ) ∣ Nat.card D.O :=
    Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left _ _)
  have hd2 : (Nat.gcd (Nat.card D.O) (Nat.card D.E) : ℤ) ∣ Nat.card D.E :=
    Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right _ _)
  obtain ⟨c, hc⟩ := dvd_sub hd1 hd2
  have hge : (Nat.gcd (Nat.card D.O) (Nat.card D.E) : ℤ) ∣ e := ⟨c, by linarith⟩
  have hd : (Nat.gcd (Nat.card D.O) (Nat.card D.E) : ℤ) ∣ 1 := hge.trans ⟨e, D.e_sq.symm⟩
  have := Int.eq_one_of_dvd_one (by positivity) hd
  exact_mod_cast this

theorem isClass {χ : L → ℂ} (hχ : χ ∈ BlocksIrr L) : BlocksIsClassFunction χ :=
  blocksVChar_isClassFunction (AddSubgroup.subset_closure hχ)

theorem St_mem : D.St ∈ BlocksIrr L := by rw [D.irr]; simp
theorem ηp_mem : D.ηp ∈ BlocksIrr L := by rw [D.irr]; simp
theorem ηm_mem : D.ηm ∈ BlocksIrr L := by rw [D.irr]; simp
theorem R_mem {θ : L → ℂ} (hθ : θ ∈ D.RFam) : θ ∈ BlocksIrr L := by rw [D.irr]; simp [hθ]
theorem S_mem {θ : L → ℂ} (hθ : θ ∈ D.SFam) : θ ∈ BlocksIrr L := by rw [D.irr]; simp [hθ]

theorem eq_of_classes {f g : L → ℂ} (hf : BlocksIsClassFunction f) (hg : BlocksIsClassFunction g)
    (h1 : f 1 = g 1) (hU : ∀ x ∈ D.U, x ≠ 1 → f x = g x) (hO : ∀ x ∈ D.O, x ≠ 1 → f x = g x)
    (hE : ∀ x ∈ D.E, x ≠ 1 → f x = g x) : f = g := by
  funext y
  have key : ∀ x, IsConj y x → f x = g x → f y = g y := by
    intro x hyx hfx
    obtain ⟨c, hc⟩ := isConj_iff.mp hyx
    rw [← hf y c, ← hg y c, hc, hfx]
  rcases D.classes y with rfl | ⟨x, hx, hx1, hyx⟩ | ⟨x, hx, hx1, hyx⟩ | ⟨x, hx, hx1, hyx⟩
  · exact h1
  · exact key x hyx (hU x hx hx1)
  · exact key x hyx (hO x hx hx1)
  · exact key x hyx (hE x hx hx1)

omit [Fintype L] in
theorem conj_comp_isClass {f : L → ℂ} (hf : BlocksIsClassFunction f) :
    BlocksIsClassFunction (starRingEnd ℂ ∘ f) := fun g h => by
  simp only [Function.comp_apply, hf g h]

theorem orderOf_dvd_O {x : L} (hx : x ∈ D.O) : orderOf x ∣ Nat.card D.O := by
  have := orderOf_dvd_natCard (⟨x, hx⟩ : D.O)
  rwa [Subgroup.orderOf_mk] at this

theorem orderOf_dvd_E {x : L} (hx : x ∈ D.E) : orderOf x ∣ Nat.card D.E := by
  have := orderOf_dvd_natCard (⟨x, hx⟩ : D.E)
  rwa [Subgroup.orderOf_mk] at this

theorem odd_of_mem_O {x : L} (hx : x ∈ D.O) : Odd (orderOf x) :=
  Odd.of_dvd_nat D.O_odd (D.orderOf_dvd_O hx)

theorem odd_of_mem_U {x : L} (hx : x ∈ D.U) (hx1 : x ≠ 1) : Odd (orderOf x) := by
  rw [D.U_order x hx hx1]
  exact D.p_prime.odd_of_ne_two D.p_ne_two

omit [Fintype L] in
theorem orderOf_conj {x y : L} (h : IsConj y x) : orderOf y = orderOf x := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  rw [← hc, ← MulAut.conj_apply, MulEquiv.orderOf_eq]

omit [Fintype L] in
theorem ne_one_of_conj {x y : L} (h : IsConj y x) (hx : x ≠ 1) : y ≠ 1 := by
  rintro rfl
  exact hx (isConj_one_right.mp h)

theorem E_comm {x y : L} (hx : x ∈ D.E) (hy : y ∈ D.E) : x * y = y * x := by
  have := D.E_cyclic
  have h := (IsCyclic.commGroup (α := D.E)).mul_comm ⟨x, hx⟩ ⟨y, hy⟩
  exact congrArg Subtype.val h

@[expose] noncomputable def s₀ : D.E := (D.E_cyclic.exists_generator).choose

theorem s₀_gen : ∀ x : D.E, x ∈ Subgroup.zpowers D.s₀ :=
  (D.E_cyclic.exists_generator).choose_spec

theorem orderOf_s₀ : orderOf (D.s₀ : L) = Nat.card D.E := by
  rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers D.s₀_gen]

@[expose] noncomputable def m : ℕ := Nat.card D.E / 2

theorem card_E_eq : Nat.card D.E = 2 * D.m := by
  have h1 := D.E_card
  have h2 := D.q_mod
  have h3 := D.e_eq
  unfold m
  omega

theorem m_odd : Odd D.m := by
  have h1 := D.E_card
  have h2 := D.q_mod
  have h3 := D.e_eq
  have h4 := D.card_E_eq
  exact Nat.odd_iff.mpr (by omega)

theorem m_pos : 0 < D.m := by
  obtain ⟨k, hk⟩ := D.m_odd
  omega

theorem mem_E_iff (x : L) : x ∈ D.E ↔ ∃ j : ℤ, (D.s₀ : L) ^ j = x := by
  constructor
  · intro hx
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (D.s₀_gen ⟨x, hx⟩)
    exact ⟨j, by rw [← Subgroup.coe_zpow, hj]⟩
  · rintro ⟨j, rfl⟩
    exact Subgroup.zpow_mem _ D.s₀.2 j

@[expose] noncomputable def J' : L := (D.s₀ : L) ^ D.m

@[expose] noncomputable def So : Subgroup L := Subgroup.zpowers ((D.s₀ : L) ^ 2)

theorem J'_mem : D.J' ∈ D.E := Subgroup.pow_mem _ D.s₀.2 _

theorem So_le_E : D.So ≤ D.E := by
  rw [So, Subgroup.zpowers_le]
  exact Subgroup.pow_mem _ D.s₀.2 _

theorem orderOf_sq_s₀ : orderOf ((D.s₀ : L) ^ 2) = D.m := by
  rw [orderOf_pow' _ two_ne_zero, D.orderOf_s₀, D.card_E_eq, Nat.gcd_mul_right_left]
  · simp

theorem card_So : Nat.card D.So = D.m := by
  rw [So, Nat.card_zpowers, D.orderOf_sq_s₀]

theorem orderOf_J' : orderOf D.J' = 2 := by
  rw [J', orderOf_pow' _ D.m_pos.ne', D.orderOf_s₀, D.card_E_eq, Nat.gcd_mul_left_left]
  simp [D.m_pos.ne']

theorem J'_mul_J' : D.J' * D.J' = 1 := by
  have := pow_orderOf_eq_one D.J'
  rw [D.orderOf_J', sq] at this
  exact this

theorem pow_m_of_mem_So {ρ : L} (hρ : ρ ∈ D.So) : ρ ^ D.m = 1 := by
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hρ
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← D.orderOf_sq_s₀,
    pow_orderOf_eq_one, one_zpow]

theorem odd_of_mem_So {ρ : L} (hρ : ρ ∈ D.So) : Odd (orderOf ρ) :=
  Odd.of_dvd_nat D.m_odd (orderOf_dvd_of_pow_eq_one (D.pow_m_of_mem_So hρ))

theorem sq_mem_So {x : L} (hx : x ∈ D.E) : x ^ 2 ∈ D.So := by
  obtain ⟨j, rfl⟩ := (D.mem_E_iff x).mp hx
  refine Subgroup.mem_zpowers_iff.mpr ⟨j, ?_⟩
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]

theorem exists_sq_of_mem_So {ρ : L} (hρ : ρ ∈ D.So) : ∃ y ∈ D.E, y ^ 2 = ρ := by
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hρ
  refine ⟨(D.s₀ : L) ^ j, Subgroup.zpow_mem _ D.s₀.2 j, ?_⟩
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]

theorem mem_E_cases {x : L} (hx : x ∈ D.E) : x ∈ D.So ∨ ∃ ρ ∈ D.So, x = D.J' * ρ := by
  obtain ⟨j, rfl⟩ := (D.mem_E_iff x).mp hx
  rcases Int.even_or_odd j with ⟨i, hi⟩ | ⟨i, hi⟩
  · left
    refine Subgroup.mem_zpowers_iff.mpr ⟨i, ?_⟩
    rw [← zpow_natCast, ← zpow_mul, hi]
    congr 1
    push_cast
    ring
  · right
    obtain ⟨k, hk⟩ := D.m_odd
    refine ⟨((D.s₀ : L) ^ 2) ^ (i - k), Subgroup.zpow_mem_zpowers _ _, ?_⟩
    rw [J', ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_add, hi, hk]
    congr 1
    push_cast
    ring

theorem J'_not_mem_So : D.J' ∉ D.So := by
  intro h
  have := D.odd_of_mem_So h
  rw [D.orderOf_J'] at this
  exact absurd this (by decide)

theorem J'_mul_ne_one {ρ : L} (hρ : ρ ∈ D.So) : D.J' * ρ ≠ 1 := by
  intro h
  apply D.J'_not_mem_So
  have : D.J' = ρ⁻¹ := eq_inv_of_mul_eq_one_left h
  rw [this]
  exact D.So.inv_mem hρ

theorem mem_So_of_odd {x : L} (hx : x ∈ D.E) (hodd : Odd (orderOf x)) : x ∈ D.So := by
  rcases D.mem_E_cases hx with h | ⟨ρ, hρ, rfl⟩
  · exact h
  · exfalso
    have hdvd : orderOf (D.J' * ρ) ∣ D.m := by
      have h1 := D.orderOf_dvd_E hx
      rw [D.card_E_eq] at h1
      exact (Nat.coprime_two_right.mpr hodd).dvd_of_dvd_mul_left h1
    have hpow : (D.J' * ρ) ^ D.m = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvd
    have hc : Commute D.J' ρ := D.E_comm D.J'_mem (D.So_le_E hρ)
    rw [hc.mul_pow, D.pow_m_of_mem_So hρ, mul_one] at hpow
    obtain ⟨k, hk⟩ := D.m_odd
    rw [hk, pow_succ, pow_mul, sq, D.J'_mul_J', one_pow, one_mul] at hpow
    have := D.orderOf_J'
    rw [hpow, orderOf_one] at this
    omega

theorem eq_J'_of_orderOf_two {x : L} (hx : x ∈ D.E) (h2 : orderOf x = 2) : x = D.J' := by
  rcases D.mem_E_cases hx with h | ⟨ρ, hρ, rfl⟩
  · have := D.odd_of_mem_So h
    rw [h2] at this
    exact absurd this (by decide)
  · have hc : Commute D.J' ρ := D.E_comm D.J'_mem (D.So_le_E hρ)
    have hsq : (D.J' * ρ) ^ 2 = 1 := by rw [← h2, pow_orderOf_eq_one]
    rw [hc.mul_pow, sq D.J', D.J'_mul_J', one_mul] at hsq
    have hρ1 : ρ = 1 := by
      have h1 : orderOf ρ ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
      have h2' := D.odd_of_mem_So hρ
      rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
      · exact orderOf_eq_one_iff.mp h
      · rw [h] at h2'
        exact absurd h2' (by decide)
    rw [hρ1, mul_one]

theorem units_sq_eq_one {u : ℂˣ} (h : u ^ 2 = 1) : u = 1 ∨ u = -1 := by
  have h' : ((u : ℂ) - 1) * ((u : ℂ) + 1) = 0 := by
    have : ((u ^ 2 : ℂˣ) : ℂ) = 1 := by rw [h]; rfl
    push_cast at this
    linear_combination this
  rcases mul_eq_zero.mp h' with h1 | h1
  · left
    apply Units.ext
    simp only [Units.val_one]
    linear_combination h1
  · right
    apply Units.ext
    simp only [Units.val_neg, Units.val_one]
    linear_combination h1

theorem χ₀_sq_apply (x : D.E) : D.χ₀ x ^ 2 = 1 := by
  rw [← MonoidHom.pow_apply, D.χ₀_sq, MonoidHom.one_apply]

theorem χ₀_So {ρ : L} (hρ : ρ ∈ D.So) : D.χ₀ ⟨ρ, D.So_le_E hρ⟩ = 1 := by
  obtain ⟨y, hy, rfl⟩ := D.exists_sq_of_mem_So hρ
  have : (⟨y ^ 2, D.So_le_E hρ⟩ : D.E) = (⟨y, hy⟩ : D.E) ^ 2 := rfl
  rw [this, map_pow, D.χ₀_sq_apply]

theorem χ₀_J' : D.χ₀ ⟨D.J', D.J'_mem⟩ = -1 := by
  have hsq : D.χ₀ ⟨D.J', D.J'_mem⟩ ^ 2 = 1 := D.χ₀_sq_apply _
  rcases units_sq_eq_one hsq with h | h
  · exfalso
    apply D.χ₀_ne
    ext ⟨x, hx⟩
    rcases D.mem_E_cases hx with hxS | ⟨ρ, hρ, rfl⟩
    · rw [D.χ₀_So hxS]; rfl
    · have : (⟨D.J' * ρ, hx⟩ : D.E) = ⟨D.J', D.J'_mem⟩ * ⟨ρ, D.So_le_E hρ⟩ := rfl
      rw [this, map_mul, h, D.χ₀_So hρ, one_mul]
      rfl
  · exact h

end PSLData

end CFSG.Walter.Ward
