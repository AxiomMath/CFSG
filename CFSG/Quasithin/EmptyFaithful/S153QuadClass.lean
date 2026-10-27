module

public import CFSG.Quasithin.EmptyFaithful.S1417Quad
public import CFSG.Quasithin.Background.B2FactorizationBridge

public section

namespace CFSG.Quasithin

namespace S153

section Basic

variable {W : Type*} [CommGroup W] {q : W → ZMod 2}

private theorem zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide

private theorem polar_comm (x y : W) : quadPolar q x y = quadPolar q y x := by
  simp only [quadPolar, mul_comm x y]
  ring

private theorem q_mul (x y : W) : q (x * y) = q x + q y + quadPolar q x y := by
  unfold quadPolar
  generalize q (x * y) = a
  generalize q x = b
  generalize q y = c
  revert a b c
  decide

private theorem polar_one_left (hq : IsQuadraticFormOn q) (x : W) : quadPolar q 1 x = 0 := by
  unfold quadPolar
  rw [one_mul, hq.1]
  generalize q x = b
  revert b
  decide

private theorem polar_one_right (hq : IsQuadraticFormOn q) (x : W) : quadPolar q x 1 = 0 := by
  rw [polar_comm]
  exact polar_one_left hq x

private theorem polar_self (hexp : ∀ w : W, w * w = 1) (hq : IsQuadraticFormOn q) (x : W) :
    quadPolar q x x = 0 := by
  unfold quadPolar
  rw [hexp, hq.1]
  generalize q x = b
  revert b
  decide

private theorem polar_mul_left (hq : IsQuadraticFormOn q) (x y z : W) :
    quadPolar q (x * y) z = quadPolar q x z + quadPolar q y z := hq.2.1 x y z

private theorem polar_mul_right (hq : IsQuadraticFormOn q) (x y z : W) :
    quadPolar q x (y * z) = quadPolar q x y + quadPolar q x z := hq.2.2 x y z

private theorem exists_dual (hn : IsNondegQuadratic q) {x : W} (hx : x ≠ 1) : ∃ y, quadPolar q x y = 1 := by
  by_contra hcon
  apply hx
  apply hn
  intro y
  by_contra h0
  exact hcon ⟨y, by
    rcases zmod_two_cases (quadPolar q x y) with h | h
    · exact absurd h h0
    · exact h⟩

private theorem eq_of_mul_eq_one_of_sq (hexp : ∀ w : W, w * w = 1) {x y : W} (h : x * y = 1) : x = y := by
  have h1 : y = x⁻¹ := eq_inv_of_mul_eq_one_right h
  have h2 : x = x⁻¹ := eq_inv_of_mul_eq_one_left (hexp x)
  rw [h1]
  exact h2

private theorem exists_two_ne_one {S : Subgroup W} (hS : Nat.card S = 4) :
    ∃ a ∈ S, ∃ b ∈ S, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  have hfin : Finite S := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype S := Fintype.ofFinite S
  have hc : 2 < (Finset.univ : Finset S).card := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hS]
    omega
  obtain ⟨a, -, b, -, c, -, hab, hac, hbc⟩ := Finset.two_lt_card.mp hc
  by_cases ha : a = 1
  · refine ⟨b, b.2, c, c.2, ?_, ?_, fun h => hbc (Subtype.ext h)⟩
    · intro h
      exact hab (ha.trans (Subtype.ext h).symm)
    · intro h
      exact hac (ha.trans (Subtype.ext h).symm)
  by_cases hb : b = 1
  · refine ⟨a, a.2, c, c.2, ?_, ?_, fun h => hac (Subtype.ext h)⟩
    · intro h
      exact ha (Subtype.ext h)
    · intro h
      exact hbc (hb.trans (Subtype.ext h).symm)
  · refine ⟨a, a.2, b, b.2, ?_, ?_, fun h => hab (Subtype.ext h)⟩
    · intro h
      exact ha (Subtype.ext h)
    · intro h
      exact hb (Subtype.ext h)

private theorem exists_dual_pair (hq : IsQuadraticFormOn q) {e₁ e₂ u₁ u₂ u₃ : W}
    (h1 : quadPolar q e₁ u₁ = 1) (h2 : quadPolar q e₂ u₂ = 1)
    (h3 : quadPolar q e₁ u₃ + quadPolar q e₂ u₃ = 1) :
    ∃ f₁ f₂ : W, quadPolar q e₁ f₁ = 1 ∧ quadPolar q e₂ f₁ = 0 ∧ quadPolar q e₁ f₂ = 0 ∧
      quadPolar q e₂ f₂ = 1 := by
  rcases zmod_two_cases (quadPolar q e₁ u₃) with hp | hp
  · have hr : quadPolar q e₂ u₃ = 1 := by
      rw [hp] at h3
      simpa using h3
    rcases zmod_two_cases (quadPolar q e₂ u₁) with hb | hb
    · exact ⟨u₁, u₃, h1, hb, hp, hr⟩
    · refine ⟨u₁ * u₃, u₃, ?_, ?_, hp, hr⟩
      · rw [polar_mul_right hq, h1, hp]; decide
      · rw [polar_mul_right hq, hb, hr]; decide
  · have hr : quadPolar q e₂ u₃ = 0 := by
      rw [hp] at h3
      have key : ∀ r : ZMod 2, 1 + r = 1 → r = 0 := by decide
      exact key _ h3
    rcases zmod_two_cases (quadPolar q e₁ u₂) with hc | hc
    · exact ⟨u₃, u₂, hp, hr, hc, h2⟩
    · refine ⟨u₃, u₂ * u₃, hp, hr, ?_, ?_⟩
      · rw [polar_mul_right hq, hc, hp]; decide
      · rw [polar_mul_right hq, h2, hr]; decide

private theorem exists_singular_mul (hexp : ∀ w : W, w * w = 1) (hq : IsQuadraticFormOn q) {e f : W}
    (he : q e = 0) (hef : quadPolar q e f = 1) :
    ∃ f' : W, q f' = 0 ∧ quadPolar q e f' = 1 ∧
      ∀ g : W, quadPolar q g e = 0 → quadPolar q g f' = quadPolar q g f := by
  rcases zmod_two_cases (q f) with hf | hf
  · exact ⟨f, hf, hef, fun g _ => rfl⟩
  · refine ⟨f * e, ?_, ?_, fun g hg => ?_⟩
    · rw [q_mul (q := q) f e, hf, he, polar_comm f e, hef]; decide
    · rw [polar_mul_right hq, hef, polar_self hexp hq]; decide
    · rw [polar_mul_right hq, hg]; simp

private theorem exists_orth (hexp : ∀ w : W, w * w = 1) (hq : IsQuadraticFormOn q) {e₁ e₂ f₁ f₂ : W}
    (he₁ : q e₁ = 0) (hf₂ : q f₂ = 0) (h11 : quadPolar q e₁ f₁ = 1)
    (h12 : quadPolar q e₁ f₂ = 0) (h22 : quadPolar q e₂ f₂ = 1) (hb21 : quadPolar q e₂ e₁ = 0) :
    ∃ f₂' : W, q f₂' = 0 ∧ quadPolar q e₁ f₂' = 0 ∧ quadPolar q e₂ f₂' = 1 ∧
      quadPolar q f₁ f₂' = 0 := by
  rcases zmod_two_cases (quadPolar q f₁ f₂) with h | h
  · exact ⟨f₂, hf₂, h12, h22, h⟩
  · refine ⟨f₂ * e₁, ?_, ?_, ?_, ?_⟩
    · rw [q_mul (q := q) f₂ e₁, hf₂, he₁, polar_comm f₂ e₁, h12]; decide
    · rw [polar_mul_right hq, h12, polar_self hexp hq]; decide
    · rw [polar_mul_right hq, h22, hb21]; decide
    · rw [polar_mul_right hq, h, polar_comm f₁ e₁, h11]; decide

private theorem exists_hyperbolic_basis (hexp : ∀ w : W, w * w = 1) (hq : IsQuadraticFormOn q)
    (hn : IsNondegQuadratic q) (hp : IsPlusType q) :
    ∃ e₁ e₂ f₁ f₂ : W, q e₁ = 0 ∧ q e₂ = 0 ∧ q f₁ = 0 ∧ q f₂ = 0 ∧
      quadPolar q e₁ e₂ = 0 ∧ quadPolar q e₁ f₁ = 1 ∧ quadPolar q e₁ f₂ = 0 ∧
      quadPolar q e₂ f₁ = 0 ∧ quadPolar q e₂ f₂ = 1 ∧ quadPolar q f₁ f₂ = 0 := by
  obtain ⟨S, hS4, hS0⟩ := hp
  obtain ⟨e₁, he₁S, e₂, he₂S, he₁1, he₂1, he₁₂⟩ := exists_two_ne_one hS4
  have hq₁ : q e₁ = 0 := hS0 e₁ he₁S
  have hq₂ : q e₂ = 0 := hS0 e₂ he₂S
  have hq₁₂ : q (e₁ * e₂) = 0 := hS0 _ (S.mul_mem he₁S he₂S)
  have hb12 : quadPolar q e₁ e₂ = 0 := by
    have := q_mul (q := q) e₁ e₂
    rw [hq₁₂, hq₁, hq₂] at this
    simpa using this.symm
  have hne : e₁ * e₂ ≠ 1 := fun h => he₁₂ (eq_of_mul_eq_one_of_sq hexp h)
  obtain ⟨u₁, hu₁⟩ := exists_dual hn he₁1
  obtain ⟨u₂, hu₂⟩ := exists_dual hn he₂1
  obtain ⟨u₃, hu₃⟩ := exists_dual hn hne
  have hu₃' : quadPolar q e₁ u₃ + quadPolar q e₂ u₃ = 1 := by
    rw [← polar_mul_left hq]
    exact hu₃
  obtain ⟨f₁, f₂, h11, h21, h12, h22⟩ := exists_dual_pair hq hu₁ hu₂ hu₃'
  have hb21 : quadPolar q e₂ e₁ = 0 := by
    rw [polar_comm e₂ e₁]
    exact hb12
  obtain ⟨f₁', hqf₁, h11', hg₁⟩ := exists_singular_mul hexp hq hq₁ h11
  have h21' : quadPolar q e₂ f₁' = 0 := by
    rw [hg₁ e₂ hb21]
    exact h21
  obtain ⟨f₂', hqf₂, h22', hg₂⟩ := exists_singular_mul hexp hq hq₂ h22
  have h12' : quadPolar q e₁ f₂' = 0 := by
    rw [hg₂ e₁ hb12]
    exact h12
  obtain ⟨f₂'', hq3, h1_, h2_, h3_⟩ := exists_orth hexp hq hq₁ hqf₂ h11' h12' h22' hb21
  exact ⟨e₁, e₂, f₁', f₂'', hq₁, hq₂, hqf₁, hq3, hb12, h11', h1_, h21', h2_, h3_⟩

private theorem exists_anisotropic_basis (hexp : ∀ w : W, w * w = 1) (hq : IsQuadraticFormOn q)
    (hn : IsNondegQuadratic q) (hp : IsPlusType q) :
    ∃ a₁ b₁ a₂ b₂ : W, q a₁ = 1 ∧ q b₁ = 1 ∧ q a₂ = 1 ∧ q b₂ = 1 ∧
      quadPolar q a₁ b₁ = 1 ∧ quadPolar q a₂ b₂ = 1 ∧
      quadPolar q a₁ a₂ = 0 ∧ quadPolar q a₁ b₂ = 0 ∧ quadPolar q b₁ a₂ = 0 ∧
      quadPolar q b₁ b₂ = 0 := by
  obtain ⟨e₁, e₂, f₁, f₂, hq1, hq2, hq3, hq4, h12, h1f1, h1f2, h2f1, h2f2, hf12⟩ :=
    exists_hyperbolic_basis hexp hq hn hp
  have t11 : quadPolar q e₁ e₁ = 0 := polar_self hexp hq e₁
  have tf1f1 : quadPolar q f₁ f₁ = 0 := polar_self hexp hq f₁
  have t22 : quadPolar q e₂ e₂ = 0 := polar_self hexp hq e₂
  have tf2f2 : quadPolar q f₂ f₂ = 0 := polar_self hexp hq f₂
  have tf1e1 : quadPolar q f₁ e₁ = 1 := by rw [polar_comm f₁ e₁]; exact h1f1
  have tf1e2 : quadPolar q f₁ e₂ = 0 := by rw [polar_comm f₁ e₂]; exact h2f1
  have te2e1 : quadPolar q e₂ e₁ = 0 := by rw [polar_comm e₂ e₁]; exact h12
  have tf2e1 : quadPolar q f₂ e₁ = 0 := by rw [polar_comm f₂ e₁]; exact h1f2
  have tf2f1 : quadPolar q f₂ f₁ = 0 := by rw [polar_comm f₂ f₁]; exact hf12
  have tf2e2 : quadPolar q f₂ e₂ = 1 := by rw [polar_comm f₂ e₂]; exact h2f2
  refine ⟨e₁ * f₁, e₁ * (e₂ * f₂), e₂ * f₂, e₁ * f₁ * e₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [q_mul (q := q), polar_mul_left hq, polar_mul_right hq, hq1, hq2, hq3, hq4, h12,
      h1f1, h1f2, h2f1, h2f2, hf12, t11, tf1f1, t22, tf2f2, tf1e1, tf1e2, te2e1, tf2e1, tf2f1,
      tf2e2] <;> decide

end Basic

section Klein

variable {W : Type*} [CommGroup W]

private def kleinOf (a b : W) (ha : a * a = 1) (hb : b * b = 1) : Subgroup W where
  carrier := {w | w = 1 ∨ w = a ∨ w = b ∨ w = a * b}
  one_mem' := Or.inl rfl
  mul_mem' := by
    intro x y hx hy
    have h1 : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
    have h2 : b * (a * b) = a := by rw [mul_comm a b, ← mul_assoc, hb, one_mul]
    have h3 : (a * b) * a = b := by rw [mul_comm a b, mul_assoc, ha, mul_one]
    have h4 : (a * b) * b = a := by rw [mul_assoc, hb, mul_one]
    have h5 : (a * b) * (a * b) = 1 := by rw [mul_mul_mul_comm, ha, hb, one_mul]
    have h6 : b * a = a * b := mul_comm b a
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      simp [ha, hb, h1, h2, h3, h4, h5, h6]
  inv_mem' := by
    intro x hx
    have h5 : (a * b) * (a * b) = 1 := by rw [mul_mul_mul_comm, ha, hb, one_mul]
    rcases hx with rfl | rfl | rfl | rfl
    · simp
    · simp [inv_eq_of_mul_eq_one_right ha]
    · simp [inv_eq_of_mul_eq_one_right hb]
    · simp [inv_eq_of_mul_eq_one_right h5]

private theorem mem_kleinOf {a b : W} {ha : a * a = 1} {hb : b * b = 1} {w : W} :
    w ∈ kleinOf a b ha hb ↔ w = 1 ∨ w = a ∨ w = b ∨ w = a * b := Iff.rfl

private theorem klein_mul_ne_one {a b : W} (ha : a * a = 1) (hab : a ≠ b) : a * b ≠ 1 := by
  intro h
  apply hab
  have h1 : b = a⁻¹ := eq_inv_of_mul_eq_one_right h
  rw [h1]
  exact (inv_eq_of_mul_eq_one_right ha).symm

private theorem card_kleinOf {a b : W} (ha : a * a = 1) (hb : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hab : a ≠ b) : Nat.card (kleinOf a b ha hb) = 4 := by
  classical
  have hab1 : a * b ≠ 1 := klein_mul_ne_one ha hab
  have hab2 : a * b ≠ a := by
    intro h
    apply hb1
    exact mul_left_cancel (h.trans (mul_one a).symm)
  have hab3 : a * b ≠ b := by
    intro h
    apply ha1
    exact mul_right_cancel (h.trans (one_mul b).symm)
  have hset : ((kleinOf a b ha hb : Subgroup W) : Set W) = ↑({1, a, b, a * b} : Finset W) := by
    ext w
    simp only [SetLike.mem_coe, mem_kleinOf, Finset.coe_insert, Finset.coe_singleton,
      Set.mem_insert_iff, Set.mem_singleton_iff]
  have h1 : Nat.card (kleinOf a b ha hb) = (((kleinOf a b ha hb : Subgroup W) : Set W)).ncard :=
    Nat.card_coe_set_eq _
  rw [h1, hset, Set.ncard_coe_finset]
  simp [Finset.card_insert_of_notMem, ha1.symm, hb1.symm, hab1.symm, hab, hab2.symm, hab3.symm]

private theorem isKleinFour_of {G : Type*} [Group G] (hcard : Nat.card G = 4) (hsq : ∀ g : G, g * g = 1) :
    IsKleinFour G := by
  refine ⟨hcard, ?_⟩
  have hfin : Finite G := Nat.finite_of_card_ne_zero (by omega)
  have hnt : Nontrivial G := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  rw [Monoid.exponent_eq_prime_iff Nat.prime_two]
  intro g hg
  exact orderOf_eq_prime (by rw [pow_two]; exact hsq g) hg

end Klein

section Main

variable {W : Type*} [CommGroup W] {q : W → ZMod 2}

theorem exists_decomposition_of_plusType (hexp : ∀ w : W, w * w = 1) (hcard : Nat.card W = 16)
    (hq : IsQuadraticFormOn q) (hn : IsNondegQuadratic q) (hp : IsPlusType q) :
    ∃ (U₁ U₂ : Subgroup W) (hinf : U₁ ⊓ U₂ = ⊥) (hsup : U₁ ⊔ U₂ = ⊤)
      (φ₁ : ↥U₁ ≃* S1417.F2sq) (φ₂ : ↥U₂ ≃* S1417.F2sq),
      ∀ w : W, q w = S1417.quadOf hinf hsup φ₁ φ₂ w := by
  classical
  have hfin : Finite W := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨a₁, b₁, a₂, b₂, hqa₁, hqb₁, hqa₂, hqb₂, hab₁, hab₂, h1, h2, h3, h4⟩ :=
    exists_anisotropic_basis hexp hq hn hp
  have hq1 : q 1 = 0 := hq.1
  have ha₁ : a₁ ≠ 1 := fun h => by rw [h, hq1] at hqa₁; exact zero_ne_one hqa₁
  have hb₁ : b₁ ≠ 1 := fun h => by rw [h, hq1] at hqb₁; exact zero_ne_one hqb₁
  have ha₂ : a₂ ≠ 1 := fun h => by rw [h, hq1] at hqa₂; exact zero_ne_one hqa₂
  have hb₂ : b₂ ≠ 1 := fun h => by rw [h, hq1] at hqb₂; exact zero_ne_one hqb₂
  have hne₁ : a₁ ≠ b₁ := fun h => by
    rw [h, polar_self hexp hq] at hab₁; exact zero_ne_one hab₁
  have hne₂ : a₂ ≠ b₂ := fun h => by
    rw [h, polar_self hexp hq] at hab₂; exact zero_ne_one hab₂
  let U₁ : Subgroup W := kleinOf a₁ b₁ (hexp a₁) (hexp b₁)
  let U₂ : Subgroup W := kleinOf a₂ b₂ (hexp a₂) (hexp b₂)
  have hU₁ : Nat.card U₁ = 4 := card_kleinOf (hexp a₁) (hexp b₁) ha₁ hb₁ hne₁
  have hU₂ : Nat.card U₂ = 4 := card_kleinOf (hexp a₂) (hexp b₂) ha₂ hb₂ hne₂
  have hm₁ : a₁ * b₁ ≠ 1 := klein_mul_ne_one (hexp a₁) hne₁
  have hm₂ : a₂ * b₂ ≠ 1 := klein_mul_ne_one (hexp a₂) hne₂
  have hqU₁ : ∀ y ∈ U₁, q y = if y = 1 then 0 else 1 := by
    intro y hy
    rcases hy with rfl | rfl | rfl | rfl
    · simp [hq1]
    · simp [ha₁, hqa₁]
    · simp [hb₁, hqb₁]
    · rw [q_mul (q := q) a₁ b₁, hqa₁, hqb₁, hab₁]
      simp [hm₁]
      decide
  have hqU₂ : ∀ y ∈ U₂, q y = if y = 1 then 0 else 1 := by
    intro y hy
    rcases hy with rfl | rfl | rfl | rfl
    · simp [hq1]
    · simp [ha₂, hqa₂]
    · simp [hb₂, hqb₂]
    · rw [q_mul (q := q) a₂ b₂, hqa₂, hqb₂, hab₂]
      simp [hm₂]
      decide
  have horth : ∀ y ∈ U₁, ∀ z ∈ U₂, quadPolar q y z = 0 := by
    intro y hy z hz
    rcases hy with rfl | rfl | rfl | rfl
    · exact polar_one_left hq z
    all_goals
      rcases hz with rfl | rfl | rfl | rfl
      all_goals first
        | exact polar_one_right hq _
        | (simp only [polar_mul_left hq, polar_mul_right hq, h1, h2, h3, h4]; try decide)
  have hnd₁ : ∀ y ∈ U₁, y ≠ 1 → ∃ y' ∈ U₁, quadPolar q y y' = 1 := by
    intro y hy hy1
    rcases hy with h | h | h | h
    · exact absurd h hy1
    · exact ⟨b₁, Or.inr (Or.inr (Or.inl rfl)), by rw [h]; exact hab₁⟩
    · exact ⟨a₁, Or.inr (Or.inl rfl), by rw [h, polar_comm b₁ a₁]; exact hab₁⟩
    · refine ⟨a₁, Or.inr (Or.inl rfl), ?_⟩
      rw [h, polar_mul_left hq, polar_self hexp hq, polar_comm b₁ a₁, hab₁]
      decide
  have hinf : U₁ ⊓ U₂ = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [Subgroup.mem_bot]
    by_contra hw1
    obtain ⟨y', hy', hβ⟩ := hnd₁ w hw.1 hw1
    have := horth y' hy' w hw.2
    rw [polar_comm y' w, hβ] at this
    exact one_ne_zero this
  have hsup : U₁ ⊔ U₂ = ⊤ := by
    have h := B2F.card_sup_mul_card_inf_of_commute (A := U₁) (B := U₂)
      (fun a _ b _ => mul_comm a b)
    rw [hinf, Subgroup.card_bot, mul_one, hU₁, hU₂] at h
    exact Subgroup.eq_top_of_card_eq _ (by rw [h, hcard])
  have k1 : IsKleinFour U₁ := isKleinFour_of hU₁ (fun g => Subtype.ext (hexp g))
  have k2 : IsKleinFour U₂ := isKleinFour_of hU₂ (fun g => Subtype.ext (hexp g))
  have kF : IsKleinFour S1417.F2sq := isKleinFour_of S1417.card_F2sq (by decide)
  obtain ⟨φ₁⟩ := IsKleinFour.nonempty_mulEquiv (G₁ := U₁) (G₂ := S1417.F2sq)
  obtain ⟨φ₂⟩ := IsKleinFour.nonempty_mulEquiv (G₁ := U₂) (G₂ := S1417.F2sq)
  refine ⟨U₁, U₂, hinf, hsup, φ₁, φ₂, fun w => ?_⟩
  obtain ⟨y, hy, z, hz, rfl⟩ := S1417.exists_mul_eq hsup w
  rw [S1417.quadOf_mul hinf hsup φ₁ φ₂ hy hz, q_mul (q := q) y z, hqU₁ y hy, hqU₂ z hz,
    horth y hy z hz, add_zero]

end Main

end S153

end CFSG.Quasithin
