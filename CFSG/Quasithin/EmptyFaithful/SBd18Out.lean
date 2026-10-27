module

public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupLinearThreeFour

public section

namespace CFSG.Quasithin.SBd18

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

abbrev OutGrp (K : Type) [Field K] : Type :=
  Kˣ ⋊[LinearThreeFourOuter.inversionAction Kˣ]
    (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))

@[expose] def OutGrp.z₀ (K : Type) [Field K] : OutGrp K :=
  ⟨1, (Multiplicative.ofAdd 1, Multiplicative.ofAdd 1)⟩

@[expose] def fixedSub {P : Type*} [Group P] (α : MulAut P) : Subgroup P :=
  (α.toMonoidHom).eqLocus (MonoidHom.id P)

theorem mem_fixedSub {P : Type*} [Group P] {α : MulAut P} {p : P} : p ∈ fixedSub α ↔ α p = p :=
  Iff.rfl

variable {K : Type} [Field K]

theorem OutGrp.card (h3 : Nat.card Kˣ = 3) : Nat.card (OutGrp K) = 12 := by
  rw [SemidirectProduct.card, h3, Nat.card_prod]
  simp

theorem OutGrp.act_apply (a b : Multiplicative (ZMod 2)) (x : Kˣ) :
    LinearThreeFourOuter.inversionAction Kˣ (a, b) x =
      if Multiplicative.toAdd a + Multiplicative.toAdd b = 0 then x else x⁻¹ :=
  LinearThreeFourOuter.inversionAction_apply (Multiplicative.toAdd a) (Multiplicative.toAdd b) x

theorem units_inv_ne_self (h3 : ∀ x : Kˣ, x ^ 3 = 1) {u : Kˣ} (hu : u ≠ 1) : u⁻¹ ≠ u := by
  intro h
  apply hu
  have h2 : u * u = 1 := by
    calc u * u = u * u⁻¹ := by rw [h]
      _ = 1 := mul_inv_cancel u
  have h3' := h3 u
  calc u = u ^ 3 * (u * u)⁻¹ := by group
    _ = 1 := by rw [h3', h2]; group

theorem units_eq_one_of_inv_eq (h3 : ∀ x : Kˣ, x ^ 3 = 1) {x : Kˣ} (hx : x⁻¹ = x) : x = 1 := by
  have h2 : x * x = 1 := by
    calc x * x = x * x⁻¹ := by rw [hx]
      _ = 1 := mul_inv_cancel x
  calc x = x ^ 3 * (x * x)⁻¹ := by group
    _ = 1 := by rw [h3 x, h2]; group

theorem OutGrp.eq_one_or_eq_central (h3 : ∀ x : Kˣ, x ^ 3 = 1) (hne : ∃ u : Kˣ, u ≠ 1)
    {q : OutGrp K} (hq : ∀ q' : OutGrp K, q' * q = q * q') : q = 1 ∨ q = OutGrp.z₀ K := by
  obtain ⟨u, hu⟩ := hne
  obtain ⟨x, ⟨a, b⟩⟩ := q
  have hc1 := congrArg SemidirectProduct.left (hq (SemidirectProduct.inl u))
  have hc2 := congrArg SemidirectProduct.left
    (hq (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2), Multiplicative.ofAdd (0 : ZMod 2))))
  simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inl, SemidirectProduct.right_inl,
    SemidirectProduct.left_inr, SemidirectProduct.right_inr, map_one, MulAut.one_apply,
    OutGrp.act_apply, one_mul, mul_one, map_one, toAdd_ofAdd] at hc1 hc2
  have h10 : ¬ ((1 : ZMod 2) + 0 = 0) := by decide
  simp only [h10, ↓reduceIte] at hc2
  have hx : x = 1 := units_eq_one_of_inv_eq h3 hc2
  subst hx
  have hab : Multiplicative.toAdd a + Multiplicative.toAdd b = 0 := by
    by_contra hne'
    simp only [hne', ↓reduceIte, mul_comm] at hc1
    exact units_inv_ne_self h3 hu (by simpa using hc1.symm)
  have hcases : ∀ s t : ZMod 2, s + t = 0 → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1) := by decide
  rcases hcases _ _ hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · left
    have ha' : a = 1 := by
      have := congrArg Multiplicative.ofAdd ha
      simpa using this
    have hb' : b = 1 := by
      have := congrArg Multiplicative.ofAdd hb
      simpa using this
    subst ha' hb'
    rfl
  · right
    have ha' : a = Multiplicative.ofAdd 1 := by
      have := congrArg Multiplicative.ofAdd ha
      simpa using this
    have hb' : b = Multiplicative.ofAdd 1 := by
      have := congrArg Multiplicative.ofAdd hb
      simpa using this
    subst ha' hb'
    rfl

theorem OutGrp.eq_central_of_sq_one (h3 : ∀ x : Kˣ, x ^ 3 = 1) {q : OutGrp K}
    (hq : q * q = 1) (hr : q.right = (Multiplicative.ofAdd 1, Multiplicative.ofAdd 1)) :
    q = OutGrp.z₀ K := by
  obtain ⟨x, ⟨a, b⟩⟩ := q
  simp only at hr
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hr
  have hl := congrArg SemidirectProduct.left hq
  simp only [SemidirectProduct.mul_left, OutGrp.act_apply, SemidirectProduct.one_left, toAdd_ofAdd] at hl
  have h11 : ((1 : ZMod 2) + 1 = 0) := by decide
  simp only [h11, ↓reduceIte] at hl
  have hx : x = 1 := by
    have h2 : x * x = 1 := hl
    calc x = x ^ 3 * (x * x)⁻¹ := by group
      _ = 1 := by rw [h3 x, h2]; group
  subst hx
  rfl

abbrev OutClasses (K : Type) [Field K] (Ψ : MulAut (projectiveSL 3 K) →* OutGrp K) : Prop :=
  ∀ α : MulAut (projectiveSL 3 K), α * α = 1 →
    ((Ψ α).right = 1 → α ∈
        (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range) ∧
    ((Ψ α).right = (Multiplicative.ofAdd 1, Multiplicative.ofAdd 0) →
      Nat.card ↥(fixedSub α) = 168 ∧ IsSimpleGroup ↥(fixedSub α)) ∧
    ((Ψ α).right = (Multiplicative.ofAdd 0, Multiplicative.ofAdd 1) →
      Nat.card ↥(fixedSub α) = 60 ∧ IsSimpleGroup ↥(fixedSub α)) ∧
    ((Ψ α).right = (Multiplicative.ofAdd 1, Multiplicative.ofAdd 1) →
      ∃ E : Subgroup (projectiveSL 3 K), Nat.card ↥E = 9 ∧ (∀ e ∈ E, α e = e) ∧
        fixedSub α = Subgroup.normalizer (E : Set (projectiveSL 3 K)) ∧
        ∀ x ∈ E, x ≠ 1 → Subgroup.centralizer ({x} : Set (projectiveSL 3 K)) = E)

abbrev OutConj (K : Type) [Field K] (Ψ : MulAut (projectiveSL 3 K) →* OutGrp K) : Prop :=
  ∀ α α' : MulAut (projectiveSL 3 K), α * α = 1 → α' * α' = 1 → Ψ α = Ψ α' →
    (Ψ α).right ≠ 1 → ∃ p : projectiveSL 3 K, MulAut.conj p * α * (MulAut.conj p)⁻¹ = α'

structure OutFacts (K : Type) [Field K] : Prop where
  out : ∃ Ψ : MulAut (projectiveSL 3 K) →* OutGrp K,
    Function.Surjective Ψ ∧
    Ψ.ker = (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range ∧
    OutClasses K Ψ ∧ OutConj K Ψ

theorem OutGrp.eq_one_of_sq_one_of_right_eq_one (h3 : ∀ x : Kˣ, x ^ 3 = 1) {q : OutGrp K}
    (hq : q * q = 1) (hr : q.right = 1) : q = 1 := by
  obtain ⟨x, ⟨a, b⟩⟩ := q
  simp only at hr
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hr
  have hl := congrArg SemidirectProduct.left hq
  simp only [SemidirectProduct.mul_left, OutGrp.act_apply, SemidirectProduct.one_left] at hl
  have h00 : Multiplicative.toAdd (1 : Multiplicative (ZMod 2)) +
      Multiplicative.toAdd (1 : Multiplicative (ZMod 2)) = 0 := by decide
  simp only [h00, ↓reduceIte] at hl
  have hx : x = 1 := by
    have h2 : x * x = 1 := hl
    calc x = x ^ 3 * (x * x)⁻¹ := by group
      _ = 1 := by rw [h3 x, h2]; group
  subst hx
  rfl

theorem OutGrp.right_cases (h3 : ∀ x : Kˣ, x ^ 3 = 1) {q : OutGrp K} (hq : q * q = 1) (h1 : q ≠ 1)
    (hz : q ≠ OutGrp.z₀ K) :
    q.right = (Multiplicative.ofAdd 1, Multiplicative.ofAdd 0) ∨
      q.right = (Multiplicative.ofAdd 0, Multiplicative.ofAdd 1) := by
  have hall : ∀ a : Multiplicative (ZMod 2), a = Multiplicative.ofAdd 0 ∨ a = Multiplicative.ofAdd 1 := by
    decide
  obtain ⟨x, ⟨a, b⟩⟩ := q
  rcases hall a with rfl | rfl <;> rcases hall b with rfl | rfl
  · exact absurd (OutGrp.eq_one_of_sq_one_of_right_eq_one h3 hq rfl) h1
  · exact Or.inr rfl
  · exact Or.inl rfl
  · exact absurd (OutGrp.eq_central_of_sq_one h3 hq rfl) hz

end CFSG.Quasithin.SBd18
