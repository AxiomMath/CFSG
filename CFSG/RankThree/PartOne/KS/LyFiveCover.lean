module

public import CFSG.RankThree.PartOne.KS.LyFiveGeneric
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.RankThree.PartOne.LyFive

open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

@[expose] def centralizerConj' {G : Type*} [Group G] (x g : G) :
    centralizer ({x * g * x⁻¹} : Set G) ≃* centralizer ({g} : Set G) where
  toFun y := ⟨x⁻¹ * (y : G) * x, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := Subgroup.mem_centralizer_singleton_iff.1 y.2
    calc x⁻¹ * (y : G) * x * g = x⁻¹ * ((y : G) * (x * g * x⁻¹)) * x := by group
      _ = x⁻¹ * ((x * g * x⁻¹) * (y : G)) * x := by rw [h]
      _ = g * (x⁻¹ * (y : G) * x) := by group⟩
  invFun y := ⟨x * (y : G) * x⁻¹, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := Subgroup.mem_centralizer_singleton_iff.1 y.2
    calc x * (y : G) * x⁻¹ * (x * g * x⁻¹) = x * ((y : G) * g) * x⁻¹ := by group
      _ = x * (g * (y : G)) * x⁻¹ := by rw [h]
      _ = x * g * x⁻¹ * (x * (y : G) * x⁻¹) := by group⟩
  left_inv y := Subtype.ext (by simp only; group)
  right_inv y := Subtype.ext (by simp only; group)
  map_mul' y w := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

section Cover

variable {T : Type*} [Group T] {x y : T}

theorem orderOf_eq_five_of_conj_pow {w r : T} (hw : orderOf w = 5) (hr5 : r ^ 5 = 1) {e : ℕ}
    {g : T} (hg : g * w * g⁻¹ = r ^ e) : orderOf r = 5 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  refine orderOf_eq_prime hr5 ?_
  intro h1
  rw [h1, one_pow] at hg
  have : w = 1 := by
    calc w = g⁻¹ * (g * w * g⁻¹) * g := by group
      _ = 1 := by rw [hg]; group
  rw [this, orderOf_one] at hw
  omega

theorem fiveCore_of_cover
    (hcov : ∀ w : T, orderOf w = 5 → ∃ g : T, ∃ r ∈ ({x, y} : Set T), ∃ e : ℕ, 1 ≤ e ∧ e ≤ 4 ∧
      g * w * g⁻¹ = r ^ e)
    (hx5 : x ^ 5 = 1) (hy5 : y ^ 5 = 1) (hx : FiveCoreAt' x) (hy : FiveCoreAt' y) :
    FiveCore T := by
  intro w hw
  obtain ⟨g, r, hr, e, he1, he4, hg⟩ := hcov w hw
  have hr' : r = x ∨ r = y := by simpa using hr
  have hr5 : r ^ 5 = 1 := by rcases hr' with rfl | rfl <;> assumption
  have hrord := orderOf_eq_five_of_conj_pow hw hr5 hg
  have hrc : FiveCoreAt' r := by rcases hr' with rfl | rfl <;> assumption
  exact fiveCoreAt_of_fiveCoreAt' (fiveCoreAt'_of_conj_pow hrord (k := e) (by omega) (by omega) g hg hrc)

theorem card_centralizer_of_cover
    (hcov : ∀ w : T, orderOf w = 5 → ∃ g : T, ∃ r ∈ ({x, y} : Set T), ∃ e : ℕ, 1 ≤ e ∧ e ≤ 4 ∧
      g * w * g⁻¹ = r ^ e)
    (hx5 : x ^ 5 = 1) (hy5 : y ^ 5 = 1) {w : T} (hw : orderOf w = 5) :
    Nat.card (centralizer ({w} : Set T)) = Nat.card (centralizer ({x} : Set T)) ∨
      Nat.card (centralizer ({w} : Set T)) = Nat.card (centralizer ({y} : Set T)) := by
  obtain ⟨g, r, hr, e, he1, he4, hg⟩ := hcov w hw
  have hr' : r = x ∨ r = y := by simpa using hr
  have hr5 : r ^ 5 = 1 := by rcases hr' with rfl | rfl <;> assumption
  have hrord := orderOf_eq_five_of_conj_pow hw hr5 hg
  have hcard : Nat.card (centralizer ({w} : Set T)) = Nat.card (centralizer ({r} : Set T)) := by
    have h1 : Nat.card (centralizer ({g * w * g⁻¹} : Set T)) =
        Nat.card (centralizer ({w} : Set T)) := Nat.card_congr (centralizerConj' g w).toEquiv
    rw [hg, centralizer_pow_eq hrord (k := e) (by omega) (by omega)] at h1
    exact h1.symm
  rcases hr' with rfl | rfl
  · exact Or.inl hcard
  · exact Or.inr hcard

theorem exists_involution_of_cover
    (hcov : ∀ w : T, orderOf w = 5 → ∃ g : T, ∃ r ∈ ({x, y} : Set T), ∃ e : ℕ, 1 ≤ e ∧ e ≤ 4 ∧
      g * w * g⁻¹ = r ^ e)
    (hx5 : x ^ 5 = 1) (hy5 : y ^ 5 = 1)
    (hxe : ∃ u : T, orderOf u = 2 ∧ u * x = x * u) (hye : ∃ u : T, orderOf u = 2 ∧ u * y = y * u)
    {w : T} (hw : orderOf w = 5) : ∃ u : T, orderOf u = 2 ∧ u * w = w * u := by
  obtain ⟨g, r, hr, e, he1, he4, hg⟩ := hcov w hw
  have hr' : r = x ∨ r = y := by simpa using hr
  obtain ⟨u, hu2, hur⟩ : ∃ u : T, orderOf u = 2 ∧ u * r = r * u := by
    rcases hr' with rfl | rfl
    · exact hxe
    · exact hye
  refine ⟨g⁻¹ * u * g, ?_, ?_⟩
  · have := (MulAut.conj g⁻¹ : MulAut T).orderOf_eq u
    rw [MulAut.conj_apply, inv_inv] at this
    rw [this, hu2]
  · have hure : u * r ^ e = r ^ e * u := (Commute.pow_right (show Commute u r from hur) e).eq
    have hw' : w = g⁻¹ * r ^ e * g := by
      rw [← hg]; group
    rw [hw']
    calc g⁻¹ * u * g * (g⁻¹ * r ^ e * g) = g⁻¹ * (u * r ^ e) * g := by group
      _ = g⁻¹ * (r ^ e * u) * g := by rw [hure]
      _ = g⁻¹ * r ^ e * g * (g⁻¹ * u * g) := by group

theorem exists_involution_of_even_card [Finite T] {r : T}
    (h : 2 ∣ Nat.card (centralizer ({r} : Set T))) : ∃ u : T, orderOf u = 2 ∧ u * r = r * u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := centralizer ({r} : Set T)) 2 h
  refine ⟨(u : T), ?_, ?_⟩
  · rw [Subgroup.orderOf_coe]; exact hu
  · exact Subgroup.mem_centralizer_singleton_iff.1 u.2

end Cover

section Transfer

variable {T J : Type*} [Group T] [Group J]

theorem orderOf_conj_inv {G : Type*} [Group G] (g w : G) : orderOf (g⁻¹ * w * g) = orderOf w := by
  have h1 : g⁻¹ * w * g = (MulAut.conj g⁻¹ : MulAut G) w := by
    rw [MulAut.conj_apply, inv_inv]
  rw [h1, MulEquiv.orderOf_eq]

theorem hpt_of_equiv (e : T ≃* J)
    (h : ∀ w : J, orderOf w = 5 → ∀ f : J → J, (∀ x y, f (x * y) = f x * f y) →
      (∀ x, f (f x) = x) → (∀ g ∈ centralizer ({w} : Set J), f g = g) →
      ∃ j : J, ∀ x, f x = j * x * j⁻¹) :
    ∀ w : T, orderOf w = 5 → ∀ v : MulAut T, orderOf v = 2 →
      (∀ g ∈ centralizer ({w} : Set T), v g = g) →
      v ∈ (MulAut.conj : T →* MulAut T).range := by
  intro w hw v hv hfix
  have hvv : v * v = 1 := by rw [← pow_two, ← hv]; exact pow_orderOf_eq_one v
  have hvv' : ∀ t : T, v (v t) = t := fun t => by
    have := congrArg (fun f : MulAut T => f t) hvv
    simpa using this
  have hw' : orderOf (e w) = 5 := by rw [MulEquiv.orderOf_eq, hw]
  obtain ⟨j, hj⟩ := h (e w) hw' (fun x => e (v (e.symm x)))
    (fun x y => by simp only [map_mul])
    (fun x => by simp only [e.symm_apply_apply, hvv', e.apply_symm_apply])
    (fun g hg => by
      have ht : e.symm g ∈ centralizer ({w} : Set T) := by
        rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
        apply e.injective
        rw [map_mul, map_mul, e.apply_symm_apply]
        exact hg
      simp only [hfix _ ht, e.apply_symm_apply])
  refine ⟨e.symm j, ?_⟩
  ext t
  have h1 := hj (e t)
  simp only [e.symm_apply_apply] at h1
  have h3 : v t = e.symm j * t * (e.symm j)⁻¹ := by
    apply e.injective
    rw [map_mul, map_mul, map_inv, e.apply_symm_apply, ← h1]
  rw [MulAut.conj_apply]
  exact h3.symm

theorem orderOf_equiv_eq_five (e : T ≃* J) {b : T} (hb : orderOf b = 5) : orderOf (e b) = 5 := by
  rw [MulEquiv.orderOf_eq, hb]

theorem card_dvd_centralizer_of_equiv (e : T ≃* J) (b : T) (K : Subgroup T)
    (hK : ∀ x ∈ K, b * x = x * b) : Nat.card K ∣ Nat.card (centralizer ({e b} : Set J)) := by
  have hKle : K.map e.toMonoidHom ≤ centralizer ({e b} : Set J) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom, ← map_mul, ← map_mul,
      hK x hx]
  have h1 := Subgroup.card_dvd_of_le hKle
  rwa [Subgroup.card_map_of_injective e.injective] at h1

theorem fiveCoreAt'_of_equiv (e : T ≃* J) (h : FiveCore J) {w : T} (hw : orderOf w = 5) :
    FiveCoreAt' w := by
  have h1 := fiveCoreAt'_of_fiveCoreAt (h (e w) (by rw [MulEquiv.orderOf_eq, hw]))
  have h2 := fiveCoreAt'_map e.symm h1
  simpa using h2

theorem exists_conj_of_pow_five [Finite T] (hout : Nat.card (Outer T) ≤ 4) {α : MulAut T}
    (hα : α ^ 5 = 1) :
    ∃ b : T, MulAut.conj b = α := by
  have hfin : Finite (MulAut T) := Finite.of_injective _ (DFunLike.coe_injective (F := MulAut T))
  set q := QuotientGroup.mk' (inner T) α
  have hqp : orderOf q ∣ 5 := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hα, map_one])
  have hqle : orderOf q ≤ 4 :=
    (Nat.le_of_dvd Nat.card_pos (orderOf_dvd_natCard q)).trans hout
  have hq1 : orderOf q = 1 := by
    rcases (Nat.dvd_prime Nat.prime_five).mp hqp with h | h
    · exact h
    · omega
  have hmem : α ∈ inner T :=
    (QuotientGroup.eq_one_iff α).mp (orderOf_eq_one_iff.mp hq1)
  obtain ⟨b, hb⟩ := hmem
  exact ⟨b, hb⟩

end Transfer

section Twist

theorem eq_one_of_conj_eq_mul {G : Type*} [Group G] {z w u : G} (hz2 : z ^ 2 = 1)
    (hzw : Commute z w) (hw5 : w ^ 5 = 1) (h : u * w * u⁻¹ = z * w) : z = 1 := by
  have h5 : (u * w * u⁻¹) ^ 5 = 1 := by rw [conj_pow, hw5, mul_one, mul_inv_cancel]
  rw [h, hzw.mul_pow, hw5, mul_one] at h5
  calc z = z ^ 5 * ((z ^ 2)⁻¹) ^ 2 := by group
    _ = 1 := by rw [h5, hz2]; simp

theorem exists_twist {G : Type*} [Group G] (g : G) {v : MulAut G} (hv : v * v = 1) :
    ∃ α : MulAut G, (∀ x, α x = g⁻¹ * v (g * x * g⁻¹) * g) ∧ α * α = 1 ∧
      ∀ x : G, MulAut.conj x = α → MulAut.conj (g * x * g⁻¹) = v := by
  refine ⟨(MulAut.conj g)⁻¹ * v * MulAut.conj g, ?_, ?_, ?_⟩
  · intro x
    simp [MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_def]
  · calc (MulAut.conj g)⁻¹ * v * MulAut.conj g * ((MulAut.conj g)⁻¹ * v * MulAut.conj g)
        = (MulAut.conj g)⁻¹ * (v * v) * MulAut.conj g := by group
      _ = 1 := by rw [hv]; group
  · intro x hx
    rw [map_mul, map_mul, hx, map_inv]
    group

end Twist

end CFSG.RankThree.PartOne.LyFive
