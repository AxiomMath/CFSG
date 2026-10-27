module

public import CFSG.SignalizerFunctorTheorem.McBride.Models.UnitaryHeisenberg.Heis3
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.GroupTheory.GroupAction.CardCommute
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Prop

public section

open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.McBride.UnitaryHeisenberg

section Abstract

variable {G : Type*} [Group G]

theorem commute_inv_conj {g O A : G} (h : Commute g (O * A * O⁻¹)) :
    Commute (O⁻¹ * g * O) A := by
  have := h.eq
  show O⁻¹ * g * O * A = A * (O⁻¹ * g * O)
  calc O⁻¹ * g * O * A = O⁻¹ * (g * (O * A * O⁻¹)) * O := by group
    _ = O⁻¹ * ((O * A * O⁻¹) * g) * O := by rw [this]
    _ = A * (O⁻¹ * g * O) := by group

theorem commute_conj_conj {x y : G} (h : Commute x y) (O : G) :
    Commute (O⁻¹ * x * O) (O⁻¹ * y * O) := by
  have := h.eq
  show O⁻¹ * x * O * (O⁻¹ * y * O) = O⁻¹ * y * O * (O⁻¹ * x * O)
  calc O⁻¹ * x * O * (O⁻¹ * y * O) = O⁻¹ * (x * y) * O := by group
    _ = O⁻¹ * (y * x) * O := by rw [this]
    _ = O⁻¹ * y * O * (O⁻¹ * x * O) := by group

structure IsHeisPair (a b ζ : G) : Prop where
  a_pow : a ^ 3 = 1
  b_pow : b ^ 3 = 1
  ζ_pow : ζ ^ 3 = 1
  ζ_ne : ζ ≠ 1
  ζ_central : ζ ∈ Subgroup.center G
  ab : a * b = ζ * (b * a)

namespace IsHeisPair

variable {a b ζ : G} (h : IsHeisPair a b ζ)

include h in
theorem commute_ζ (g : G) : Commute g ζ := Subgroup.mem_center_iff.mp h.ζ_central g

include h in
theorem commute_ζ_pow (g : G) (n : ℕ) : Commute g (ζ ^ n) := (h.commute_ζ g).pow_right n

include h in
theorem commute_of_mem_zpowers {z : G} (hz : z ∈ Subgroup.zpowers ζ) (w : G) : Commute z w := by
  obtain ⟨k, rfl⟩ := hz
  exact ((h.commute_ζ w).symm).zpow_left k

include h in
theorem orderOf_ζ : orderOf ζ = 3 := orderOf_eq_prime h.ζ_pow h.ζ_ne

include h in
theorem ζ_pow_eq_one_iff (n : ℕ) : ζ ^ n = 1 ↔ 3 ∣ n := by
  rw [← h.orderOf_ζ]; exact (orderOf_dvd_iff_pow_eq_one).symm

omit h in
theorem pow_val_eq (g : G) (hg : g ^ 3 = 1) (n : ℕ) (u : ZMod 3) (hu : u.val = n % 3) :
    g ^ u.val = g ^ n := by
  rw [hu, ← pow_eq_pow_mod _ hg]

include h in
theorem a_pow_mul_b : ∀ m : ℕ, a ^ m * b = ζ ^ m * (b * a ^ m) := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    calc a ^ (m + 1) * b = a ^ m * (a * b) := by rw [pow_succ, mul_assoc]
      _ = a ^ m * (ζ * (b * a)) := by rw [h.ab]
      _ = ζ * (a ^ m * b) * a := by
        rw [← mul_assoc, (h.commute_ζ (a ^ m)).eq, mul_assoc, mul_assoc, mul_assoc]
      _ = ζ ^ (m + 1) * (b * a ^ (m + 1)) := by
        rw [ih, pow_succ' ζ m, pow_succ a m]
        simp only [mul_assoc]


include h in
theorem cm (x y : G) (n : ℕ) : x * (ζ ^ n * y) = ζ ^ n * (x * y) := by
  rw [← mul_assoc, (h.commute_ζ_pow x n).eq, mul_assoc]

include h in
theorem cm' (x y : G) (n : ℕ) : x * ζ ^ n * y = x * y * ζ ^ n := by
  rw [mul_assoc, (h.commute_ζ_pow y n).symm.eq, ← mul_assoc]

include h in
theorem a_pow_mul_b_pow (m n : ℕ) : a ^ m * b ^ n = ζ ^ (m * n) * (b ^ n * a ^ m) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc a ^ m * b ^ (n + 1) = (a ^ m * b ^ n) * b := by rw [pow_succ, mul_assoc]
      _ = ζ ^ (m * n) * (b ^ n * (a ^ m * b)) := by rw [ih]; simp only [mul_assoc]
      _ = ζ ^ (m * n) * (b ^ n * (ζ ^ m * (b * a ^ m))) := by rw [h.a_pow_mul_b]
      _ = ζ ^ (m * (n + 1)) * (b ^ (n + 1) * a ^ m) := by
        rw [← mul_assoc (b ^ n), (h.commute_ζ_pow (b ^ n) m).eq, mul_add, mul_one, pow_add,
          pow_succ b n]
        simp only [mul_assoc]

include h in
theorem key (px py qx qy : ℕ) :
    b ^ px * a ^ py * (b ^ qx * a ^ qy) =
      ζ ^ (py * qx) * (b ^ (px + qx) * a ^ (py + qy)) := by
  calc b ^ px * a ^ py * (b ^ qx * a ^ qy) = b ^ px * (a ^ py * b ^ qx) * a ^ qy := by
        simp only [mul_assoc]
    _ = b ^ px * (ζ ^ (py * qx) * (b ^ qx * a ^ py)) * a ^ qy := by rw [h.a_pow_mul_b_pow]
    _ = ζ ^ (py * qx) * (b ^ px * (b ^ qx * a ^ py)) * a ^ qy := by rw [h.cm]
    _ = ζ ^ (py * qx) * (b ^ (px + qx) * a ^ (py + qy)) := by
        rw [pow_add b, pow_add a]; simp only [mul_assoc]

include h in
theorem mul_aux (px py pz qx qy qz : ℕ) :
    (b ^ px * a ^ py * ζ ^ pz) * (b ^ qx * a ^ qy * ζ ^ qz) =
      b ^ (px + qx) * a ^ (py + qy) * ζ ^ (pz + qz + py * qx) := by
  calc (b ^ px * a ^ py * ζ ^ pz) * (b ^ qx * a ^ qy * ζ ^ qz)
      = (b ^ px * a ^ py) * ζ ^ pz * (b ^ qx * a ^ qy) * ζ ^ qz := by simp only [mul_assoc]
    _ = (b ^ px * a ^ py) * (b ^ qx * a ^ qy) * ζ ^ pz * ζ ^ qz := by rw [h.cm']
    _ = ζ ^ (py * qx) * (b ^ (px + qx) * a ^ (py + qy)) * ζ ^ pz * ζ ^ qz := by rw [h.key]
    _ = b ^ (px + qx) * a ^ (py + qy) * ζ ^ (pz + qz + py * qx) := by
        rw [(h.commute_ζ_pow (b ^ (px + qx) * a ^ (py + qy)) (py * qx)).symm.eq]
        simp only [mul_assoc, ← pow_add]
        rw [show py * qx + pz + qz = pz + qz + py * qx by ring]

@[expose] noncomputable def Φ : Heis3 →* G where
  toFun p := b ^ p.x.val * a ^ p.y.val * ζ ^ p.z.val
  map_one' := by simp [Heis3.one_x, Heis3.one_y, Heis3.one_z]
  map_mul' p q := by
    rw [h.mul_aux]
    simp only [Heis3.mul_x, Heis3.mul_y, Heis3.mul_z]
    rw [pow_val_eq b h.b_pow (p.x.val + q.x.val) (p.x + q.x) (ZMod.val_add _ _),
      pow_val_eq a h.a_pow (p.y.val + q.y.val) (p.y + q.y) (ZMod.val_add _ _),
      pow_val_eq ζ h.ζ_pow (p.z.val + q.z.val + p.y.val * q.x.val)
        (p.z + q.z + p.y * q.x)]
    rw [ZMod.val_add, ZMod.val_add, ZMod.val_mul]
    omega

theorem Φ_apply (p : Heis3) : h.Φ p = b ^ p.x.val * a ^ p.y.val * ζ ^ p.z.val := rfl

theorem Φ_a₀ : h.Φ Heis3.a₀ = a := by
  have h1 : (1 : ZMod 3).val = 1 := rfl
  simp [Φ_apply, Heis3.a₀, h1]

theorem Φ_b₀ : h.Φ Heis3.b₀ = b := by
  have h1 : (1 : ZMod 3).val = 1 := rfl
  simp [Φ_apply, Heis3.b₀, h1]

theorem Φ_ζ₀ : h.Φ Heis3.ζ₀ = ζ := by
  have h1 : (1 : ZMod 3).val = 1 := rfl
  simp [Φ_apply, Heis3.ζ₀, h1]

theorem Φ_comm_a (p : Heis3) : ⁅h.Φ p, a⁆ = ζ ^ (-p.x).val := by
  have h1 := congrArg h.Φ (Heis3.commutator_a₀_b₀ p).1
  rwa [map_commutatorElement, Φ_a₀, map_pow, Φ_ζ₀] at h1

theorem Φ_comm_b (p : Heis3) : ⁅h.Φ p, b⁆ = ζ ^ p.y.val := by
  have h1 := congrArg h.Φ (Heis3.commutator_a₀_b₀ p).2
  rwa [map_commutatorElement, Φ_b₀, map_pow, Φ_ζ₀] at h1

include h in
theorem zmod_eq_zero_of_pow_eq_one (u : ZMod 3) (hu : ζ ^ u.val = 1) : u = 0 := by
  have h3 : 3 ∣ u.val := (h.ζ_pow_eq_one_iff _).mp hu
  have : u.val < 3 := ZMod.val_lt u
  have : u.val = 0 := by omega
  exact (ZMod.val_eq_zero u).mp this

theorem Φ_injective : Function.Injective h.Φ := by
  rw [injective_iff_map_eq_one]
  intro p hp
  have h1 := h.Φ_comm_a p
  have h2 := h.Φ_comm_b p
  rw [hp, commutatorElement_one_left] at h1 h2
  have hx : p.x = 0 := by
    have := h.zmod_eq_zero_of_pow_eq_one (-p.x) h1.symm
    exact (by decide : ∀ u : ZMod 3, -u = 0 → u = 0) p.x this
  have hy : p.y = 0 := h.zmod_eq_zero_of_pow_eq_one p.y h2.symm
  have hz : p.z = 0 := by
    apply h.zmod_eq_zero_of_pow_eq_one
    rw [h.Φ_apply, hx, hy] at hp
    simpa using hp
  ext <;> simp [hx, hy, hz]

@[expose] noncomputable def E : Subgroup G := h.Φ.range

theorem card_E : Nat.card h.E = 27 := by
  rw [E, ← Heis3.card_Heis3]
  exact (Nat.card_congr (MonoidHom.ofInjective (h.Φ_injective)).toEquiv).symm

theorem a_mem_E : a ∈ h.E := ⟨Heis3.a₀, h.Φ_a₀⟩

theorem b_mem_E : b ∈ h.E := ⟨Heis3.b₀, h.Φ_b₀⟩

theorem ζ_mem_E : ζ ∈ h.E := ⟨Heis3.ζ₀, h.Φ_ζ₀⟩

include h in
theorem ζ_eq_commutator : ζ = ⁅a, b⁆ := by
  rw [commutatorElement_def, h.ab]; group

theorem E_eq_closure : h.E = Subgroup.closure {a, b} := by
  have ha : a ∈ Subgroup.closure {a, b} := Subgroup.subset_closure (by simp)
  have hb : b ∈ Subgroup.closure {a, b} := Subgroup.subset_closure (by simp)
  have hζ : ζ ∈ Subgroup.closure {a, b} := by
    rw [h.ζ_eq_commutator, commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  apply le_antisymm
  · rintro _ ⟨p, rfl⟩
    rw [h.Φ_apply]
    exact mul_mem (mul_mem (pow_mem hb _) (pow_mem ha _)) (pow_mem hζ _)
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    exacts [h.a_mem_E, h.b_mem_E]

include h in
theorem exists_ζ_pow {z : G} (hz : z ∈ Subgroup.zpowers ζ) : ∃ s : ZMod 3, z = ζ ^ s.val := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  refine ⟨(n : ZMod 3), ?_⟩
  have h3 : ((orderOf ζ : ℕ) : ℤ) = 3 := by rw [h.orderOf_ζ]; rfl
  have h4 : (((n : ZMod 3).val : ℕ) : ℤ) = n % 3 := by
    rw [ZMod.val_intCast]; rfl
  rw [← zpow_natCast, h4, ← h3, zpow_mod_orderOf]

theorem zpowers_ζ_le_E : Subgroup.zpowers ζ ≤ h.E := by
  rw [Subgroup.zpowers_le]; exact h.ζ_mem_E

include h in
theorem card_zpowers_ζ : Nat.card (Subgroup.zpowers ζ) = 3 := by
  rw [Nat.card_zpowers, h.orderOf_ζ]

include h in
theorem commutator_mem_zpowers {x y : G} (hx : x ∈ h.E) (hy : y ∈ h.E) :
    ⁅x, y⁆ ∈ Subgroup.zpowers ζ := by
  obtain ⟨p, rfl⟩ := hx
  obtain ⟨q, rfl⟩ := hy
  obtain ⟨k, hk⟩ := Heis3.commutator_mem p q
  rw [← map_commutatorElement, hk, map_pow, h.Φ_ζ₀]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers ζ) _

include h in
theorem a_not_mem_zpowers : a ∉ Subgroup.zpowers ζ := fun ha => by
  have hab : a * b = b * a := (h.commute_of_mem_zpowers ha b).eq
  rw [h.ab] at hab
  exact h.ζ_ne (by simpa using hab)

include h in
theorem b_not_mem_zpowers : b ∉ Subgroup.zpowers ζ := fun hb => by
  have hab : a * b = b * a := (h.commute_of_mem_zpowers hb a).eq.symm
  rw [h.ab] at hab
  exact h.ζ_ne (by simpa using hab)

section Quotient

variable {Y : Type*} [Group Y] (π : G →* Y)

theorem commute_of_commutator_eq {x g c : G} (hc : ⁅x, c⁆ = ⁅g, c⁆) : Commute (x⁻¹ * g) c := by
  have e : x * c * x⁻¹ = g * c * g⁻¹ := by
    have := hc
    simp only [commutatorElement_def] at this
    exact mul_right_cancel (by simpa [mul_assoc] using this)
  show x⁻¹ * g * c = c * (x⁻¹ * g)
  calc x⁻¹ * g * c = x⁻¹ * (g * c * g⁻¹) * g := by group
    _ = x⁻¹ * (x * c * x⁻¹) * g := by rw [e]
    _ = c * (x⁻¹ * g) := by group

theorem commutator_mem_of_commute {g x : G} (hπ : ∀ g, π g = 1 → g ∈ Subgroup.zpowers ζ)
    (hc : Commute (π g) (π x)) : ⁅g, x⁆ ∈ Subgroup.zpowers ζ := by
  apply hπ
  rw [map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr hc.eq

include h in
theorem centralizer_map_E (hπs : Function.Surjective π)
    (hker : ∀ g : G, π g = 1 ↔ g ∈ Subgroup.zpowers ζ)
    (hCP : ∀ g : G, Commute g a → Commute g b → g ∈ Subgroup.zpowers ζ) :
    Subgroup.centralizer ((h.E.map π : Subgroup Y) : Set Y) = h.E.map π := by
  ext y
  constructor
  · intro hy
    obtain ⟨g, rfl⟩ := hπs y
    have hcom : ∀ x ∈ h.E, ⁅g, x⁆ ∈ Subgroup.zpowers ζ := fun x hx =>
      commutator_mem_of_commute π (fun g hg => (hker g).mp hg)
        (Subgroup.mem_centralizer_iff.mp hy (π x) (Subgroup.mem_map_of_mem _ hx)).symm
    obtain ⟨s, hs⟩ := h.exists_ζ_pow (hcom a h.a_mem_E)
    obtain ⟨t, ht⟩ := h.exists_ζ_pow (hcom b h.b_mem_E)
    obtain ⟨e, he1, he2⟩ := Heis3.exists_comm_eq s t
    have h1 : ⁅h.Φ e, a⁆ = ⁅g, a⁆ := by
      have := congrArg h.Φ he1
      rw [map_commutatorElement, h.Φ_a₀, map_pow, h.Φ_ζ₀] at this
      rw [this, hs]
    have h2 : ⁅h.Φ e, b⁆ = ⁅g, b⁆ := by
      have := congrArg h.Φ he2
      rw [map_commutatorElement, h.Φ_b₀, map_pow, h.Φ_ζ₀] at this
      rw [this, ht]
    have hz := hCP _ (commute_of_commutator_eq h1) (commute_of_commutator_eq h2)
    have hgE : g ∈ h.E := by
      have : g = h.Φ e * ((h.Φ e)⁻¹ * g) := by group
      rw [this]
      exact mul_mem ⟨e, rfl⟩ (h.zpowers_ζ_le_E hz)
    exact ⟨g, hgE, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨x, hx, rfl⟩
    have : ⁅x, g⁆ ∈ Subgroup.zpowers ζ := h.commutator_mem_zpowers hx hg
    have h1 : π ⁅x, g⁆ = 1 := (hker _).mpr this
    rw [map_commutatorElement] at h1
    exact (commutatorElement_eq_one_iff_mul_comm.mp h1)

section Normalizer

variable [Finite G]

include h in
theorem card_normalizer_dvd (hπs : Function.Surjective π)
    (hker : ∀ g : G, π g = 1 ↔ g ∈ Subgroup.zpowers ζ)
    (hCP : ∀ g : G, Commute g a → Commute g b → g ∈ Subgroup.zpowers ζ) :
    Nat.card (Subgroup.normalizer ((h.E.map π : Subgroup Y) : Set Y)) ∣ 216 := by
  classical
  set E := h.E with hE
  set N : Subgroup G := Subgroup.normalizer (E : Set G) with hN
  set M : Subgroup Y := Subgroup.normalizer ((E.map π : Subgroup Y) : Set Y) with hM
  have hcomap : Subgroup.comap π (E.map π) = E := by
    rw [Subgroup.comap_map_eq]
    refine sup_eq_left.mpr fun g hg => h.zpowers_ζ_le_E ((hker g).mp hg)
  have hZN : Subgroup.zpowers ζ ≤ N := h.zpowers_ζ_le_E.trans Subgroup.le_normalizer
  have hA : Nat.card N = 3 * Nat.card M := by
    let f : N →* Y := π.comp N.subtype
    have hrange : f.range = M := by
      ext y
      constructor
      · rintro ⟨n, rfl⟩
        rw [hM, Subgroup.mem_normalizer_iff]
        intro z
        have hfn : f n = π (n : G) := rfl
        rw [hfn]
        constructor
        · rintro ⟨e, he, rfl⟩
          exact ⟨n * e * n⁻¹, ((Subgroup.mem_normalizer_iff.mp n.2) e).mp he, by simp⟩
        · rintro ⟨e', he', he'z⟩
          refine ⟨n⁻¹ * e' * n, ?_, ?_⟩
          · have := (Subgroup.mem_normalizer_iff.mp (inv_mem n.2) e').mp he'
            simpa using this
          · rw [map_mul, map_mul, he'z]
            simp only [Subgroup.coe_inv, map_inv]
            group
      · intro hy
        obtain ⟨g, rfl⟩ := hπs y
        have hgN : g ∈ N := by
          rw [hN, Subgroup.mem_normalizer_iff]
          intro e
          constructor
          · intro he
            have h1 : π (g * e * g⁻¹) ∈ E.map π := by
              rw [map_mul, map_mul, map_inv]
              exact ((Subgroup.mem_normalizer_iff.mp hy) (π e)).mp (Subgroup.mem_map_of_mem _ he)
            rwa [← hcomap]
          · intro he
            have h1 : π (g * e * g⁻¹) ∈ E.map π := Subgroup.mem_map_of_mem _ he
            rw [map_mul, map_mul, map_inv] at h1
            have h2 := ((Subgroup.mem_normalizer_iff.mp hy) (π e)).mpr h1
            rwa [← hcomap]
        exact ⟨⟨g, hgN⟩, rfl⟩
    have hker' : f.ker = (Subgroup.zpowers ζ).subgroupOf N := by
      ext n
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      exact hker n
    have := Subgroup.card_ker_mul_card_range f
    rw [hker', hrange, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZN).toEquiv,
      h.card_zpowers_ζ] at this
    exact this.symm
  have hmem : ∀ (n : N) {x : G}, x ∈ E → (n : G) * x * (n : G)⁻¹ ∈ E := fun n x hx =>
    ((Subgroup.mem_normalizer_iff.mp n.2) x).mp hx
  have hconj : ∀ (n : N) (u v : G), ⁅(n : G) * u * (n : G)⁻¹, (n : G) * v * (n : G)⁻¹⁆ =
      (n : G) * ⁅u, v⁆ * (n : G)⁻¹ := fun n u v => by
    simp only [commutatorElement_def]; group
  have hζn : ∀ n : N, (n : G) * ζ * (n : G)⁻¹ = ζ := fun n => by
    rw [(h.commute_ζ (n : G)).eq]; group
  let X : Type _ := {q : G × G // q.1 ∈ E ∧ q.2 ∈ E ∧ ⁅q.1, q.2⁆ = ζ}
  let act : N → X → X := fun n q => ⟨((n : G) * q.1.1 * (n : G)⁻¹, (n : G) * q.1.2 * (n : G)⁻¹),
    hmem n q.2.1, hmem n q.2.2.1, by
      show ⁅(n : G) * q.1.1 * (n : G)⁻¹, (n : G) * q.1.2 * (n : G)⁻¹⁆ = ζ
      rw [hconj, q.2.2.2, hζn]⟩
  let _inst : MulAction N X :=
    { smul := act
      one_smul := fun q => by
        apply Subtype.ext
        simp [HSMul.hSMul, SMul.smul, act]
      mul_smul := fun m n q => by
        apply Subtype.ext
        simp [HSMul.hSMul, SMul.smul, act, mul_assoc] }
  have hXcard : Nat.card X = 216 := by
    let e : {q : Heis3 × Heis3 // ⁅q.1, q.2⁆ = Heis3.ζ₀} → X := fun q =>
      ⟨(h.Φ q.1.1, h.Φ q.1.2), ⟨q.1.1, rfl⟩, ⟨q.1.2, rfl⟩, by
        show ⁅h.Φ q.1.1, h.Φ q.1.2⁆ = ζ
        rw [← map_commutatorElement, q.2, h.Φ_ζ₀]⟩
    have he : Function.Bijective e := by
      constructor
      · rintro ⟨⟨p, q⟩, hpq⟩ ⟨⟨p', q'⟩, hpq'⟩ hee
        have h1 : h.Φ p = h.Φ p' := congrArg (fun r : X => r.1.1) hee
        have h2 : h.Φ q = h.Φ q' := congrArg (fun r : X => r.1.2) hee
        have h1' := h.Φ_injective h1
        have h2' := h.Φ_injective h2
        subst h1' h2'
        rfl
      · rintro ⟨⟨u, v⟩, hu, hv, hpq⟩
        obtain ⟨p, hp⟩ := hu
        obtain ⟨q, hq⟩ := hv
        have hp' : h.Φ p = u := hp
        have hq' : h.Φ q = v := hq
        have hpq' : ⁅u, v⁆ = ζ := hpq
        have hpq2 : ⁅p, q⁆ = Heis3.ζ₀ := h.Φ_injective (by
          rw [map_commutatorElement, hp', hq', hpq', h.Φ_ζ₀])
        refine ⟨⟨(p, q), hpq2⟩, ?_⟩
        apply Subtype.ext
        exact Prod.ext hp' hq'
    rw [← Nat.card_congr (Equiv.ofBijective e he), Nat.card_eq_fintype_card]
    exact Heis3.card_commutator_eq
  have hstab : ∀ q : X, MulAction.stabilizer N q = (Subgroup.zpowers ζ).subgroupOf N := by
    intro q
    ext n
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    constructor
    · intro hq
      have h1 : (n : G) * q.1.1 * (n : G)⁻¹ = q.1.1 := congrArg (fun r : X => r.1.1) hq
      have h2 : (n : G) * q.1.2 * (n : G)⁻¹ = q.1.2 := congrArg (fun r : X => r.1.2) hq
      have hc1 : Commute (n : G) q.1.1 := by
        show (n : G) * q.1.1 = q.1.1 * (n : G)
        exact mul_inv_eq_iff_eq_mul.mp h1
      have hc2 : Commute (n : G) q.1.2 := by
        show (n : G) * q.1.2 = q.1.2 * (n : G)
        exact mul_inv_eq_iff_eq_mul.mp h2
      obtain ⟨p, hp⟩ := q.2.1
      obtain ⟨r, hr⟩ := q.2.2.1
      have hpr : ⁅p, r⁆ = Heis3.ζ₀ := h.Φ_injective (by
        rw [map_commutatorElement, hp, hr, q.2.2.2, h.Φ_ζ₀])
      obtain ⟨⟨i, j, k, ha⟩, ⟨i', j', k', hb⟩⟩ := Heis3.eq_words_of_commutator_eq p r hpr
      have hmul : ∀ (i j k : ℕ), Commute (n : G) (q.1.1 ^ i * q.1.2 ^ j * ζ ^ k) := fun i j k =>
        ((hc1.pow_right i).mul_right (hc2.pow_right j)).mul_right (h.commute_ζ_pow _ k)
      refine hCP n ?_ ?_
      · have : a = q.1.1 ^ (i : ℕ) * q.1.2 ^ (j : ℕ) * ζ ^ (k : ℕ) := by
          have := congrArg h.Φ ha
          rw [h.Φ_a₀] at this
          rw [this]
          simp [map_mul, map_pow, hp, hr, h.Φ_ζ₀]
        rw [this]
        exact hmul _ _ _
      · have : b = q.1.1 ^ (i' : ℕ) * q.1.2 ^ (j' : ℕ) * ζ ^ (k' : ℕ) := by
          have := congrArg h.Φ hb
          rw [h.Φ_b₀] at this
          rw [this]
          simp [map_mul, map_pow, hp, hr, h.Φ_ζ₀]
        rw [this]
        exact hmul _ _ _
    · intro hn
      apply Subtype.ext
      have h1 : (n : G) * q.1.1 * (n : G)⁻¹ = q.1.1 := by
        rw [(h.commute_of_mem_zpowers hn q.1.1).eq]; group
      have h2 : (n : G) * q.1.2 * (n : G)⁻¹ = q.1.2 := by
        rw [(h.commute_of_mem_zpowers hn q.1.2).eq]; group
      exact Prod.ext h1 h2
  have hs : ∀ q : X, Nat.card (MulAction.stabilizer N q) = 3 := fun q => by
    rw [hstab q, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZN).toEquiv, h.card_zpowers_ζ]
  have : Fintype N := Fintype.ofFinite N
  have : Fintype X := Fintype.ofFinite X
  have : Fintype (MulAction.orbitRel.Quotient N X) := Fintype.ofFinite _
  have : ∀ q : X, Fintype (MulAction.stabilizer N q) := fun q => Fintype.ofFinite _
  have key := MulAction.card_eq_sum_card_group_div_card_stabilizer N X
  have hs' : ∀ q : X, Fintype.card (MulAction.stabilizer N q) = 3 := fun q => by
    rw [← Nat.card_eq_fintype_card]; exact hs q
  simp only [hs'] at key
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card (α := N),
    hA, Nat.mul_div_cancel_left _ (by norm_num : 0 < 3), ← Nat.card_eq_fintype_card (α := X),
    hXcard] at key
  exact Dvd.intro_left _ key.symm

end Normalizer

include h in
theorem commutator_eq_one_of_pow_mem {x y : G} (hxy : ⁅x, y⁆ ∈ Subgroup.zpowers ζ) {m : ℕ}
    (hm : ¬ 3 ∣ m) (hx : x ^ m ∈ Subgroup.zpowers ζ) : ⁅x, y⁆ = 1 := by
  set c := ⁅x, y⁆ with hc
  have hxyx : x * y * x⁻¹ = c * y := by simp [hc, commutatorElement_def, mul_assoc]
  have hpow : ∀ k : ℕ, x ^ k * y * (x ^ k)⁻¹ = c ^ k * y := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc x ^ (k + 1) * y * (x ^ (k + 1))⁻¹ = x * (x ^ k * y * (x ^ k)⁻¹) * x⁻¹ := by
            rw [pow_succ', mul_inv_rev]; simp only [mul_assoc]
        _ = x * (c ^ k * y) * x⁻¹ := by rw [ih]
        _ = (x * c ^ k) * y * x⁻¹ := by simp only [mul_assoc]
        _ = (c ^ k * x) * y * x⁻¹ := by rw [← ((h.commute_of_mem_zpowers hxy x).pow_left k).eq]
        _ = c ^ k * (x * y * x⁻¹) := by simp only [mul_assoc]
        _ = c ^ (k + 1) * y := by rw [hxyx, pow_succ, mul_assoc]
  have h1 : x ^ m * y * (x ^ m)⁻¹ = y := by
    rw [(h.commute_of_mem_zpowers hx y).eq, mul_inv_cancel_right]
  rw [hpow m] at h1
  have h2 : c ^ m = 1 := by simpa using h1
  obtain ⟨s, hs⟩ := h.exists_ζ_pow hxy
  rw [hs, ← pow_mul, h.ζ_pow_eq_one_iff] at h2
  have h3 : 3 ∣ s.val := ((Nat.Prime.dvd_mul Nat.prime_three).mp h2).resolve_right hm
  have h4 : s.val < 3 := ZMod.val_lt s
  have h5 : s.val = 0 := by omega
  rw [hs, h5, pow_zero]

include h in
theorem card_map_E (hker : ∀ g : G, π g = 1 ↔ g ∈ Subgroup.zpowers ζ) :
    Nat.card (h.E.map π) = 9 := by
  let f : h.E →* Y := π.comp h.E.subtype
  have hrange : f.range = h.E.map π := by
    ext y
    constructor
    · rintro ⟨e, rfl⟩
      exact ⟨e, e.2, rfl⟩
    · rintro ⟨e, he, rfl⟩
      exact ⟨⟨e, he⟩, rfl⟩
  have hker' : f.ker = (Subgroup.zpowers ζ).subgroupOf h.E := by
    ext e
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hker e
  have := Subgroup.card_ker_mul_card_range f
  rw [hker', hrange, Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.zpowers_ζ_le_E).toEquiv,
    h.card_zpowers_ζ, h.card_E] at this
  omega

include h in
theorem no_commuting_pair (hπs : Function.Surjective π)
    (hker : ∀ g : G, π g = 1 ↔ g ∈ Subgroup.zpowers ζ)
    (hMU : ∀ x y : G, Commute x a → Commute y b → Commute x y →
      x ∈ Subgroup.zpowers ζ ∨ y ∈ Subgroup.zpowers ζ)
    {x' y' : Y} (hx1 : x' ≠ 1) (hy1 : y' ≠ 1) (hx3 : ¬ 3 ∣ orderOf x')
    (hy3 : ¬ 3 ∣ orderOf y') (hxa : Commute x' (π a)) (hyb : Commute y' (π b))
    (hxy : Commute x' y') : False := by
  obtain ⟨x, rfl⟩ := hπs x'
  obtain ⟨y, rfl⟩ := hπs y'
  have hxm : x ^ orderOf (π x) ∈ Subgroup.zpowers ζ :=
    (hker _).mp (by rw [map_pow, pow_orderOf_eq_one])
  have c1 : Commute x a := by
    have := h.commutator_eq_one_of_pow_mem
      (commutator_mem_of_commute π (fun g hg => (hker g).mp hg) hxa) hx3 hxm
    exact commutatorElement_eq_one_iff_mul_comm.mp this
  have c2 : Commute y b := by
    have hym : y ^ orderOf (π y) ∈ Subgroup.zpowers ζ :=
      (hker _).mp (by rw [map_pow, pow_orderOf_eq_one])
    have := h.commutator_eq_one_of_pow_mem
      (commutator_mem_of_commute π (fun g hg => (hker g).mp hg) hyb) hy3 hym
    exact commutatorElement_eq_one_iff_mul_comm.mp this
  have c3 : Commute x y := by
    have := h.commutator_eq_one_of_pow_mem
      (commutator_mem_of_commute π (fun g hg => (hker g).mp hg) hxy) hx3 hxm
    exact commutatorElement_eq_one_iff_mul_comm.mp this
  rcases hMU x y c1 c2 c3 with hx | hy
  · exact hx1 ((hker x).mpr hx)
  · exact hy1 ((hker y).mpr hy)

end Quotient

end IsHeisPair

namespace IsHeisPair

variable {a b ζ : G}

theorem conj (h : IsHeisPair a b ζ) (g : G) : IsHeisPair (g * a * g⁻¹) (g * b * g⁻¹) ζ where
  a_pow := by rw [conj_pow, h.a_pow]; group
  b_pow := by rw [conj_pow, h.b_pow]; group
  ζ_pow := h.ζ_pow
  ζ_ne := h.ζ_ne
  ζ_central := h.ζ_central
  ab := by
    have hz : g * ζ * g⁻¹ = ζ := by rw [(h.commute_ζ g).eq]; group
    calc g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
      _ = g * (ζ * (b * a)) * g⁻¹ := by rw [h.ab]
      _ = (g * ζ * g⁻¹) * (g * b * g⁻¹ * (g * a * g⁻¹)) := by group
      _ = ζ * (g * b * g⁻¹ * (g * a * g⁻¹)) := by rw [hz]

theorem subgroup (h : IsHeisPair a b ζ) (H : Subgroup G) (ha : a ∈ H) (hb : b ∈ H) (hζ : ζ ∈ H) :
    IsHeisPair (⟨a, ha⟩ : H) ⟨b, hb⟩ ⟨ζ, hζ⟩ where
  a_pow := Subtype.ext h.a_pow
  b_pow := Subtype.ext h.b_pow
  ζ_pow := Subtype.ext h.ζ_pow
  ζ_ne := fun e => h.ζ_ne (congrArg Subtype.val e)
  ζ_central := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.mp h.ζ_central g)
  ab := Subtype.ext h.ab

theorem mem_zpowers_of_inv_conj (h : IsHeisPair a b ζ) (g : G) {x : G}
    (hx : g⁻¹ * x * g ∈ Subgroup.zpowers ζ) : x ∈ Subgroup.zpowers ζ := by
  have h1 := (h.commute_of_mem_zpowers hx g).eq
  have : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
  rw [this, ← h1]
  simpa using hx

theorem commute_conj (h : IsHeisPair a b ζ)
    (hCP : ∀ x : G, Commute x a → Commute x b → x ∈ Subgroup.zpowers ζ) (g : G) :
    ∀ x : G, Commute x (g * a * g⁻¹) → Commute x (g * b * g⁻¹) → x ∈ Subgroup.zpowers ζ :=
  fun _ hxa hxb => h.mem_zpowers_of_inv_conj g (hCP _ (commute_inv_conj hxa) (commute_inv_conj hxb))

theorem mu_conj (h : IsHeisPair a b ζ)
    (hMU : ∀ x y : G, Commute x a → Commute y b → Commute x y →
      x ∈ Subgroup.zpowers ζ ∨ y ∈ Subgroup.zpowers ζ) (g : G) :
    ∀ x y : G, Commute x (g * a * g⁻¹) → Commute y (g * b * g⁻¹) → Commute x y →
      x ∈ Subgroup.zpowers ζ ∨ y ∈ Subgroup.zpowers ζ := by
  intro x y hxa hyb hxy
  rcases hMU _ _ (commute_inv_conj hxa) (commute_inv_conj hyb) (commute_conj_conj hxy g) with
    hx | hy
  · exact Or.inl (h.mem_zpowers_of_inv_conj g hx)
  · exact Or.inr (h.mem_zpowers_of_inv_conj g hy)

theorem E_conj (h : IsHeisPair a b ζ) (g : G) :
    (h.conj g).E = h.E.map (MulAut.conj g).toMonoidHom := by
  rw [(h.conj g).E_eq_closure, h.E_eq_closure, MonoidHom.map_closure]
  congr 1
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.image_insert_eq, Set.image_singleton,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply]

end IsHeisPair

end Abstract

end CFSG.SignalizerFunctorTheorem.McBride.UnitaryHeisenberg
