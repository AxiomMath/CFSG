module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Data.Nat.Totient

public section

namespace CFSG.Quasithin.H13.A6

open Subgroup

variable {G : Type*} [Group G]

@[expose] def cfix (c : G) (X : Subgroup G) : Subgroup G := X ⊓ Subgroup.centralizer {c}

theorem mem_cfix {c : G} {X : Subgroup G} {x : G} :
    x ∈ cfix c X ↔ x ∈ X ∧ c * x = x * c := by
  rw [cfix, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, h2.symm⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, h2.symm⟩

@[expose] noncomputable def nu (c : G) (X : Subgroup G) : ℕ := (cfix c X).relIndex X

theorem card_sup_mul_card_inf' {X N : Subgroup G} (hXN : X ≤ Subgroup.normalizer (N : Set G)) :
    Nat.card (X ⊔ N : Subgroup G) * Nat.card (X ⊓ N : Subgroup G) = Nat.card X * Nat.card N := by
  have : (N.subgroupOf (X ⊔ N)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr
      (sup_le hXN Subgroup.le_normalizer)
  have : (N.subgroupOf X).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using (Subgroup.mem_normalizer_iff.mp (hXN g.2) n).mp hn⟩
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient X N hXN
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf X)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf (X ⊔ N))
  have h3 : Nat.card (N.subgroupOf X) = Nat.card (X ⊓ N : Subgroup G) := by
    rw [← Subgroup.card_map_of_injective X.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  have h4 : Nat.card (N.subgroupOf (X ⊔ N)) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [h2, h4, h1, h3, Nat.card_congr e.toEquiv]
  ring

theorem nu_mul [Finite G] (c : G) {X Y : Subgroup G} (hYX : Y ≤ X)
    (hN : cfix c X ≤ Subgroup.normalizer (Y : Set G)) :
    nu c X = (cfix c X ⊔ Y).relIndex X * nu c Y := by
  unfold nu
  have h1 : cfix c X ≤ cfix c X ⊔ Y := le_sup_left
  have h2 : cfix c X ⊔ Y ≤ X := sup_le inf_le_left hYX
  rw [← Subgroup.relIndex_mul_relIndex (cfix c X) (cfix c X ⊔ Y) X h1 h2, mul_comm]
  congr 1
  have hY : cfix c X ⊓ Y = cfix c Y := by
    ext y
    simp only [cfix, Subgroup.mem_inf]
    constructor
    · rintro ⟨⟨-, hc⟩, hy⟩; exact ⟨hy, hc⟩
    · rintro ⟨hy, hc⟩; exact ⟨⟨hYX hy, hc⟩, hy⟩
  have hp := card_sup_mul_card_inf' hN
  have r1 := Subgroup.relIndex_mul_card (cfix c X) (cfix c X ⊔ Y)
  have r2 := Subgroup.relIndex_mul_card (cfix c Y) Y
  rw [inf_eq_left.2 h1] at r1
  rw [inf_eq_left.2 (show cfix c Y ≤ Y from inf_le_left)] at r2
  rw [hY] at hp
  have hpos : 0 < Nat.card (cfix c X) := Nat.card_pos
  have hpos' : 0 < Nat.card (cfix c Y) := Nat.card_pos
  have key : (cfix c X).relIndex (cfix c X ⊔ Y) * Nat.card (cfix c X) * Nat.card (cfix c Y) =
      (cfix c Y).relIndex Y * Nat.card (cfix c Y) * Nat.card (cfix c X) := by
    rw [r1, r2, hp, mul_comm]
  exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hpos hpos') (by
    calc (cfix c X).relIndex (cfix c X ⊔ Y) * (Nat.card (cfix c X) * Nat.card (cfix c Y))
        = (cfix c X).relIndex (cfix c X ⊔ Y) * Nat.card (cfix c X) * Nat.card (cfix c Y) := by
          ring
      _ = (cfix c Y).relIndex Y * Nat.card (cfix c Y) * Nat.card (cfix c X) := key
      _ = (cfix c Y).relIndex Y * (Nat.card (cfix c X) * Nat.card (cfix c Y)) := by ring)

theorem exists_comm_mul_of_conj_mem [Finite G] {c : G} (hc : c ^ 3 = 1) {N : Subgroup G}
    (hN : ¬ 3 ∣ Nat.card N) (hcN : ∀ n ∈ N, c * n * c⁻¹ ∈ N) {x : G}
    (hx : x⁻¹ * (c * x * c⁻¹) ∈ N) : ∃ n ∈ N, c * (x * n) * c⁻¹ = x * n := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype N := Fintype.ofFinite N
  let f : Function.End ↥N := fun n => ⟨x⁻¹ * (c * (x * n) * c⁻¹), by
    have e : x⁻¹ * (c * (x * n) * c⁻¹) = (x⁻¹ * (c * x * c⁻¹)) * (c * n * c⁻¹) := by group
    rw [e]
    exact N.mul_mem hx (hcN n n.2)⟩
  have hfn : ∀ k : ℕ, ∀ n : ↥N, (((f ^ k) n : ↥N) : G) = x⁻¹ * (c ^ k * (x * n) * (c ^ k)⁻¹) := by
    intro k
    induction k with
    | zero =>
      intro n
      simp only [pow_zero, one_mul, inv_one, mul_one, inv_mul_cancel_left]
      rfl
    | succ k ih =>
      intro n
      have e : (f ^ (k + 1)) n = f ((f ^ k) n) := by rw [pow_succ']; rfl
      rw [e]
      show x⁻¹ * (c * (x * ((f ^ k) n : G)) * c⁻¹) = _
      rw [ih, pow_succ']
      group
  have hf3 : f ^ 3 ^ 1 = 1 := by
    funext n
    apply Subtype.ext
    rw [pow_one, hfn, hc, one_mul, inv_one, mul_one, inv_mul_cancel_left]
    rfl
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 3) (n := 1) hf3
  have hne : Fintype.card (Function.fixedPoints f) ≠ 0 := by
    intro h0
    rw [h0] at hmod
    apply hN
    rw [Nat.card_eq_fintype_card]
    exact Nat.modEq_zero_iff_dvd.mp hmod
  obtain ⟨⟨n, hn⟩⟩ := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hne)
  refine ⟨n, n.2, ?_⟩
  have h := congrArg Subtype.val (show f n = n from hn)
  change x⁻¹ * (c * (x * n) * c⁻¹) = n at h
  calc c * (x * n) * c⁻¹ = x * (x⁻¹ * (c * (x * n) * c⁻¹)) := by rw [mul_inv_cancel_left]
    _ = x * n := by rw [h]

theorem relIndex_cfix_sup_eq_one [Finite G] {c : G} (hc : c ^ 3 = 1) {X Y : Subgroup G}
    (hYX : Y ≤ X) (hY : ¬ 3 ∣ Nat.card Y) (hcY : ∀ y ∈ Y, c * y * c⁻¹ ∈ Y)
    (hcX : ∀ x ∈ X, x⁻¹ * (c * x * c⁻¹) ∈ Y) : (cfix c X ⊔ Y).relIndex X = 1 := by
  rw [Subgroup.relIndex_eq_one]
  intro x hx
  obtain ⟨n, hn, hxn⟩ := exists_comm_mul_of_conj_mem hc hY hcY (hcX x hx)
  have hmem : x * n ∈ cfix c X := by
    refine mem_cfix.2 ⟨X.mul_mem hx (hYX hn), ?_⟩
    calc c * (x * n) = c * (x * n) * c⁻¹ * c := by group
      _ = x * n * c := by rw [hxn]
  have e : x = (x * n) * n⁻¹ := by group
  rw [e]
  exact (cfix c X ⊔ Y).mul_mem (Subgroup.mem_sup_left hmem)
    (Subgroup.mem_sup_right (Y.inv_mem hn))

theorem cfix_sup_eq_of_fpf {c : G} {X Y : Subgroup G}
    (hfp : ∀ x ∈ X, c * x * c⁻¹ * x⁻¹ ∈ Y → x ∈ Y) : cfix c X ⊔ Y = Y := by
  refine sup_eq_right.2 fun x hx => ?_
  obtain ⟨hxX, hxc⟩ := mem_cfix.1 hx
  refine hfp x hxX ?_
  have e : c * x * c⁻¹ * x⁻¹ = 1 := by rw [hxc]; group
  rw [e]
  exact Y.one_mem

theorem nu_eq_card {c : G} {Y : Subgroup G} (h : ∀ y ∈ Y, c * y = y * c → y = 1) :
    nu c Y = Nat.card Y := by
  have hb : cfix c Y = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyY, hyc⟩ := mem_cfix.1 hy
    exact (Subgroup.mem_bot).2 (h y hyY hyc)
  rw [nu, hb, Subgroup.relIndex_bot_left]

theorem nu_conj {g c : G} {X : Subgroup G} (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    nu (g * c * g⁻¹) X = nu c X := by
  have hX : X.map (MulAut.conj g).toMonoidHom = X := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hg x).mp hx
    · intro hy
      refine ⟨g⁻¹ * y * g, ?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) y).mp hy
        simpa using this
      · simp [MulAut.conj_apply, mul_assoc]
  have hC : (cfix c X).map (MulAut.conj g).toMonoidHom = cfix (g * c * g⁻¹) X := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨hxX, hxc⟩ := mem_cfix.1 hx
      refine mem_cfix.2 ⟨(Subgroup.mem_normalizer_iff.mp hg x).mp hxX, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc g * c * g⁻¹ * (g * x * g⁻¹) = g * (c * x) * g⁻¹ := by group
        _ = g * (x * c) * g⁻¹ := by rw [hxc]
        _ = g * x * g⁻¹ * (g * c * g⁻¹) := by group
    · intro hy
      obtain ⟨hyX, hyc⟩ := mem_cfix.1 hy
      refine ⟨g⁻¹ * y * g, mem_cfix.2 ⟨?_, ?_⟩, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) y).mp hyX
        simpa using this
      · calc c * (g⁻¹ * y * g) = g⁻¹ * ((g * c * g⁻¹) * y) * g := by group
          _ = g⁻¹ * (y * (g * c * g⁻¹)) * g := by rw [hyc]
          _ = g⁻¹ * y * g * c := by group
      · simp [MulAut.conj_apply, mul_assoc]
  unfold nu
  rw [← hC]
  conv_rhs => rw [← Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom)
    (cfix c X) X (MulAut.conj g).injective]
  rw [hX]

end CFSG.Quasithin.H13.A6
