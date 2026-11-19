module

public import CFSG.Quasithin.Recognition.Kleidman.OrdinaryProofs.F3Invariant
public import Mathlib.GroupTheory.PGroup
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

open Module

namespace CFSG.Quasithin.Kleidman.F204.O2Alg

set_option linter.unusedSectionVars false

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem add_self_eq_zero (v : W) : v + v = 0 := by
  rw [← two_smul (ZMod 2) v]
  have : (2 : ZMod 2) = 0 := rfl
  simp [this]

theorem neg_eq_self' (v : W) : -v = v := by
  have := add_self_eq_zero v
  exact neg_eq_of_add_eq_zero_right this

theorem sub_eq_add' (v w : W) : v - w = v + w := by
  rw [sub_eq_add_neg, neg_eq_self']

theorem two_nsmul_zero (a : W) : (2 : ℕ) • a = 0 := by
  rw [two_nsmul]; exact add_self_eq_zero a

theorem eq_of_add_eq_zero2 {v w : W} (h : v + w = 0) : v = w := by
  have := neg_eq_of_add_eq_zero_left h
  rw [neg_eq_self'] at this
  exact this.symm

section Basic
variable (x t : W ≃ₗ[ZMod 2] W)

theorem pow_succ_apply (n : ℕ) (w : W) : (x ^ (n + 1)) w = x ((x ^ n) w) := by
  rw [pow_succ']
  rfl

theorem x_sq_fix (hx : x ^ 5 = 1) (w : W) (h : x (x w) = w) : x w = w := by
  have h5 : (x ^ 5) w = w := by rw [hx]; rfl
  have e : (x ^ 5) w = x (x (x (x (x w)))) := by
    simp [pow_succ_apply]
  rw [e] at h5
  rw [h, h] at h5
  exact h5

end Basic

section Four
variable [Module.Finite (ZMod 2) W]

theorem four_dvd_finrank (x : W ≃ₗ[ZMod 2] W) (hx : x ^ 5 = 1)
    (hfpf : ∀ w, x w = w → w = 0) : 4 ∣ finrank (ZMod 2) W := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : Finite W := Module.finite_of_finite (ZMod 2)
  let G : Subgroup (W ≃ₗ[ZMod 2] W) := Subgroup.zpowers x
  have hG : IsPGroup 5 G := by
    rintro ⟨g, hg⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨1, Subtype.ext ?_⟩
    show (x ^ n) ^ (5 ^ 1) = 1
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]
  have hfix : Nat.card (MulAction.fixedPoints G W) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => ?_⟩, ⟨⟨0, ?_⟩⟩⟩
    · have ha := hfpf a.1 (a.2 ⟨x, Subgroup.mem_zpowers x⟩)
      have hb := hfpf b.1 (b.2 ⟨x, Subgroup.mem_zpowers x⟩)
      exact Subtype.ext (ha.trans hb.symm)
    · intro g
      exact map_zero _
  have hmod := hG.card_modEq_card_fixedPoints W
  rw [hfix, Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W)] at hmod
  rw [Nat.card_zmod] at hmod
  set n := finrank (ZMod 2) W with hn
  have h1 : 2 ^ n % 5 = 1 := hmod
  have h2 : 2 ^ n % 5 = 2 ^ (n % 4) % 5 := by
    conv_lhs => rw [← Nat.div_add_mod n 4, pow_add, pow_mul]
    rw [Nat.mul_mod, Nat.pow_mod]
    norm_num
  have h3 : n % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have h4 : n % 4 = 0 := by
    rw [h2] at h1
    interval_cases hh : n % 4 <;> simp_all
  omega

end Four

section Invariant
variable [Module.Finite (ZMod 2) W]

theorem pow_four_mem (x : W ≃ₗ[ZMod 2] W) (S : Submodule (ZMod 2) W) (hS : ∀ w ∈ S, x w ∈ S)
    (w : W) (hw : w ∈ S) : (x ^ 4) w ∈ S := by
  have e : (x ^ 4) w = x (x (x (x w))) := by simp [pow_succ_apply]
  rw [e]
  exact hS _ (hS _ (hS _ (hS _ hw)))

theorem four_dvd_finrank_of_invariant (x : W ≃ₗ[ZMod 2] W) (hx : x ^ 5 = 1)
    (hfpf : ∀ w, x w = w → w = 0) (S : Submodule (ZMod 2) W) (hS : ∀ w ∈ S, x w ∈ S) :
    4 ∣ finrank (ZMod 2) S := by
  have hmap : S.map (x : W →ₗ[ZMod 2] W) = S := by
    apply le_antisymm
    · rintro _ ⟨w, hw, rfl⟩
      exact hS w hw
    · intro w hw
      refine ⟨(x ^ 4) w, pow_four_mem x S hS w hw, ?_⟩
      show x ((x ^ 4) w) = w
      have : (x ^ (4 + 1)) w = x ((x ^ 4) w) := pow_succ_apply x 4 w
      rw [← this]
      show (x ^ 5) w = w
      rw [hx]; rfl
  let xS : S ≃ₗ[ZMod 2] S := LinearEquiv.ofSubmodules x S S hmap
  have hxS : ∀ v : S, ((xS v : S) : W) = x (v : W) := fun v => rfl
  have hpow : ∀ (n : ℕ) (v : S), (((xS ^ n) v : S) : W) = (x ^ n) (v : W) := by
    intro n
    induction n with
    | zero => intro v; rfl
    | succ n ih =>
      intro v
      rw [pow_succ_apply, pow_succ_apply, hxS, ih]
  apply four_dvd_finrank xS
  · refine LinearEquiv.ext fun v => Subtype.ext ?_
    rw [hpow, hx]
    rfl
  · intro v hv
    refine Subtype.ext ?_
    have := congrArg (fun u : S => (u : W)) hv
    exact hfpf _ this

theorem eq_bot_or_top_of_invariant (x : W ≃ₗ[ZMod 2] W) (hx : x ^ 5 = 1)
    (hfpf : ∀ w, x w = w → w = 0) (hdim : finrank (ZMod 2) W = 4)
    (S : Submodule (ZMod 2) W) (hS : ∀ w ∈ S, x w ∈ S) : S = ⊥ ∨ S = ⊤ := by
  have hd := four_dvd_finrank_of_invariant x hx hfpf S hS
  have hle : finrank (ZMod 2) S ≤ 4 := hdim ▸ Submodule.finrank_le S
  have : finrank (ZMod 2) S = 0 ∨ finrank (ZMod 2) S = 4 := by
    obtain ⟨k, hk⟩ := hd
    omega
  rcases this with h | h
  · left
    exact Submodule.finrank_eq_zero.mp h
  · right
    exact Submodule.eq_top_of_finrank_eq (h.trans hdim.symm)

end Invariant

section Rel
variable (x t : W ≃ₗ[ZMod 2] W)

variable (hx : x ^ 5 = 1) (ht : t * t = 1) (htx : t * x * t = x ^ 4)
include hx ht htx

theorem t_mul_x : t * x = x ^ 4 * t := by
  calc t * x = t * x * (t * t) := by rw [ht, mul_one]
    _ = (t * x * t) * t := by simp only [mul_assoc]
    _ = x ^ 4 * t := by rw [htx]

theorem t_mul_x4 : t * x ^ 4 = x * t := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have h1 : (t * x * t⁻¹) ^ 4 = t * x ^ 4 * t⁻¹ := conj_pow
  rw [hti, htx] at h1
  have h16 : (x ^ 4) ^ 4 = x := by
    calc (x ^ 4) ^ 4 = x ^ 16 := by rw [← pow_mul]
      _ = (x ^ 5) ^ 3 * x := by rw [← pow_mul, ← pow_succ]
      _ = x := by rw [hx]; simp
  rw [h16] at h1
  calc t * x ^ 4 = t * x ^ 4 * (t * t) := by rw [ht, mul_one]
    _ = (t * x ^ 4 * t) * t := by simp only [mul_assoc]
    _ = x * t := by rw [← h1]

theorem t_x_apply (w : W) : t (x w) = (x ^ 4) (t w) := by
  have := congrArg (fun g : W ≃ₗ[ZMod 2] W => g w) (t_mul_x x t hx ht htx)
  simpa using this

theorem t_x4_apply (w : W) : t ((x ^ 4) w) = x (t w) := by
  have := congrArg (fun g : W ≃ₗ[ZMod 2] W => g w) (t_mul_x4 x t hx ht htx)
  simpa using this

section Fpf

variable [Module.Finite (ZMod 2) W]
variable (hfpf : ∀ w, x w = w → w = 0)
include hfpf

theorem a_inj : Function.Injective ((x : W →ₗ[ZMod 2] W) +
    ((x ^ 4 : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W)) := by
  rw [injective_iff_map_eq_zero]
  intro w hw
  simp only [LinearMap.add_apply, LinearEquiv.coe_coe] at hw
  have h1 : x w = (x ^ 4) w := by
    have := neg_eq_of_add_eq_zero_left hw
    rw [neg_eq_self'] at this
    exact this.symm
  have h2 : x (x w) = w := by
    rw [h1]
    have : (x ^ (4 + 1)) w = x ((x ^ 4) w) := pow_succ_apply x 4 w
    rw [← this]
    show (x ^ 5) w = w
    rw [hx]; rfl
  exact hfpf w (x_sq_fix x hx w h2)

theorem descent (w : W) (hw : t w = w) : ∃ v, t v + v = w := by
  have hinj := a_inj x t hx ht htx hfpf
  have hsurj := LinearMap.injective_iff_surjective.mp hinj
  obtain ⟨v0, hv0⟩ := hsurj w
  have hav : ∀ v, ((x : W →ₗ[ZMod 2] W) +
      ((x ^ 4 : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W)) v = x v + (x ^ 4) v := fun v => rfl
  have hta : ∀ v, t (x v + (x ^ 4) v) = x (t v) + (x ^ 4) (t v) := by
    intro v
    rw [map_add, t_x_apply x t hx ht htx, t_x4_apply x t hx ht htx, add_comm]
  have htv : t v0 = v0 := by
    apply hinj
    rw [hav, hav, ← hta, ← hav v0, hv0, hw]
  refine ⟨x v0, ?_⟩
  rw [t_x_apply x t hx ht htx, htv, add_comm]
  rw [hav] at hv0
  exact hv0

theorem finrank_eq_two_mul :
    finrank (ZMod 2) W = 2 * finrank (ZMod 2)
      (LinearMap.range ((t : W →ₗ[ZMod 2] W) - LinearMap.id)) := by
  set g : W →ₗ[ZMod 2] W := (t : W →ₗ[ZMod 2] W) - LinearMap.id with hg
  have hgv : ∀ v, g v = t v + v := fun v => by
    show t v - v = t v + v
    exact sub_eq_add' _ _
  have hker : LinearMap.ker g = LinearMap.range g := by
    ext w
    simp only [LinearMap.mem_ker, LinearMap.mem_range, hgv]
    constructor
    · intro h
      have hw : t w = w := by
        have := neg_eq_of_add_eq_zero_left h
        rw [neg_eq_self'] at this
        exact this.symm
      exact descent x t hx ht htx hfpf w hw
    · rintro ⟨v, rfl⟩
      have htt : t (t v) = v := by
        have := congrArg (fun g : W ≃ₗ[ZMod 2] W => g v) ht
        simpa using this
      rw [map_add, htt, add_comm v (t v)]
      exact add_self_eq_zero _
  have h := LinearMap.finrank_range_add_finrank_ker g
  rw [hker] at h
  omega

end Fpf
end Rel

section Form
variable [Module.Finite (ZMod 2) W]

theorem no_invariant_form (hdim : finrank (ZMod 2) W = 4)
    (f r : W ≃ₗ[ZMod 2] W) (hc : Commute f r) (hf : orderOf f = 5) (hr : orderOf r = 3)
    (hfpf : ∀ w, f w = w → w = 0)
    (B : W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2)
    (hfB : ∀ v w, B (f v) (f w) = B v w) (hrB : ∀ v w, B (r v) (r w) = B v w)
    (hB : ∃ v w, B v w ≠ 0) : False := by
  have hf5 : f ^ 5 = 1 := by rw [← hf]; exact pow_orderOf_eq_one f
  have hinv : ∀ v ∈ LinearMap.ker B, f v ∈ LinearMap.ker B := by
    intro v hv
    rw [LinearMap.mem_ker] at hv ⊢
    ext w
    have h1 : B (f v) w = B v (f.symm w) := by
      have := hfB v (f.symm w)
      simpa using this
    rw [LinearMap.zero_apply, h1, hv]
    rfl
  rcases eq_bot_or_top_of_invariant f hf5 hfpf hdim (LinearMap.ker B) hinv with h | h
  · refine CFSG.Quasithin.Recognition.Kleidman.OrdinaryProofs.F3Invariant.no_commuting_five_three
      hdim B ?_ f r hc hf hr hfB hrB
    intro v hv
    have : v ∈ LinearMap.ker B := by
      rw [LinearMap.mem_ker]
      ext w
      exact hv w
    rw [h] at this
    exact (Submodule.mem_bot _).mp this
  · obtain ⟨v, w, hvw⟩ := hB
    have : v ∈ LinearMap.ker B := by rw [h]; trivial
    rw [LinearMap.mem_ker] at this
    exact hvw (by rw [this]; rfl)

end Form

section General

variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]

@[expose] def fixSub (x : U ≃ₗ[ZMod 2] U) : Submodule (ZMod 2) U where
  carrier := {u | x u = u}
  add_mem' := by
    intro a b ha hb
    show x (a + b) = a + b
    rw [map_add, show x a = a from ha, show x b = b from hb]
  zero_mem' := map_zero x
  smul_mem' := by
    intro c a ha
    show x (c • a) = c • a
    rw [map_smul, show x a = a from ha]

theorem mem_fixSub {x : U ≃ₗ[ZMod 2] U} {u : U} : u ∈ fixSub x ↔ x u = u := Iff.rfl

theorem map_eq_of_pow (F : Submodule (ZMod 2) U) (g : U ≃ₗ[ZMod 2] U) (n : ℕ) (hn : g ^ (n + 1) = 1)
    (hF : ∀ u ∈ F, g u ∈ F) : F.map (g : U →ₗ[ZMod 2] U) = F := by
  apply le_antisymm
  · rintro _ ⟨w, hw, rfl⟩
    exact hF w hw
  · intro w hw
    have hpow : ∀ k : ℕ, ∀ u ∈ F, (g ^ k) u ∈ F := by
      intro k
      induction k with
      | zero => intro u hu; simpa using hu
      | succ k ih => intro u hu; rw [pow_succ_apply]; exact hF _ (ih u hu)
    refine ⟨(g ^ n) w, hpow n w hw, ?_⟩
    show g ((g ^ n) w) = w
    have : (g ^ (n + 1)) w = g ((g ^ n) w) := pow_succ_apply g n w
    rw [← this, hn]; rfl

@[expose] def qeq (F : Submodule (ZMod 2) U) (g : U ≃ₗ[ZMod 2] U) (h : F.map (g : U →ₗ[ZMod 2] U) = F) :
    (U ⧸ F) ≃ₗ[ZMod 2] (U ⧸ F) := Submodule.Quotient.equiv F F g h

theorem qeq_mk (F : Submodule (ZMod 2) U) (g : U ≃ₗ[ZMod 2] U) (h : F.map (g : U →ₗ[ZMod 2] U) = F)
    (u : U) : qeq F g h (Submodule.Quotient.mk u) = Submodule.Quotient.mk (g u) := rfl

theorem qeq_pow_mk (F : Submodule (ZMod 2) U) (g : U ≃ₗ[ZMod 2] U)
    (h : F.map (g : U →ₗ[ZMod 2] U) = F) (n : ℕ) (u : U) :
    ((qeq F g h) ^ n) (Submodule.Quotient.mk u) = Submodule.Quotient.mk ((g ^ n) u) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ_apply, ih, qeq_mk, pow_succ_apply]

end General

section K

variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U] [Module.Finite (ZMod 2) U]
variable (x t : U ≃ₗ[ZMod 2] U) (hx : x ^ 5 = 1) (ht : t * t = 1) (htx : t * x * t = x ^ 4)
include hx ht htx

theorem fixSub_t_inv (f : U) (hf : f ∈ fixSub x) : t f ∈ fixSub x := by
  have h4 : (x ^ 4) f = f := by
    have e : (x ^ 4) f = x (x (x (x f))) := by simp [pow_succ_apply]
    rw [e]
    have : x f = f := hf
    rw [this, this, this, this]
  have := t_x4_apply x t hx ht htx f
  rw [h4] at this
  exact this.symm

theorem map_fixSub_x : (fixSub x).map (x : U →ₗ[ZMod 2] U) = fixSub x :=
  map_eq_of_pow _ x 4 hx (fun u hu => by have : x u = u := hu; rw [mem_fixSub, this]; exact this)

theorem map_fixSub_t : (fixSub x).map (t : U →ₗ[ZMod 2] U) = fixSub x :=
  map_eq_of_pow _ t 1 (by rw [pow_two]; exact ht) (fixSub_t_inv x t hx ht htx)

theorem quot_fpf (q : U ⧸ fixSub x) (hq : qeq (fixSub x) x (map_fixSub_x x t hx ht htx) q = q) :
    q = 0 := by
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [qeq_mk] at hq
  have h1 : x u - u ∈ fixSub x := (Submodule.Quotient.eq _).mp hq
  have h2 : x (x u - u) = x u - u := h1
  rw [map_sub, sub_eq_add', sub_eq_add'] at h2
  have h3 : x (x u) = u := by
    have h4 : x (x u) + x u = x u + u := h2
    have h5 : x (x u) + x u = u + x u := by rw [h4, add_comm]
    exact add_right_cancel h5
  have h6 : x u = u := x_sq_fix x hx u h3
  rw [Submodule.Quotient.mk_eq_zero]
  exact h6

abbrev xq : (U ⧸ fixSub x) ≃ₗ[ZMod 2] (U ⧸ fixSub x) :=
  qeq (fixSub x) x (map_fixSub_x x t hx ht htx)

abbrev tq : (U ⧸ fixSub x) ≃ₗ[ZMod 2] (U ⧸ fixSub x) :=
  qeq (fixSub x) t (map_fixSub_t x t hx ht htx)

theorem xq_mk (u : U) : xq x t hx ht htx (Submodule.Quotient.mk u) = Submodule.Quotient.mk (x u) :=
  rfl

theorem tq_mk (u : U) : tq x t hx ht htx (Submodule.Quotient.mk u) = Submodule.Quotient.mk (t u) :=
  rfl

theorem xq_pow : xq x t hx ht htx ^ 5 = 1 := by
  refine LinearEquiv.ext fun q => ?_
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [qeq_pow_mk, hx]
  rfl

theorem tq_sq : tq x t hx ht htx * tq x t hx ht htx = 1 := by
  refine LinearEquiv.ext fun q => ?_
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  have : t (t u) = u := by
    have := congrArg (fun g : U ≃ₗ[ZMod 2] U => g u) ht
    simpa using this
  rw [LinearEquiv.mul_apply, tq_mk, tq_mk, this]
  rfl

theorem tq_xq : tq x t hx ht htx * xq x t hx ht htx * tq x t hx ht htx
    = xq x t hx ht htx ^ 4 := by
  refine LinearEquiv.ext fun q => ?_
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  have := congrArg (fun g : U ≃ₗ[ZMod 2] U => g u) htx
  simp only [LinearEquiv.mul_apply] at this
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, tq_mk, xq_mk, tq_mk, qeq_pow_mk, this]

theorem K_main
    (hrk : finrank (ZMod 2) (LinearMap.range ((t : U →ₗ[ZMod 2] U) - LinearMap.id)) ≤ 2)
    (hne : ∃ u, x u ≠ u) :
    (∀ f, x f = f → t f = f) ∧ finrank (ZMod 2) (U ⧸ fixSub x) = 4 ∧
      finrank (ZMod 2) (LinearMap.range ((t : U →ₗ[ZMod 2] U) - LinearMap.id)) = 2 := by
  set F := fixSub x with hF
  have hfpf : ∀ q, xq x t hx ht htx q = q → q = 0 := quot_fpf x t hx ht htx
  have hdesc := finrank_eq_two_mul (xq x t hx ht htx) (tq x t hx ht htx)
    (xq_pow x t hx ht htx) (tq_sq x t hx ht htx) (tq_xq x t hx ht htx) hfpf
  have hfour := four_dvd_finrank (xq x t hx ht htx) (xq_pow x t hx ht htx) hfpf
  let R := LinearMap.range ((t : U →ₗ[ZMod 2] U) - LinearMap.id)
  let L : R →ₗ[ZMod 2] (U ⧸ F) := F.mkQ ∘ₗ R.subtype
  have hrange : LinearMap.range L
      = LinearMap.range (((tq x t hx ht htx : (U ⧸ F) ≃ₗ[ZMod 2] (U ⧸ F)) :
          (U ⧸ F) →ₗ[ZMod 2] (U ⧸ F)) - LinearMap.id) := by
    ext z
    constructor
    · rintro ⟨⟨y, v, rfl⟩, rfl⟩
      refine ⟨Submodule.Quotient.mk v, ?_⟩
      show tq x t hx ht htx (Submodule.Quotient.mk v) - Submodule.Quotient.mk v
        = F.mkQ ((t : U →ₗ[ZMod 2] U) v - v)
      rw [map_sub]
      rfl
    · rintro ⟨q, rfl⟩
      obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      refine ⟨⟨(t : U →ₗ[ZMod 2] U) u - u, u, rfl⟩, ?_⟩
      show F.mkQ ((t : U →ₗ[ZMod 2] U) u - u) = tq x t hx ht htx (Submodule.Quotient.mk u)
        - Submodule.Quotient.mk u
      rw [map_sub]
      rfl
  have hle : finrank (ZMod 2) (LinearMap.range L) ≤ finrank (ZMod 2) R :=
    LinearMap.finrank_range_le L
  have hpos : 0 < finrank (ZMod 2) (U ⧸ F) := by
    obtain ⟨u, hu⟩ := hne
    have : Nontrivial (U ⧸ F) := by
      refine ⟨⟨Submodule.Quotient.mk u, 0, ?_⟩⟩
      intro h
      exact hu ((Submodule.Quotient.mk_eq_zero F).mp h)
    exact Module.finrank_pos
  have hrk2 : finrank (ZMod 2) R ≤ 2 := hrk
  have hd2 : finrank (ZMod 2) (U ⧸ F) = 2 * finrank (ZMod 2) (LinearMap.range L) := by
    rw [hrange]; exact hdesc
  have hdim : finrank (ZMod 2) (U ⧸ F) = 4 := by
    obtain ⟨k, hk⟩ := hfour
    have hk' : finrank (ZMod 2) (U ⧸ F) = 4 * k := hk
    omega
  have hrk' : finrank (ZMod 2) R = 2 := by omega
  refine ⟨?_, hdim, hrk'⟩
  have hker := LinearMap.finrank_range_add_finrank_ker L
  have hker0 : finrank (ZMod 2) (LinearMap.ker L) = 0 := by omega
  have hbot : LinearMap.ker L = ⊥ := Submodule.finrank_eq_zero.mp hker0
  intro f hf
  have htf : t f ∈ F := fixSub_t_inv x t hx ht htx f hf
  have hz : ((t : U →ₗ[ZMod 2] U) f - f) ∈ R := ⟨f, rfl⟩
  have hzF : (t : U →ₗ[ZMod 2] U) f - f ∈ F := F.sub_mem htf hf
  have hzk : (⟨(t : U →ₗ[ZMod 2] U) f - f, hz⟩ : R) ∈ LinearMap.ker L := by
    rw [LinearMap.mem_ker]
    exact (Submodule.Quotient.mk_eq_zero F).mpr hzF
  rw [hbot] at hzk
  have := congrArg Subtype.val ((Submodule.mem_bot _).mp hzk)
  have h0 : t f - f = 0 := this
  exact sub_eq_zero.mp h0

theorem t_t_apply (u : U) : t (t u) = u := by
  have := congrArg (fun g : U ≃ₗ[ZMod 2] U => g u) ht
  simpa using this

theorem K_prime
    (hH : ∀ u, (x * t * x ^ 4) (t u + u) = t u + u) : ∀ u, x u = u := by
  have h2 := two_nsmul_zero (W := U)
  have step1 : ∀ u, x (t u + u) = t u + u := by
    intro u
    have h := hH u
    have htw : t (t u + u) = t u + u := by
      rw [map_add, t_t_apply x t hx ht htx, add_comm]
    have : (x * t * x ^ 4) (t u + u) = x (x (t u + u)) := by
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, t_x4_apply x t hx ht htx, htw]
    rw [this] at h
    exact x_sq_fix x hx _ h
  have claimA : ∀ u, t (x u + u) = x u + u := by
    intro u
    set m := x u + u with hm
    have hs := step1 m
    set a := t u with ha
    set v : U := (x ^ 3) a + (x ^ 2) a + x a + a + u with hv
    have e1 : x (x a) = (x ^ 2) a := by
      have : (x ^ (1 + 1)) a = x ((x ^ 1) a) := pow_succ_apply x 1 a
      simpa using this.symm
    have e2 : x ((x ^ 2) a) = (x ^ 3) a := (pow_succ_apply x 2 a).symm
    have e3 : x ((x ^ 3) a) = (x ^ 4) a := (pow_succ_apply x 3 a).symm
    have hw : t m + m = x v + v := by
      have htm : t m = (x ^ 4) a + a := by
        rw [hm, map_add, t_x_apply x t hx ht htx]
      have hxv : x v = (x ^ 4) a + (x ^ 3) a + (x ^ 2) a + x a + x u := by
        rw [hv, map_add, map_add, map_add, map_add, e3, e2, e1]
      rw [htm, hxv, hv, hm]
      apply eq_of_add_eq_zero2
      have : (x ^ 4) a + a + (x u + u) + ((x ^ 4) a + (x ^ 3) a + (x ^ 2) a + x a + x u
          + ((x ^ 3) a + (x ^ 2) a + x a + a + u)) = (2 : ℕ) • (x ^ 4) a + (2 : ℕ) • a
          + (2 : ℕ) • (x u) + (2 : ℕ) • u + (2 : ℕ) • (x ^ 3) a + (2 : ℕ) • (x ^ 2) a
          + (2 : ℕ) • (x a) := by abel
      rw [this, h2, h2, h2, h2, h2, h2, h2]
      simp
    rw [hw] at hs
    have hxv1 : x (x v) = v := by
      have h4 : x (x v) + x v = x v + v := by rw [map_add] at hs; exact hs
      have h5 : x (x v) + x v = v + x v := by rw [h4, add_comm]
      exact add_right_cancel h5
    have hxv : x v = v := x_sq_fix x hx v hxv1
    have : t m + m = 0 := by rw [hw, hxv]; exact add_self_eq_zero v
    exact eq_of_add_eq_zero2 this
  intro u
  have hm1 : ∀ w, t (x w + w) = x w + w := claimA
  have h1 : t (x (x u + u)) = x (x u + u) := by
    have := hm1 (x u)
    rwa [← map_add] at this
  have h2' : t (x (x u + u)) = (x ^ 4) (t (x u + u)) := t_x_apply x t hx ht htx _
  rw [claimA u] at h2'
  rw [h2'] at h1
  have h3 : x (x (x u + u)) = x u + u := by
    have := congrArg x h1
    have e : x ((x ^ 4) (x u + u)) = x u + u := by
      have : (x ^ (4 + 1)) (x u + u) = x ((x ^ 4) (x u + u)) := pow_succ_apply x 4 _
      rw [← this]
      show (x ^ 5) (x u + u) = _
      rw [hx]; rfl
    rw [e] at this
    exact this.symm
  have h4 : x (x u + u) = x u + u := x_sq_fix x hx _ h3
  have h5 : x (x u) = u := by
    have h6 : x (x u) + x u = x u + u := by rw [map_add] at h4; exact h4
    have h7 : x (x u) + x u = u + x u := by rw [h6, add_comm]
    exact add_right_cancel h7
  exact x_sq_fix x hx u h5

section D
variable (d : U ≃ₗ[ZMod 2] U) (hd3 : d ^ 3 = 1) (hdx : d * x = x * d)
include hd3 hdx

theorem fixSub_d_inv (f : U) (hf : f ∈ fixSub x) : d f ∈ fixSub x := by
  have h := congrArg (fun g : U ≃ₗ[ZMod 2] U => g f) hdx
  simp only [LinearEquiv.mul_apply] at h
  have hf' : x f = f := hf
  rw [hf'] at h
  exact h.symm

theorem map_fixSub_d : (fixSub x).map (d : U →ₗ[ZMod 2] U) = fixSub x :=
  map_eq_of_pow _ d 2 hd3 (fixSub_d_inv x t hx ht htx d hd3 hdx)

abbrev dq : (U ⧸ fixSub x) ≃ₗ[ZMod 2] (U ⧸ fixSub x) :=
  qeq (fixSub x) d (map_fixSub_d x t hx ht htx d hd3 hdx)

theorem dq_mk (u : U) : dq x t hx ht htx d hd3 hdx (Submodule.Quotient.mk u)
    = Submodule.Quotient.mk (d u) := rfl

theorem dq_pow : dq x t hx ht htx d hd3 hdx ^ 3 = 1 := by
  refine LinearEquiv.ext fun q => ?_
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [qeq_pow_mk, hd3]
  rfl

theorem dq_xq_comm : Commute (dq x t hx ht htx d hd3 hdx) (xq x t hx ht htx) := by
  refine LinearEquiv.ext fun q => ?_
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  have h := congrArg (fun g : U ≃ₗ[ZMod 2] U => g u) hdx
  simp only [LinearEquiv.mul_apply] at h
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, xq_mk, dq_mk, dq_mk, xq_mk, h]

theorem no_form
    (hrk : finrank (ZMod 2) (LinearMap.range ((t : U →ₗ[ZMod 2] U) - LinearMap.id)) ≤ 2)
    (hne : ∃ u, x u ≠ u) (hdnt : ∃ u, d u + u ∉ fixSub x)
    (B : (U ⧸ fixSub x) →ₗ[ZMod 2] (U ⧸ fixSub x) →ₗ[ZMod 2] ZMod 2)
    (hxB : ∀ v w, B (xq x t hx ht htx v) (xq x t hx ht htx w) = B v w)
    (hdB : ∀ v w, B (dq x t hx ht htx d hd3 hdx v) (dq x t hx ht htx d hd3 hdx w) = B v w)
    (hB : ∃ v w, B v w ≠ 0) : False := by
  obtain ⟨-, hdim, -⟩ := K_main x t hx ht htx hrk hne
  have hfpf := quot_fpf x t hx ht htx
  have hx5 := xq_pow x t hx ht htx
  have hxne : xq x t hx ht htx ≠ 1 := by
    intro h1
    obtain ⟨u, hu⟩ := hne
    have : Nontrivial (U ⧸ fixSub x) := by
      refine ⟨⟨Submodule.Quotient.mk u, 0, ?_⟩⟩
      intro h
      exact hu ((Submodule.Quotient.mk_eq_zero _).mp h)
    have hpos : 0 < finrank (ZMod 2) (U ⧸ fixSub x) := Module.finrank_pos
    have hall : ∀ q : U ⧸ fixSub x, q = 0 := by
      intro q
      apply hfpf
      show xq x t hx ht htx q = q
      rw [h1]; rfl
    have : finrank (ZMod 2) (U ⧸ fixSub x) = 0 := by
      have : Subsingleton (U ⧸ fixSub x) := ⟨fun a b => (hall a).trans (hall b).symm⟩
      exact Module.finrank_zero_of_subsingleton
    omega
  have hxo : orderOf (xq x t hx ht htx) = 5 :=
    orderOf_eq_prime hx5 hxne (hp := ⟨Nat.prime_five⟩)
  have hdne : dq x t hx ht htx d hd3 hdx ≠ 1 := by
    intro h1
    obtain ⟨u, hu⟩ := hdnt
    apply hu
    have h := congrArg (fun g => g (Submodule.Quotient.mk u)) h1
    simp only [dq_mk] at h
    have h' : (Submodule.Quotient.mk (d u) : U ⧸ fixSub x) = Submodule.Quotient.mk u := h
    have := (Submodule.Quotient.eq _).mp h'
    rw [sub_eq_add'] at this
    exact this
  have hdo : orderOf (dq x t hx ht htx d hd3 hdx) = 3 :=
    orderOf_eq_prime (dq_pow x t hx ht htx d hd3 hdx) hdne (hp := ⟨Nat.prime_three⟩)
  exact no_invariant_form hdim (xq x t hx ht htx) (dq x t hx ht htx d hd3 hdx)
    (dq_xq_comm x t hx ht htx d hd3 hdx).symm hxo hdo (hfpf) B hxB hdB hB

end D

end K

end CFSG.Quasithin.Kleidman.F204.O2Alg
