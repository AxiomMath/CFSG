module

public import CFSG.Quasithin.Background.SimsE2DihMod
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.SimsE2

namespace Dih

open Polynomial

section Additive

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem exists_isCompl_of_pow_eq_self (θ : Module.End (ZMod 2) W) {n : ℕ} (hn : n ≠ 0)
    (hθ : θ ^ 2 ^ n = θ) {S : Submodule (ZMod 2) W} (hS : S ∈ θ.invtSubmodule) :
    ∃ S' ∈ θ.invtSubmodule, IsCompl S S' := by
  have hsep : (X ^ 2 ^ n - X : (ZMod 2)[X]).Separable :=
    galois_poly_separable 2 (2 ^ n) (dvd_pow_self 2 hn)
  have hss : θ.IsSemisimple := Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    hsep.squarefree (by rw [map_sub, map_pow, aeval_X, hθ, sub_self])
  exact Module.End.isSemisimple_iff.1 hss S hS

theorem aeval_pow_two_pow {A : Type*} [Ring A] [Algebra (ZMod 2) A] (a : A) {n : ℕ}
    (ha : a ^ 2 ^ n = a) (f : (ZMod 2)[X]) : aeval a (f ^ 2 ^ n) = aeval a f := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hexp : ∀ k : ℕ, f ^ 2 ^ k = expand (ZMod 2) (2 ^ k) f := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc f ^ 2 ^ (k + 1) = (f ^ 2 ^ k) ^ 2 := by rw [pow_succ, pow_mul]
        _ = (expand (ZMod 2) (2 ^ k) f) ^ 2 := by rw [ih]
        _ = expand (ZMod 2) 2 (expand (ZMod 2) (2 ^ k) f) := (ZMod.expand_card _).symm
        _ = expand (ZMod 2) (2 ^ (k + 1)) f := by rw [expand_expand, pow_succ, mul_comm]
  rw [hexp n, expand_aeval, ha]

theorem card_le_of_minimal [Finite W] (θ : Module.End (ZMod 2) W) {n : ℕ} (hn : n ≠ 0)
    (hθ : θ ^ 2 ^ n = θ) {S : Submodule (ZMod 2) W} (hS : S ∈ θ.invtSubmodule) (hS0 : S ≠ ⊥)
    (hmin : ∀ T ∈ θ.invtSubmodule, T ≤ S → T = ⊥ ∨ T = S) : Nat.card S ≤ 2 ^ n := by
  classical
  have hS' : ∀ x ∈ S, θ x ∈ S := fun x hx => hS hx
  set θS : Module.End (ZMod 2) S := θ.restrict hS' with hθSdef
  have hθS : θS ^ 2 ^ n = θS := by
    rw [hθSdef, Module.End.pow_restrict]
    ext x
    simp [hθ]
  obtain ⟨s₀, hs₀S, hs₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS0
  have hcomm : ∀ f : (ZMod 2)[X], aeval θS f * θS = θS * aeval θS f := by
    intro f
    have h1 : aeval θS (f * X) = aeval θS f * θS := by rw [map_mul, aeval_X]
    have h2 : aeval θS (X * f) = θS * aeval θS f := by rw [map_mul, aeval_X]
    rw [← h1, ← h2, mul_comm]
  have hinj : ∀ f : (ZMod 2)[X], aeval θS f ≠ 0 → Function.Injective (aeval θS f) := by
    intro f hf
    set T := (LinearMap.ker (aeval θS f)).map S.subtype with hTdef
    have hT : T ∈ θ.invtSubmodule := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
      rw [Submodule.mem_comap]
      refine Submodule.mem_map.2 ⟨θS x, ?_, rfl⟩
      rw [LinearMap.mem_ker] at hx ⊢
      rw [← Module.End.mul_apply, hcomm, Module.End.mul_apply, hx, map_zero]
    rcases hmin T hT (Submodule.map_subtype_le _ _) with h | h
    · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro x hx
      have hxT : S.subtype x ∈ T := Submodule.mem_map.2 ⟨x, hx, rfl⟩
      rw [h, Submodule.mem_bot] at hxT
      exact (Submodule.mem_bot _).2 (Subtype.ext hxT)
    · exfalso
      apply hf
      ext x
      have hxT : (x : W) ∈ T := by rw [h]; exact x.2
      obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.1 hxT
      have hxy : y = x := Subtype.ext hyx
      rw [← hxy]
      exact congrArg Subtype.val (LinearMap.mem_ker.1 hy)
  set φ : (ZMod 2)[X] →+* Module.End (ZMod 2) S := (aeval θS).toRingHom with hφ
  have hφapp : ∀ f, φ f = aeval θS f := fun f => rfl
  haveI hprime : (RingHom.ker φ).IsPrime := by
    rw [Ideal.isPrime_iff]
    refine ⟨?_, fun {f g} hfg => ?_⟩
    · rw [Ne, Ideal.eq_top_iff_one, RingHom.mem_ker, map_one]
      intro h1
      apply hs₀
      have := LinearMap.congr_fun h1 ⟨s₀, hs₀S⟩
      simpa using congrArg Subtype.val this
    · rw [RingHom.mem_ker, map_mul] at hfg
      by_cases hf : φ f = 0
      · exact Or.inl hf
      · right
        rw [RingHom.mem_ker]
        ext x
        have := LinearMap.congr_fun hfg x
        rw [Module.End.mul_apply, LinearMap.zero_apply] at this
        have h0 := hinj f (by rwa [← hφapp]) (this.trans (map_zero (aeval θS f)).symm)
        rw [h0]
        rfl
  haveI : Finite (Module.End (ZMod 2) S) :=
    Finite.of_injective (fun f : Module.End (ZMod 2) S => (f : S → S)) DFunLike.coe_injective
  haveI : Finite ((ZMod 2)[X] ⧸ RingHom.ker φ) :=
    Finite.of_equiv _ (RingHom.quotientKerEquivRange φ).symm.toEquiv
  have hroot : ∀ x : (ZMod 2)[X] ⧸ RingHom.ker φ, x ^ 2 ^ n = x := by
    intro x
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← map_pow, Ideal.Quotient.eq, RingHom.mem_ker, map_sub, sub_eq_zero, hφapp, hφapp]
    exact aeval_pow_two_pow θS hθS f
  have hcardR : Nat.card ((ZMod 2)[X] ⧸ RingHom.ker φ) ≤ 2 ^ n := by
    haveI : Fintype ((ZMod 2)[X] ⧸ RingHom.ker φ) := Fintype.ofFinite _
    have hq : 1 < 2 ^ n := Nat.one_lt_two_pow hn
    have hdeg : (X ^ 2 ^ n - X : ((ZMod 2)[X] ⧸ RingHom.ker φ)[X]).natDegree = 2 ^ n := by
      rw [natDegree_sub_eq_left_of_natDegree_lt] <;> simp [hq]
    have hne : (X ^ 2 ^ n - X : ((ZMod 2)[X] ⧸ RingHom.ker φ)[X]) ≠ 0 := by
      intro h0
      rw [h0, natDegree_zero] at hdeg
      omega
    rw [Nat.card_eq_fintype_card, ← Finset.card_univ, ← hdeg]
    apply card_le_degree_of_subset_roots
    intro x _
    rw [mem_roots hne, IsRoot, eval_sub, eval_pow, eval_X, hroot, sub_self]
  set ev : (ZMod 2)[X] →ₗ[ZMod 2] S :=
    (LinearMap.applyₗ (⟨s₀, hs₀S⟩ : S)).comp (aeval θS).toLinearMap with hevdef
  have hev : ∀ f, ev f = aeval θS f ⟨s₀, hs₀S⟩ := fun f => rfl
  set T := (LinearMap.range ev).map S.subtype with hTdef
  have hTinv : T ∈ θ.invtSubmodule := by
    intro y hy
    obtain ⟨_, ⟨f, rfl⟩, rfl⟩ := Submodule.mem_map.1 hy
    rw [Submodule.mem_comap]
    refine Submodule.mem_map.2 ⟨ev (X * f), LinearMap.mem_range_self _ _, ?_⟩
    rw [hev, map_mul, aeval_X, Module.End.mul_apply]
    rfl
  have hs₀T : s₀ ∈ T := Submodule.mem_map.2 ⟨ev 1, LinearMap.mem_range_self _ _, by simp [hev]⟩
  have hTS : T = S := (hmin T hTinv (Submodule.map_subtype_le _ _)).resolve_left fun h => by
    rw [h] at hs₀T
    exact hs₀ ((Submodule.mem_bot _).1 hs₀T)
  have hsurj : Function.Surjective
      (fun k : φ.range => (k : Module.End (ZMod 2) S) ⟨s₀, hs₀S⟩) := by
    intro s
    have hsT : (s : W) ∈ T := by rw [hTS]; exact s.2
    obtain ⟨_, ⟨f, rfl⟩, hfs⟩ := Submodule.mem_map.1 hsT
    exact ⟨⟨φ f, RingHom.mem_range_self φ f⟩, Subtype.ext hfs⟩
  calc Nat.card S ≤ Nat.card φ.range := Nat.card_le_card_of_surjective _ hsurj
    _ = Nat.card ((ZMod 2)[X] ⧸ RingHom.ker φ) :=
      Nat.card_congr (RingHom.quotientKerEquivRange φ).symm.toEquiv
    _ ≤ 2 ^ n := hcardR

end Additive

section Arith

theorem dParamPrime_ne_zero {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : E2.dParamPrime p ≠ 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have h20 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by rw [Nat.cast_ofNat]; exact h
    rw [CharP.cast_eq_zero_iff (ZMod p) p] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h')
  have hpos : 0 < E2.dParam p := orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2
    ⟨p - 1, by have := hp.two_le; omega, ZMod.pow_card_sub_one_eq_one h20⟩)
  have h1 : E2.dParam p ≠ 1 := by
    intro h
    have h21 : (2 : ZMod p) = 1 := orderOf_eq_one_iff.1 h
    have h10 : ((1 : ℕ) : ZMod p) = 0 := by
      rw [Nat.cast_one]
      calc (1 : ZMod p) = 2 - 1 := by ring
        _ = 0 := by rw [h21, sub_self]
    rw [CharP.cast_eq_zero_iff (ZMod p) p] at h10
    exact hp.one_lt.ne' (Nat.dvd_one.1 h10)
  unfold E2.dParamPrime
  split_ifs <;> omega

theorem two_pow_dParamPrime {p : ℕ} (hp : p.Prime) :
    (2 : ZMod p) ^ E2.dParamPrime p = 1 ∨ (2 : ZMod p) ^ E2.dParamPrime p = -1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hd : (2 : ZMod p) ^ E2.dParam p = 1 := pow_orderOf_eq_one _
  unfold E2.dParamPrime
  split_ifs with hev
  · obtain ⟨k, hk⟩ := hev
    have hk2 : (k + k) / 2 = k := by omega
    rw [hk, hk2]
    rw [hk, ← two_mul, pow_mul'] at hd
    exact mul_self_eq_one_iff.1 (by rw [← sq]; exact hd)
  · exact Or.inl hd

theorem pow_eq_zpow_of_cast_eq {G : Type*} [Group G] {x : G} {p : ℕ} (hx : orderOf x = p)
    {q : ℕ} {m : ℤ} (h : ((q : ℤ) : ZMod p) = (m : ZMod p)) : x ^ q = x ^ m := by
  rw [← zpow_natCast, zpow_eq_zpow_iff_modEq, hx, ← ZMod.intCast_eq_intCast_iff]
  exact h

end Arith

section Theta

variable {N : Type*} [CommGroup N]

@[expose] def thetaHom (γ : MulAut N) : N →* N where
  toFun x := γ x * γ⁻¹ x
  map_one' := by rw [map_one, map_one, one_mul]
  map_mul' x y := by
    change γ (x * y) * γ⁻¹ (x * y) = γ x * γ⁻¹ x * (γ y * γ⁻¹ y)
    rw [map_mul, map_mul]
    exact mul_mul_mul_comm _ _ _ _

theorem thetaHom_apply (γ : MulAut N) (x : N) : thetaHom γ x = γ x * γ⁻¹ x := rfl

theorem iterate_theta_two_pow (hsq : ∀ x : N, x * x = 1) (γ : MulAut N) (k : ℕ) (x : N) :
    (thetaHom γ)^[2 ^ k] x = (γ ^ 2 ^ k) x * (γ⁻¹ ^ 2 ^ k) x := by
  induction k generalizing x with
  | zero => simp [thetaHom_apply]
  | succ k ih =>
    have hgh : ∀ y, (γ ^ 2 ^ k) ((γ⁻¹ ^ 2 ^ k) y) = y := fun y => by
      rw [← MulAut.mul_apply, inv_pow, mul_inv_cancel, MulAut.one_apply]
    have hhg : ∀ y, (γ⁻¹ ^ 2 ^ k) ((γ ^ 2 ^ k) y) = y := fun y => by
      rw [← MulAut.mul_apply, inv_pow, inv_mul_cancel, MulAut.one_apply]
    have e2 : ∀ (F : N → N) (y : N), F^[2] y = F (F y) := fun F y => rfl
    rw [pow_succ, Function.iterate_mul, e2, ih, ih, map_mul, map_mul, hgh, hhg, pow_mul,
      pow_mul, sq, sq, MulAut.mul_apply, MulAut.mul_apply]
    calc (γ ^ 2 ^ k) ((γ ^ 2 ^ k) x) * x * (x * (γ⁻¹ ^ 2 ^ k) ((γ⁻¹ ^ 2 ^ k) x)) =
        (γ ^ 2 ^ k) ((γ ^ 2 ^ k) x) * (x * x) * (γ⁻¹ ^ 2 ^ k) ((γ⁻¹ ^ 2 ^ k) x) := by
          simp only [mul_assoc]
      _ = _ := by rw [hsq, mul_one]

theorem iterate_theta_eq (hsq : ∀ x : N, x * x = 1) {p : ℕ} (hp : p.Prime) {γ : MulAut N}
    (hγ : orderOf γ = p) (x : N) : (thetaHom γ)^[2 ^ E2.dParamPrime p] x = thetaHom γ x := by
  rw [iterate_theta_two_pow hsq, thetaHom_apply]
  have hcast : (((2 ^ E2.dParamPrime p : ℕ) : ℤ) : ZMod p) = (2 : ZMod p) ^ E2.dParamPrime p := by
    push_cast
    rfl
  rcases two_pow_dParamPrime hp with h | h
  · have hq : γ ^ 2 ^ E2.dParamPrime p = γ := by
      rw [pow_eq_zpow_of_cast_eq hγ (m := 1) (by rw [hcast, h]; push_cast; rfl), zpow_one]
    rw [inv_pow, hq]
  · have hq : γ ^ 2 ^ E2.dParamPrime p = γ⁻¹ := by
      rw [pow_eq_zpow_of_cast_eq hγ (m := -1) (by rw [hcast, h]; push_cast; rfl), zpow_neg_one]
    rw [inv_pow, hq, inv_inv, mul_comm]

theorem thetaHom_comm {γ τ : MulAut N} (hτγ : τ * γ * τ⁻¹ = γ⁻¹) (x : N) :
    τ (thetaHom γ x) = thetaHom γ (τ x) := by
  have h1 : τ * γ = γ⁻¹ * τ := by rw [← hτγ, inv_mul_cancel_right]
  have h2 : τ * γ⁻¹ = γ * τ := by
    calc τ * γ⁻¹ = γ * (γ⁻¹ * τ) * γ⁻¹ := by group
      _ = γ * (τ * γ) * γ⁻¹ := by rw [h1]
      _ = γ * τ := by group
  have e1 : τ (γ x) = γ⁻¹ (τ x) := by rw [← MulAut.mul_apply, h1, MulAut.mul_apply]
  have e2 : τ (γ⁻¹ x) = γ (τ x) := by rw [← MulAut.mul_apply, h2, MulAut.mul_apply]
  rw [thetaHom_apply, thetaHom_apply, map_mul, e1, e2, mul_comm]

end Theta

section Bridge

variable {N : Type*} [CommGroup N]

@[expose, instance_reducible] def moduleZModTwo (hsq : ∀ x : N, x * x = 1) :
    Module (ZMod 2) (Additive N) :=
  AddCommGroup.zmodModule (n := 2) fun x => by
    rw [two_nsmul]
    exact hsq (Additive.toMul x)

section Module

variable [Module (ZMod 2) (Additive N)]

@[expose] def subgroupOrderIsoSubmodule : Subgroup N ≃o Submodule (ZMod 2) (Additive N) :=
  Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule 2)

theorem mem_subgroupOrderIsoSubmodule (T : Subgroup N) (x : Additive N) :
    x ∈ subgroupOrderIsoSubmodule T ↔ Additive.toMul x ∈ T :=
  Iff.rfl

theorem card_subgroupOrderIsoSubmodule (T : Subgroup N) :
    Nat.card (subgroupOrderIsoSubmodule T) = Nat.card T :=
  Nat.card_congr (Equiv.subtypeEquiv Additive.toMul fun x => mem_subgroupOrderIsoSubmodule T x)

theorem invtSubmodule_iff (θ : N →* N) (T : Subgroup N) :
    subgroupOrderIsoSubmodule T ∈
        Module.End.invtSubmodule ((MonoidHom.toAdditive θ).toZModLinearMap 2) ↔
      ∀ x ∈ T, θ x ∈ T := by
  rw [Module.End.mem_invtSubmodule]
  exact ⟨fun h x hx => (mem_subgroupOrderIsoSubmodule T _).1
      (h ((mem_subgroupOrderIsoSubmodule T (Additive.ofMul x)).2 hx)),
    fun h x hx => (mem_subgroupOrderIsoSubmodule T _).2
      (h _ ((mem_subgroupOrderIsoSubmodule T x).1 hx))⟩

theorem toZModLinearMap_pow_eq (θ : N →* N) {n : ℕ} (hθ : ∀ x, θ^[2 ^ n] x = θ x) :
    ((MonoidHom.toAdditive θ).toZModLinearMap 2) ^ 2 ^ n =
      (MonoidHom.toAdditive θ).toZModLinearMap 2 := by
  have hit : ∀ (k : ℕ) (x : Additive N), ((MonoidHom.toAdditive θ).toZModLinearMap 2)^[k] x =
      Additive.ofMul (θ^[k] (Additive.toMul x)) := by
    intro k
    induction k with
    | zero => intro x; rfl
    | succ k ih => intro x; rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']; rfl
  ext x
  rw [Module.End.pow_apply, hit, hθ]
  rfl

end Module

theorem exists_compl_of_iterate (hsq : ∀ x : N, x * x = 1) (θ : N →* N) {n : ℕ} (hn : n ≠ 0)
    (hθ : ∀ x, θ^[2 ^ n] x = θ x) {S : Subgroup N} (hS : ∀ x ∈ S, θ x ∈ S) :
    ∃ S' : Subgroup N, (∀ x ∈ S', θ x ∈ S') ∧ S ⊓ S' = ⊥ ∧ S ⊔ S' = ⊤ := by
  letI := moduleZModTwo hsq
  set e : Subgroup N ≃o Submodule (ZMod 2) (Additive N) := subgroupOrderIsoSubmodule
  obtain ⟨S'', hS''inv, hcompl⟩ := exists_isCompl_of_pow_eq_self _ hn
    (toZModLinearMap_pow_eq θ hθ) ((invtSubmodule_iff θ S).2 hS)
  have hc := (OrderIso.isCompl_iff e.symm).1 hcompl
  rw [e.symm_apply_apply] at hc
  refine ⟨e.symm S'', (invtSubmodule_iff θ _).1 (by rwa [e.apply_symm_apply]),
    disjoint_iff.1 hc.disjoint, codisjoint_iff.1 hc.codisjoint⟩

theorem card_le_of_minimal_mul [Finite N] (hsq : ∀ x : N, x * x = 1) (θ : N →* N) {n : ℕ}
    (hn : n ≠ 0) (hθ : ∀ x, θ^[2 ^ n] x = θ x) {S : Subgroup N} (hS : ∀ x ∈ S, θ x ∈ S)
    (hS0 : S ≠ ⊥) (hmin : ∀ T : Subgroup N, (∀ x ∈ T, θ x ∈ T) → T ≤ S → T = ⊥ ∨ T = S) :
    Nat.card S ≤ 2 ^ n := by
  letI := moduleZModTwo hsq
  set e : Subgroup N ≃o Submodule (ZMod 2) (Additive N) := subgroupOrderIsoSubmodule
  rw [← card_subgroupOrderIsoSubmodule S]
  refine card_le_of_minimal _ hn (toZModLinearMap_pow_eq θ hθ) ((invtSubmodule_iff θ S).2 hS)
    (fun h => hS0 ?_) fun T' hT' hT'S => ?_
  · rw [← e.symm_apply_apply S, show e S = ⊥ from h, map_bot]
  · have hT : ∀ x ∈ e.symm T', θ x ∈ e.symm T' :=
      (invtSubmodule_iff θ _).1 (by rwa [e.apply_symm_apply])
    have hle : e.symm T' ≤ S := by
      rw [← e.symm_apply_apply S]
      exact e.symm.monotone hT'S
    rcases hmin _ hT hle with h | h
    · left
      rw [← e.apply_symm_apply T', h, map_bot]
    · right
      rw [← e.apply_symm_apply T', h]

end Bridge

section Decomp

variable {N : Type*} [CommGroup N]

theorem card_sup_le [Finite N] (S T : Subgroup N) :
    Nat.card ↥(S ⊔ T) ≤ Nat.card S * Nat.card T := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_surjective (fun x : ↥S × ↥T =>
    (⟨(x.1 : N) * x.2, Subgroup.mul_mem _ (Subgroup.mem_sup_left x.1.2)
      (Subgroup.mem_sup_right x.2.2)⟩ : ↥(S ⊔ T))) ?_
  rintro ⟨y, hy⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hy
  exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩

theorem exists_decomp_minimal [Finite N] (θ : N →* N)
    (hcompl : ∀ S : Subgroup N, (∀ x ∈ S, θ x ∈ S) →
      ∃ S' : Subgroup N, (∀ x ∈ S', θ x ∈ S') ∧ S ⊓ S' = ⊥ ∧ S ⊔ S' = ⊤)
    (Y : Subgroup N) (hY : ∀ x ∈ Y, θ x ∈ Y) :
    ∃ (r : ℕ) (S : Fin r → Subgroup N), (∀ i, (∀ x ∈ S i, θ x ∈ S i) ∧ S i ≤ Y ∧ S i ≠ ⊥ ∧
      ∀ T : Subgroup N, (∀ x ∈ T, θ x ∈ T) → T ≤ S i → T = ⊥ ∨ T = S i) ∧
      (⨆ i, S i) = Y ∧ ∀ i, S i ⊓ (⨆ j, ⨆ (_ : j ≠ i), S j) = ⊥ := by
  classical
  induction hn : Nat.card Y using Nat.strong_induction_on generalizing Y with
  | _ n ih =>
  by_cases hY0 : Y = ⊥
  · refine ⟨0, Fin.elim0, fun i => i.elim0, ?_, fun i => i.elim0⟩
    rw [hY0]
    exact iSup_of_empty _
  have hex : ∃ k, ∃ T : Subgroup N, (∀ x ∈ T, θ x ∈ T) ∧ T ≤ Y ∧ T ≠ ⊥ ∧ Nat.card T = k :=
    ⟨_, Y, hY, le_rfl, hY0, rfl⟩
  obtain ⟨S₀, hS₀inv, hS₀Y, hS₀0, hS₀k⟩ := Nat.find_spec hex
  have hS₀min : ∀ T : Subgroup N, (∀ x ∈ T, θ x ∈ T) → T ≤ S₀ → T = ⊥ ∨ T = S₀ := by
    intro T hT hTS
    by_cases hT0 : T = ⊥
    · exact Or.inl hT0
    · right
      have := Nat.find_min' hex ⟨T, hT, hTS.trans hS₀Y, hT0, rfl⟩
      exact Subgroup.eq_of_le_of_card_ge hTS (hS₀k ▸ this)
  obtain ⟨S', hS'inv, hinf, hsup⟩ := hcompl S₀ hS₀inv
  set Y' := Y ⊓ S' with hY'def
  have hY'inv : ∀ x ∈ Y', θ x ∈ Y' := fun x hx => ⟨hY x hx.1, hS'inv x hx.2⟩
  have hYeq : S₀ ⊔ Y' = Y := by
    rw [hY'def, inf_comm, ← sup_inf_assoc_of_le S' hS₀Y, hsup, top_inf_eq]
  have hdisj : S₀ ⊓ Y' = ⊥ := by
    rw [eq_bot_iff, ← hinf]
    exact inf_le_inf_left _ inf_le_right
  have hlt : Nat.card Y' < n := by
    rw [← hn]
    refine Subgroup.card_lt_of_lt (lt_of_le_of_ne inf_le_left fun h => hS₀0 ?_)
    rw [← inf_eq_left.2 (hS₀Y.trans h.ge), hdisj]
  obtain ⟨r, S, hS, hSsup, hSind⟩ := ih _ hlt Y' hY'inv rfl
  refine ⟨r + 1, Fin.cons S₀ S, fun i => ?_, ?_, fun i => ?_⟩
  · refine Fin.cases ?_ (fun j => ?_) i
    · exact ⟨hS₀inv, hS₀Y, hS₀0, hS₀min⟩
    · obtain ⟨h1, h2, h3, h4⟩ := hS j
      exact ⟨h1, h2.trans inf_le_left, h3, h4⟩
  · apply le_antisymm
    · exact iSup_le fun i => Fin.cases hS₀Y (fun j => (hS j).2.1.trans inf_le_left) i
    · rw [← hYeq, ← hSsup]
      exact sup_le (le_iSup_of_le 0 le_rfl) (iSup_le fun j => le_iSup_of_le j.succ le_rfl)
  · refine Fin.cases ?_ (fun k => ?_) i
    · rw [Fin.cons_zero, eq_bot_iff, ← hdisj]
      refine inf_le_inf_left _ (iSup₂_le fun j hj => ?_)
      obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.2 hj
      rw [Fin.cons_succ, ← hSsup]
      exact le_iSup_of_le j' le_rfl
    · set R := ⨆ l, ⨆ (_ : l ≠ k), S l with hR
      have hRY' : R ≤ Y' := by
        rw [← hSsup]
        exact iSup₂_le fun l _ => le_iSup_of_le l le_rfl
      have hle : (⨆ j, ⨆ (_ : j ≠ k.succ), (Fin.cons S₀ S : Fin (r + 1) → Subgroup N) j) ≤
          S₀ ⊔ R := by
        refine iSup₂_le fun j hj => ?_
        induction j using Fin.cases with
        | zero => rw [Fin.cons_zero]; exact le_sup_left
        | succ l =>
          rw [Fin.cons_succ]
          have hlk : l ≠ k := fun h => hj (by rw [h])
          have hlR : S l ≤ R := by
            rw [hR]
            exact le_iSup₂_of_le l hlk le_rfl
          exact hlR.trans le_sup_right
      have hmod : Y' ⊓ (S₀ ⊔ R) = R := by
        rw [inf_comm, sup_comm, sup_inf_assoc_of_le S₀ hRY', hdisj, sup_bot_eq]
      rw [Fin.cons_succ, eq_bot_iff, ← hSind k]
      calc S k ⊓ (⨆ j, ⨆ (_ : j ≠ k.succ), (Fin.cons S₀ S : Fin (r + 1) → Subgroup N) j) ≤
          S k ⊓ (Y' ⊓ (S₀ ⊔ R)) :=
            le_inf inf_le_left (le_inf (inf_le_left.trans (hS k).2.1) (inf_le_right.trans hle))
        _ = S k ⊓ R := by rw [hmod]

theorem card_eq_sq_card_inf [Finite N] (hsq : ∀ x : N, x * x = 1) {γ τ : MulAut N}
    (hτ : τ * τ = 1) (hτγ : τ * γ * τ⁻¹ = γ⁻¹) (hfree : fixSub γ = ⊥) {X : Subgroup N}
    (hγX : ∀ u ∈ X, γ u ∈ X) (hτX : ∀ u ∈ X, τ u ∈ X) :
    Nat.card X = Nat.card ↥(X ⊓ fixSub τ) ^ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2N : IsPGroup 2 N := fun x => ⟨1, by rw [pow_one, pow_two]; exact hsq x⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (h2N.to_subgroup X)
  have hτinv : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ
  have hτγ2 : (τ * γ) * (τ * γ) = 1 := by
    have e : (τ * γ) * (τ * γ) = (τ * γ * τ⁻¹) * γ := by
      rw [hτinv]
      simp only [mul_assoc]
    rw [e, hτγ, inv_mul_cancel]
  have hτγX : ∀ u ∈ X, (τ * γ) u ∈ X := fun u hu => by
    rw [MulAut.mul_apply]
    exact hτX _ (hγX u hu)
  have h1 := card_le_sq_card_fixSub mul_comm hsq hτ hτX
  have h2 := card_le_sq_card_fixSub mul_comm hsq hτγ2 hτγX
  have hF : (X ⊓ fixSub τ) ⊓ (X ⊓ fixSub (τ * γ)) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨-, hx1⟩, -, hx2⟩
    replace hx1 : τ x = x := hx1
    replace hx2 : τ (γ x) = x := hx2
    have hγx : γ x = x := by
      calc γ x = (τ * τ) (γ x) := by rw [hτ, MulAut.one_apply]
        _ = τ (τ (γ x)) := by rw [MulAut.mul_apply]
        _ = x := by rw [hx2, hx1]
    have hx : x ∈ fixSub γ := hγx
    rwa [hfree] at hx
  have h3 := card_mul_card_le (inf_le_left : X ⊓ fixSub τ ≤ X)
    (inf_le_left : X ⊓ fixSub (τ * γ) ≤ X) hF
  obtain ⟨f₁, hf₁⟩ := IsPGroup.iff_card.mp (h2N.to_subgroup (X ⊓ fixSub τ))
  obtain ⟨f₂, hf₂⟩ := IsPGroup.iff_card.mp (h2N.to_subgroup (X ⊓ fixSub (τ * γ)))
  rw [hm, hf₁, ← pow_mul] at h1
  rw [hm, hf₂, ← pow_mul] at h2
  rw [hm, hf₁, hf₂, ← pow_add] at h3
  have e1 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h1
  have e2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h2
  have e3 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h3
  rw [hm, hf₁, ← pow_mul]
  congr 1
  omega

theorem sup_map_inv (hsq : ∀ x : N, x * x = 1) {γ τ : MulAut N} (hτγ : τ * γ * τ⁻¹ = γ⁻¹)
    {T : Subgroup N} (hT : ∀ x ∈ T, thetaHom γ x ∈ T) (hTN : T ≤ fixSub τ) :
    (∀ u ∈ T ⊔ T.map γ.toMonoidHom, γ u ∈ T ⊔ T.map γ.toMonoidHom) ∧
      (∀ u ∈ T ⊔ T.map γ.toMonoidHom, τ u ∈ T ⊔ T.map γ.toMonoidHom) := by
  have hinv : ∀ x : N, x⁻¹ = x := fun x => inv_eq_of_mul_eq_one_right (hsq x)
  have hmap : ∀ s ∈ T, γ s ∈ T.map γ.toMonoidHom := fun s hs => ⟨s, hs, rfl⟩
  have h1 : τ * γ = γ⁻¹ * τ := by rw [← hτγ, inv_mul_cancel_right]
  constructor
  · intro u hu
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hu
    obtain ⟨s, hs, rfl⟩ := hb
    have e : γ (γ s) = γ (thetaHom γ s) * s := by
      rw [thetaHom_apply, map_mul, MulAut.apply_inv_self, mul_assoc, hsq, mul_one]
    change γ (a * γ s) ∈ _
    rw [map_mul, e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (hmap a ha))
      (Subgroup.mul_mem _ (Subgroup.mem_sup_right (hmap _ (hT s hs))) (Subgroup.mem_sup_left hs))
  · intro u hu
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hu
    obtain ⟨s, hs, rfl⟩ := hb
    have hτa : τ a = a := hTN ha
    have hτs : τ s = s := hTN hs
    have e : τ (γ s) = thetaHom γ s * γ s := by
      rw [← MulAut.mul_apply, h1, MulAut.mul_apply, hτs, thetaHom_apply, mul_comm (γ s),
        mul_assoc, hsq, mul_one]
    change τ (a * γ s) ∈ _
    rw [map_mul, hτa, e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ha)
      (Subgroup.mul_mem _ (Subgroup.mem_sup_left (hT s hs)) (Subgroup.mem_sup_right (hmap s hs)))

theorem exists_decomp [Finite N] (hsq : ∀ x : N, x * x = 1) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {γ τ : MulAut N} (hγ : orderOf γ = p) (hτ : τ * τ = 1)
    (hτγ : τ * γ * τ⁻¹ = γ⁻¹) (hfree : fixSub γ = ⊥) :
    ∃ (r : ℕ) (U : Fin r → Subgroup N),
      (∀ i, (∀ u ∈ U i, γ u ∈ U i) ∧ (∀ u ∈ U i, τ u ∈ U i) ∧
        Nat.card (U i) = 2 ^ (2 * E2.dParamPrime p) ∧
        ∀ Y : Subgroup N, Y ≤ U i → (∀ u ∈ Y, γ u ∈ Y) → (∀ u ∈ Y, τ u ∈ Y) →
          Y = ⊥ ∨ Y = U i) ∧
      (⨆ i, U i) = ⊤ ∧ ∀ i, U i ⊓ (⨆ j, ⨆ (_ : j ≠ i), U j) = ⊥ := by
  set θ := thetaHom γ with hθdef
  set N₀ := fixSub τ with hN₀
  have hd' : E2.dParamPrime p ≠ 0 := dParamPrime_ne_zero hp hp2
  have hθq : ∀ x, θ^[2 ^ E2.dParamPrime p] x = θ x := iterate_theta_eq hsq hp hγ
  have hθN₀ : ∀ x ∈ N₀, θ x ∈ N₀ := fun x hx => by
    have hx' : τ x = x := hx
    change τ (θ x) = θ x
    rw [thetaHom_comm hτγ, hx']
  obtain ⟨r, S, hS, hSsup, hSind⟩ := exists_decomp_minimal θ
    (fun T hT => exists_compl_of_iterate hsq θ hd' hθq hT) N₀ hθN₀
  have hγinv : ∀ X : Subgroup N, (∀ u ∈ X, γ u ∈ X) → ∀ u ∈ X, γ⁻¹ u ∈ X := by
    intro X hX u hu
    have hγp : γ⁻¹ = γ ^ (p - 1) := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, Nat.sub_add_cancel hp.one_lt.le, ← hγ,
        pow_orderOf_eq_one]
    rw [hγp]
    exact pow_apply_mem hX (p - 1) u hu
  have hfr : ∀ X : Subgroup N, (∀ u ∈ X, γ u ∈ X) → (∀ u ∈ X, τ u ∈ X) →
      Nat.card X = Nat.card ↥(X ⊓ N₀) ^ 2 :=
    fun X h1 h2 => card_eq_sq_card_inf hsq hτ hτγ hfree h1 h2
  have hYθ : ∀ Y : Subgroup N, (∀ u ∈ Y, γ u ∈ Y) → ∀ x ∈ Y ⊓ N₀, θ x ∈ Y ⊓ N₀ :=
    fun Y hY x hx => ⟨Y.mul_mem (hY x hx.1) (hγinv Y hY x hx.1), hθN₀ x hx.2⟩
  set U : Fin r → Subgroup N := fun i => S i ⊔ (S i).map γ.toMonoidHom with hUdef
  have hUinv : ∀ i, (∀ u ∈ U i, γ u ∈ U i) ∧ (∀ u ∈ U i, τ u ∈ U i) := fun i =>
    sup_map_inv hsq hτγ (hS i).1 (hS i).2.1
  have hcardS : ∀ i, Nat.card (S i) ≤ 2 ^ E2.dParamPrime p := fun i =>
    card_le_of_minimal_mul hsq θ hd' hθq (hS i).1 (hS i).2.2.1 (hS i).2.2.2
  have hcardU_le : ∀ i, Nat.card (U i) ≤ Nat.card (S i) ^ 2 := fun i => by
    have := card_sup_le (S i) ((S i).map γ.toMonoidHom)
    rwa [Subgroup.card_map_of_injective γ.injective, ← sq] at this
  have hcardU_ge : ∀ i, 2 ^ (2 * E2.dParamPrime p) ≤ Nat.card (U i) := fun i => by
    have hU1 : U i ≠ ⊥ := by
      intro h
      have hSU : S i ≤ U i := le_sup_left
      rw [h] at hSU
      exact (hS i).2.2.1 (eq_bot_iff.2 hSU)
    have := two_pow_le_card_of_free mul_comm hsq hp le_rfl (γ := γ) (τ := τ)
      (by rw [pow_one]; exact hγ) hτ hτγ hU1 (hUinv i).1 (hUinv i).2
      (by rw [Nat.sub_self, pow_zero, pow_one, hfree, inf_bot_eq])
    rwa [pow_one] at this
  have hUN : ∀ i, U i ⊓ N₀ = S i := fun i => by
    have hle : S i ≤ U i ⊓ N₀ := le_inf le_sup_left (hS i).2.1
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    have h2 := hcardU_le i
    rw [hfr (U i) (hUinv i).1 (hUinv i).2] at h2
    exact (Nat.pow_le_pow_iff_left two_ne_zero).1 h2
  have hirr : ∀ i (Y : Subgroup N), Y ≤ U i → (∀ u ∈ Y, γ u ∈ Y) → (∀ u ∈ Y, τ u ∈ Y) →
      Y = ⊥ ∨ Y = U i := by
    intro i Y hYU hγY hτY
    have hYN : Y ⊓ N₀ ≤ S i := by
      rw [← hUN i]
      exact inf_le_inf_right _ hYU
    rcases (hS i).2.2.2 _ (hYθ Y hγY) hYN with h | h
    · left
      have := hfr Y hγY hτY
      rw [h, Subgroup.card_bot, one_pow] at this
      exact Subgroup.card_eq_one.1 this
    · right
      have hSY : S i ≤ Y := by
        rw [← h]
        exact inf_le_left
      refine le_antisymm hYU (sup_le hSY ?_)
      rw [Subgroup.map_le_iff_le_comap]
      intro x hx
      exact hγY x (hSY hx)
  have hsupU : (⨆ i, U i) = ⊤ := by
    set X := ⨆ i, U i with hX
    have hγX : ∀ u ∈ X, γ u ∈ X := by
      intro u hu
      refine Subgroup.iSup_induction U (C := fun u => γ u ∈ X) hu (fun i x hx => ?_) ?_ ?_
      · exact Subgroup.mem_iSup_of_mem i ((hUinv i).1 x hx)
      · rw [map_one]
        exact X.one_mem
      · intro x y hx hy
        rw [map_mul]
        exact X.mul_mem hx hy
    have hτX : ∀ u ∈ X, τ u ∈ X := by
      intro u hu
      refine Subgroup.iSup_induction U (C := fun u => τ u ∈ X) hu (fun i x hx => ?_) ?_ ?_
      · exact Subgroup.mem_iSup_of_mem i ((hUinv i).2 x hx)
      · rw [map_one]
        exact X.one_mem
      · intro x y hx hy
        rw [map_mul]
        exact X.mul_mem hx hy
    have hN₀X : N₀ ≤ X := by
      rw [← hSsup]
      exact iSup_mono fun i => le_sup_left
    have htop : Nat.card N = Nat.card ↥N₀ ^ 2 := by
      rw [← Subgroup.card_top, hfr ⊤ (fun u _ => Subgroup.mem_top _)
        (fun u _ => Subgroup.mem_top _), top_inf_eq]
    apply Subgroup.eq_top_of_card_eq
    rw [hfr X hγX hτX, inf_eq_right.2 hN₀X, htop]
  have hind : ∀ i, U i ⊓ (⨆ j, ⨆ (_ : j ≠ i), U j) = ⊥ := by
    intro i
    set R := ⨆ j, ⨆ (_ : j ≠ i), U j with hR
    set Ti := ⨆ j, ⨆ (_ : j ≠ i), S j with hTi
    have hUR : ∀ j, j ≠ i → U j ≤ R := fun j hj => by
      rw [hR]
      exact le_iSup₂_of_le j hj le_rfl
    have hSTi : ∀ j, j ≠ i → S j ≤ Ti := fun j hj => by
      rw [hTi]
      exact le_iSup₂_of_le j hj le_rfl
    have hγR : ∀ u ∈ R, γ u ∈ R := by
      have hle : R ≤ R.comap γ.toMonoidHom := by
        rw [hR]
        exact iSup₂_le fun j hj u hu => hUR j hj ((hUinv j).1 u hu)
      exact fun u hu => hle hu
    have hτR : ∀ u ∈ R, τ u ∈ R := by
      have hle : R ≤ R.comap τ.toMonoidHom := by
        rw [hR]
        exact iSup₂_le fun j hj u hu => hUR j hj ((hUinv j).2 u hu)
      exact fun u hu => hle hu
    have hTiR : Ti ≤ R ⊓ N₀ := by
      refine le_inf ?_ ?_
      · rw [hTi]
        exact iSup₂_le fun j hj => le_sup_left.trans (hUR j hj)
      · rw [hTi]
        exact iSup₂_le fun j _ => (hS j).2.1
    have hRT : R ≤ Ti ⊔ Ti.map γ.toMonoidHom := by
      rw [hR]
      refine iSup₂_le fun j hj => sup_le ?_ ?_
      · exact le_sup_of_le_left (hSTi j hj)
      · exact le_sup_of_le_right (Subgroup.map_mono (hSTi j hj))
    have hRN : R ⊓ N₀ = Ti := by
      refine (Subgroup.eq_of_le_of_card_ge hTiR ?_).symm
      have h2 : Nat.card R ≤ Nat.card Ti ^ 2 := by
        calc Nat.card R ≤ Nat.card ↥(Ti ⊔ Ti.map γ.toMonoidHom) := Subgroup.card_le_of_le hRT
          _ ≤ Nat.card Ti * Nat.card ↥(Ti.map γ.toMonoidHom) := card_sup_le _ _
          _ = Nat.card Ti ^ 2 := by rw [Subgroup.card_map_of_injective γ.injective, sq]
      rw [hfr R hγR hτR] at h2
      exact (Nat.pow_le_pow_iff_left two_ne_zero).1 h2
    have hYγ : ∀ u ∈ U i ⊓ R, γ u ∈ U i ⊓ R := fun u hu => ⟨(hUinv i).1 u hu.1, hγR u hu.2⟩
    have hYτ : ∀ u ∈ U i ⊓ R, τ u ∈ U i ⊓ R := fun u hu => ⟨(hUinv i).2 u hu.1, hτR u hu.2⟩
    have hYN : (U i ⊓ R) ⊓ N₀ = ⊥ := by
      rw [eq_bot_iff, ← hSind i]
      calc (U i ⊓ R) ⊓ N₀ ≤ (U i ⊓ N₀) ⊓ (R ⊓ N₀) :=
            le_inf (inf_le_inf_right _ inf_le_left) (inf_le_inf_right _ inf_le_right)
        _ = S i ⊓ Ti := by rw [hUN i, hRN]
    have := hfr _ hYγ hYτ
    rw [hYN, Subgroup.card_bot, one_pow] at this
    exact Subgroup.card_eq_one.1 this
  refine ⟨r, U, fun i => ⟨(hUinv i).1, (hUinv i).2, le_antisymm ?_ (hcardU_ge i), hirr i⟩,
    hsupU, hind⟩
  calc Nat.card (U i) ≤ Nat.card (S i) ^ 2 := hcardU_le i
    _ ≤ (2 ^ E2.dParamPrime p) ^ 2 := Nat.pow_le_pow_left (hcardS i) 2
    _ = 2 ^ (2 * E2.dParamPrime p) := by rw [← pow_mul, mul_comm]

end Decomp

end Dih

end CFSG.Quasithin.SimsE2
