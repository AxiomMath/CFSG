module

public import CFSG.LieType.BorelTits.FormFlag

public section

namespace CFSG.RankThree.PartTwo.Sec21.AS76

open Module CFSG.LieType.BorelTits

section Groups

variable {X Y : Type*} [Group X] [Group Y]

@[expose] def InvFixThree (X : Type*) [Group X] : Prop :=
  ∀ φ : MulAut X, orderOf φ = 2 → ∃ y : X, orderOf y = 3 ∧ φ y = y

theorem InvFixThree.of_mulEquiv (e : X ≃* Y) (h : InvFixThree Y) : InvFixThree X := by
  intro φ hφ
  obtain ⟨y, hy, hφy⟩ := h (MulAut.congr e φ) (by rw [MulEquiv.orderOf_eq]; exact hφ)
  refine ⟨e.symm y, by rw [MulEquiv.orderOf_eq]; exact hy, ?_⟩
  rw [MulAut.congr_apply] at hφy
  have h1 := congrArg e.symm hφy
  simpa using h1

@[expose] def InvCentThree (G : Type*) [Group G] : Prop :=
  ∀ t : G, t * t = 1 → ∃ y : G, orderOf y = 3 ∧ y * t = t * y

theorem InvCentThree.of_mulEquiv (e : X ≃* Y) (h : InvCentThree X) : InvCentThree Y := by
  intro t ht
  obtain ⟨y, hy, hyt⟩ := h (e.symm t) (by rw [← map_mul, ht, map_one])
  refine ⟨e y, by rw [MulEquiv.orderOf_eq]; exact hy, ?_⟩
  have h1 := congrArg e hyt
  rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h1

theorem conj_fix (hZ : Subgroup.center X = ⊥) (h : InvCentThree X) (x : X)
    (hx : orderOf (MulAut.conj x) = 2) : ∃ y : X, orderOf y = 3 ∧ MulAut.conj x y = y := by
  have h2 : MulAut.conj (x * x) = 1 := by rw [map_mul, ← sq, ← hx, pow_orderOf_eq_one]
  have hxx : x * x = 1 := by
    have hmem : x * x ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h3 := congrArg (fun φ : MulAut X => φ g) h2
      simp only [MulAut.conj_apply, MulAut.one_apply] at h3
      calc g * (x * x) = (x * x) * g * (x * x)⁻¹ * (x * x) := by rw [h3]
        _ = (x * x) * g := by group
    rwa [hZ, Subgroup.mem_bot] at hmem
  obtain ⟨y, hy, hyx⟩ := h x hxx
  refine ⟨y, hy, ?_⟩
  rw [MulAut.conj_apply, ← hyx, mul_inv_cancel_right]

theorem fix_of_conj {φ ψ τ : MulAut X} (hφ : φ = ψ * τ * ψ⁻¹) {y : X} (hy : τ y = y) :
    φ (ψ y) = ψ y := by
  rw [hφ, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply, hy]

end Groups

section Ring

variable {R : Type*} [Ring R]

theorem one_add_mul_self (h2 : (2 : R) = 0) {X : R} (hX : X * X = 0) :
    (1 + X) * (1 + X) = 1 := by
  have h : (1 + X) * (1 + X) = 1 + 2 * X + X * X := by noncomm_ring
  rw [h, h2, hX, zero_mul, add_zero, add_zero]

theorem braid (h2 : (2 : R) = 0) {X X' : R} (hX : X * X = 0) (hX' : X' * X' = 0)
    (h1 : X * X' * X = X) (h1' : X' * X * X' = X') :
    (1 + X) * (1 + X') * (1 + X) = (1 + X') * (1 + X) * (1 + X') := by
  have hL : (1 + X) * (1 + X') * (1 + X) =
      1 + X + X' + X * X' + X' * X + (2 * X + X * X + (X * X' * X - X)) := by noncomm_ring
  have hR : (1 + X') * (1 + X) * (1 + X') =
      1 + X + X' + X * X' + X' * X + (2 * X' + X' * X' + (X' * X * X' - X')) := by noncomm_ring
  rw [hL, hR, h1, h1', hX, hX', h2, zero_mul, zero_mul, sub_self, sub_self]

theorem cube_eq_one (h2 : (2 : R) = 0) {X X' : R} (hX : X * X = 0) (hX' : X' * X' = 0)
    (h1 : X * X' * X = X) (h1' : X' * X * X' = X') : ((1 + X) * (1 + X')) ^ 3 = 1 := by
  have ha := one_add_mul_self h2 hX
  have hb := one_add_mul_self h2 hX'
  have hab := braid h2 hX hX' h1 h1'
  set a := 1 + X
  set b := 1 + X'
  calc (a * b) ^ 3 = (a * b * a) * (b * a * b) := by rw [pow_three]; simp only [mul_assoc]
    _ = (b * a * b) * (b * a * b) := by rw [hab]
    _ = b * a * (b * b) * a * b := by simp only [mul_assoc]
    _ = 1 := by rw [hb, mul_one, mul_assoc b a a, ha, mul_one, hb]

theorem ne_one (h2 : (2 : R) = 0) {X X' : R} (hX : X * X = 0) (h1 : X * X' * X = X)
    (hX0 : X ≠ 0) : (1 + X) * (1 + X') ≠ 1 := by
  intro h
  have h3 : 1 + X' = 1 + X := by
    calc 1 + X' = (1 + X) * (1 + X) * (1 + X') := by rw [one_add_mul_self h2 hX, one_mul]
      _ = (1 + X) * ((1 + X) * (1 + X')) := by rw [mul_assoc]
      _ = 1 + X := by rw [h, mul_one]
  have hXX : X' = X := add_left_cancel h3
  apply hX0
  rw [← h1, hXX, hX, zero_mul]

theorem commute_prod {X X' N : R} (hc : X * N = N * X) (hc' : X' * N = N * X') :
    (1 + X) * (1 + X') * N = N * ((1 + X) * (1 + X')) :=
  (((Commute.one_left N).add_left hc).mul_left ((Commute.one_left N).add_left hc') : _)

theorem end_two_eq_zero {K V : Type*} [Field K] [CharP K 2] [AddCommGroup V] [Module K V] :
    (2 : Module.End K V) = 0 := by
  ext v
  rw [← one_add_one_eq_two, LinearMap.add_apply, Module.End.one_apply, LinearMap.zero_apply,
    ← two_smul K v, CharTwo.two_eq_zero, zero_smul]

theorem eq_one_of_mul_self {K : Type*} [Field K] [CharP K 2] {d : K} (h : d * d = 1) : d = 1 := by
  have h0 : (d + 1) * (d + 1) = 0 := by
    linear_combination h + (d + 1) * CharTwo.two_eq_zero (R := K)
  have h1 := mul_self_eq_zero.mp h0
  linear_combination h1 - CharTwo.two_eq_zero (R := K)

theorem det_one_add_mul_one_add {K V : Type*} [Field K] [CharP K 2] [AddCommGroup V]
    [Module K V] {X X' : Module.End K V} (hX : X * X = 0) (hX' : X' * X' = 0) :
    LinearMap.det ((1 + X) * (1 + X')) = 1 := by
  have h2 : (2 : Module.End K V) = 0 := end_two_eq_zero
  have hd : ∀ Z : Module.End K V, Z * Z = 0 → LinearMap.det (1 + Z) = 1 := fun Z hZ =>
    eq_one_of_mul_self (by rw [← map_mul, one_add_mul_self h2 hZ, map_one])
  rw [map_mul, hd X hX, hd X' hX', one_mul]

end Ring

section Sqrt

variable {K V : Type*} [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem exists_ker_sqrt (Q : V → K) (hadd : ∀ u v, Q (u + v) = Q u + Q v)
    (hsmul : ∀ (c : K) (v : V), Q (c • v) = c ^ 2 * Q v) :
    ∃ H : Submodule K V, (∀ v, v ∈ H ↔ Q v = 0) ∧ finrank K V ≤ finrank K H + 1 := by
  set s := (frobeniusEquiv K 2).symm with hs
  have hsq : ∀ c : K, s (c ^ 2) = c := fun c => by
    have h := frobeniusEquiv_symm_apply_frobenius K 2 c
    rwa [frobenius_def] at h
  let lam : V →ₗ[K] K :=
    { toFun := fun v => s (Q v)
      map_add' := fun u v => by simp only [hadd, map_add]
      map_smul' := fun c v => by rw [hsmul, map_mul, hsq, RingHom.id_apply, smul_eq_mul] }
  refine ⟨LinearMap.ker lam, fun v => ?_, ?_⟩
  · rw [LinearMap.mem_ker]
    change s (Q v) = 0 ↔ Q v = 0
    exact map_eq_zero_iff s s.injective
  · have h1 := LinearMap.finrank_range_add_finrank_ker lam
    have h2 : finrank K (LinearMap.range lam) ≤ 1 := by
      have h3 := Submodule.finrank_le (LinearMap.range lam)
      rwa [Module.finrank_self] at h3
    omega

end Sqrt

section Forms

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem exists_eq_one [FiniteDimensional K V] (F : ReflForm K V) (M : V →ₗ[K] V)
    (H : Submodule K V) (hH : finrank K V ≤ finrank K H + 1) (hM : 2 ≤ finrank K (H.map M)) :
    ∃ u ∈ H, ∃ u' ∈ H, F.β u (M u') = 1 := by
  by_contra hne
  push Not at hne
  have hle : H.map M ≤ F.perp H := by
    rintro _ ⟨u', hu', rfl⟩ u hu
    by_contra hc
    apply hne u hu ((F.β u (M u'))⁻¹ • u') (H.smul_mem _ hu')
    rw [map_smul, F.smul_right, inv_mul_cancel₀ hc]
  have h1 := Submodule.finrank_mono hle
  have h2 := F.finrank_perp H
  omega

@[expose] def tv (F : ReflForm K V) (e : V) : Module.End K V where
  toFun v := F.β e v • e
  map_add' u v := by rw [F.add_right, add_smul]
  map_smul' c v := by rw [F.smul_right, smul_smul, RingHom.id_apply]

theorem tv_apply (F : ReflForm K V) (e v : V) : tv F e v = F.β e v • e := rfl

theorem tv_mul_self (F : ReflForm K V) {e : V} (he : F.β e e = 0) : tv F e * tv F e = 0 := by
  ext v
  rw [Module.End.mul_apply, tv_apply, tv_apply, F.smul_right, he, mul_zero, zero_smul,
    LinearMap.zero_apply]

theorem tv_mul_tv_mul_tv (F : ReflForm K V) {e e' : V} (h : F.β e e' * F.β e' e = 1) :
    tv F e * tv F e' * tv F e = tv F e := by
  ext v
  simp only [Module.End.mul_apply, tv_apply, F.smul_right]
  rw [mul_assoc, mul_comm (F.β e' e) (F.β e e'), h, mul_one]

theorem tv_ne_zero (F : ReflForm K V) {e e' : V} (h : F.β e e' = 1) : tv F e ≠ 0 := by
  intro h0
  have h1 := congrArg (fun T : Module.End K V => T e') h0
  simp only [tv_apply, h, one_smul, LinearMap.zero_apply] at h1
  rw [h1, F.β_zero_left] at h
  exact zero_ne_one h

theorem tv_commute (F : ReflForm K V) {e : V} (N : Module.End K V) (hNe : N e = 0)
    (hN : ∀ v, F.β e (N v) = 0) : tv F e * N = N * tv F e := by
  ext v
  rw [Module.End.mul_apply, Module.End.mul_apply, tv_apply, tv_apply, hN, zero_smul, map_smul, hNe,
    smul_zero]

theorem tv_isometry [CharP K 2] (F : ReflForm K V) (hσ : ∀ c, F.σ c = c)
    (hsymm : ∀ u v, F.β u v = F.β v u) {e : V} (he : F.β e e = 0) (u v : V) :
    F.β ((1 + tv F e) u) ((1 + tv F e) v) = F.β u v := by
  simp only [LinearMap.add_apply, Module.End.one_apply, tv_apply, F.add_left, F.add_right,
    F.smul_left, F.smul_right, hσ, he]
  rw [hsymm u e]
  linear_combination (F.β e u * F.β e v) * CharTwo.two_eq_zero (R := K)

end Forms

section Basis

variable {ι K V : Type*} [Field K] [AddCommGroup V] [Module K V]

@[expose] noncomputable def bE (b : Basis ι K V) (a c : ι) : Module.End K V :=
  (b.coord c).smulRight (b a)

theorem bE_apply (b : Basis ι K V) (a c : ι) (v : V) : bE b a c v = b.coord c v • b a := rfl

theorem bE_basis [DecidableEq ι] (b : Basis ι K V) (a c k : ι) :
    bE b a c (b k) = if k = c then b a else 0 := by
  rw [bE_apply, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
  split_ifs <;> simp

theorem bE_mul_bE [DecidableEq ι] (b : Basis ι K V) (a c c' d : ι) :
    bE b a c * bE b c' d = if c' = c then bE b a d else 0 := by
  ext v
  rw [Module.End.mul_apply, bE_apply b c' d, map_smul, bE_basis]
  split_ifs <;> simp [bE_apply]

end Basis

end CFSG.RankThree.PartTwo.Sec21.AS76
