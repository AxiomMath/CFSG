module

public import CFSG.Quasithin.Recognition.CertF8
public import CFSG.LocalAnalysis.UniquenessCase.UCHigmanSL2
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.RepresentationTheory.SL2NatSum

open CFSG.Quasithin (GF8)
open CFSG.LocalAnalysis.UniquenessCase.UCK.Higman
open Matrix
open scoped MatrixGroups

private def Q {K : Type} [Field K] [CharP K 2] {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] (ρ : Representation (ZMod 2) SL(2, K) V) (x y : K) : Prop :=
  ∀ v : V, ρ (uMat y) (ρ (uMat x) v - v) = ρ (uMat x) v - v

private def R {K : Type} [Field K] [CharP K 2] {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] (ρ : Representation (ZMod 2) SL(2, K) V) (x y : K) : Prop :=
  ∀ v : V, ρ (uMat x * uMat y) v + ρ (uMat y) v + ρ (uMat x) v + v = 0

private theorem add_eq_zero_iff_eq {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {a b : V} : a + b = 0 ↔ a = b := by
  constructor
  · intro h
    calc
      a = a + (b + b) := by rw [ZModModule.add_self, add_zero]
      _ = (a + b) + b := by abel
      _ = b := by rw [h, zero_add]
  · intro h
    rw [h, ZModModule.add_self]

private theorem rho_uMat_mul_apply {K : Type} [Field K] [CharP K 2]
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL(2, K) V) (x y : K) (v : V) :
    ρ (uMat y) (ρ (uMat x) v) = ρ (uMat x * uMat y) v := by
  rw [← Module.End.mul_apply, ← map_mul, uMat_mul, uMat_mul, add_comm]

private theorem rho_uMat_sub_apply {K : Type} [Field K] [CharP K 2]
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL(2, K) V) (x y : K) (v : V) :
    ρ (uMat y) (ρ (uMat x) v - v) = ρ (uMat x * uMat y) v + ρ (uMat y) v := by
  rw [map_sub, rho_uMat_mul_apply, ZModModule.sub_eq_add]

private theorem R_iff_Q {K : Type} [Field K] [CharP K 2]
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL(2, K) V) (x y : K) : R ρ x y ↔ Q ρ x y := by
  unfold R Q
  constructor
  · intro h v
    have hsum := h v
    have hfour : ρ (uMat x * uMat y) v + ρ (uMat y) v + ρ (uMat x) v + v =
        (ρ (uMat x * uMat y) v + ρ (uMat y) v) + (ρ (uMat x) v + v) := by abel
    have hsplit : ρ (uMat x * uMat y) v + ρ (uMat y) v = ρ (uMat x) v + v := by
      apply (add_eq_zero_iff_eq).1
      rwa [hfour] at hsum
    rw [rho_uMat_sub_apply, ZModModule.sub_eq_add]
    exact hsplit
  · intro h v
    have hv := h v
    rw [rho_uMat_sub_apply, ZModModule.sub_eq_add] at hv
    rw [show ρ (uMat x * uMat y) v + ρ (uMat y) v + ρ (uMat x) v + v =
      (ρ (uMat x * uMat y) v + ρ (uMat y) v) + (ρ (uMat x) v + v) by abel,
      hv, ZModModule.add_self]

private noncomputable def P {K : Type} [Field K] [CharP K 2]
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL(2, K) V) (x : K) : V →ₗ[ZMod 2] V :=
  ρ (uMat x) - 1

private def Qo {K : Type} [Field K] [CharP K 2]
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL(2, K) V) (x y : K) : Prop :=
  P ρ y * P ρ x = 0

private theorem P_apply_eq_zero_iff {K : Type} [Field K] [CharP K 2]
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL(2, K) V) (x y : K) (v : V) :
    P ρ y (P ρ x v) = 0 ↔ ρ (uMat y) (ρ (uMat x) v - v) = ρ (uMat x) v - v := by
  rw [P, P, LinearMap.sub_apply, LinearMap.sub_apply, Module.End.one_apply]
  exact sub_eq_zero

private theorem Q_iff_Qo {K : Type} [Field K] [CharP K 2]
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL(2, K) V) (x y : K) : Q ρ x y ↔ Qo ρ x y := by
  have hiff : ∀ v : V, (ρ (uMat y) (ρ (uMat x) v - v) = ρ (uMat x) v - v) ↔
      (P ρ y (P ρ x v) = 0) := by
    intro v
    exact (P_apply_eq_zero_iff ρ x y v).symm
  unfold Q Qo
  rw [LinearMap.ext_iff]
  simp only [Module.End.mul_apply]
  exact forall_congr' fun v => hiff v

private theorem P_add {K : Type} [Field K] [CharP K 2]
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL(2, K) V) (x y : K) :
    P ρ (x + y) = P ρ x + P ρ y + P ρ x * P ρ y := by
  have h : uMat (x + y) = uMat x * uMat y := (uMat_mul x y).symm
  simp only [P, h, map_mul]
  noncomm_ring

private theorem P_zero {K : Type} [Field K] [CharP K 2]
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL(2, K) V) : P ρ 0 = 0 := by
  simp [P, uMat_zero]

private theorem P_self {K : Type} [Field K] [CharP K 2]
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL(2, K) V) (x : K) : P ρ x * P ρ x = 0 := by
  have hA : ρ (uMat x) * ρ (uMat x) = 1 := by
    rw [← map_mul, uMat_two, map_one]
  have hAA : ρ (uMat x) + ρ (uMat x) = 0 := by
    ext v
    simpa using ZModModule.add_self (ρ (uMat x) v)
  have h11 : (1 : V →ₗ[ZMod 2] V) + 1 = 0 := by
    ext v
    simpa using ZModModule.add_self v
  simp only [P]
  calc
    (ρ (uMat x) - 1) * (ρ (uMat x) - 1)
        = ρ (uMat x) * ρ (uMat x) - ρ (uMat x) - ρ (uMat x) + 1 := by noncomm_ring
    _ = 1 - ρ (uMat x) - ρ (uMat x) + 1 := by rw [hA]
    _ = 1 - (ρ (uMat x) + ρ (uMat x)) + 1 := by rw [sub_sub]
    _ = 1 - 0 + 1 := by rw [hAA]
    _ = 1 + 1 := by rw [sub_zero]
    _ = 0 := h11

private theorem P_comm {K : Type} [Field K] [CharP K 2]
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL(2, K) V) (x y : K) :
    P ρ x * P ρ y = P ρ y * P ρ x := by
  have hAB : ρ (uMat x) * ρ (uMat y) = ρ (uMat y) * ρ (uMat x) := by
    rw [← map_mul, ← map_mul, uMat_mul, uMat_mul, add_comm]
  simp only [P]
  calc
    (ρ (uMat x) - 1) * (ρ (uMat y) - 1)
        = ρ (uMat x) * ρ (uMat y) - ρ (uMat x) - ρ (uMat y) + 1 := by noncomm_ring
    _ = ρ (uMat y) * ρ (uMat x) - ρ (uMat x) - ρ (uMat y) + 1 := by rw [hAB]
    _ = ρ (uMat y) * ρ (uMat x) - ρ (uMat y) - ρ (uMat x) + 1 := by abel
    _ = (ρ (uMat y) - 1) * (ρ (uMat x) - 1) := by noncomm_ring

private theorem Qo_symm {K : Type} [Field K] [CharP K 2]
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL(2, K) V) (x y : K) : Qo ρ x y ↔ Qo ρ y x := by
  unfold Qo
  rw [P_comm ρ x y]

private theorem Qo_zero {K : Type} [Field K] [CharP K 2]
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL(2, K) V) (y : K) : Qo ρ 0 y := by
  unfold Qo
  rw [P_zero]
  exact mul_zero _

private theorem Qo_self {K : Type} [Field K] [CharP K 2]
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL(2, K) V) (x : K) : Qo ρ x x := by
  unfold Qo
  exact P_self ρ x

private theorem Qo_add {K : Type} [Field K] [CharP K 2]
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL(2, K) V) {x x' y : K}
    (h1 : Qo ρ x y) (h2 : Qo ρ x' y) : Qo ρ (x + x') y := by
  unfold Qo at *
  rw [P_add]
  calc
    P ρ y * (P ρ x + P ρ x' + P ρ x * P ρ x')
        = P ρ y * P ρ x + P ρ y * P ρ x' + (P ρ y * P ρ x) * P ρ x' := by
          noncomm_ring
    _ = 0 := by rw [h1, h2, zero_mul, zero_add, zero_add]

theorem list_sum_map_eq_zero_of_even_count {P : Type*} [DecidableEq P] {U : Type*}
    [AddCommMonoid U] (L : List P) (f : P → U) (h2 : ∀ u : U, u + u = 0)
    (hL : ∀ e ∈ L, Even (L.count e)) : (L.map f).sum = 0 := by
  rw [Finset.sum_list_map_count]
  refine Finset.sum_eq_zero fun e he => ?_
  obtain ⟨m, hm⟩ := hL e (List.mem_toFinset.1 he)
  rw [hm, add_nsmul, ← nsmul_add, h2, nsmul_zero]

namespace EightCert

private abbrev T := GF8 × GF8 × GF8 × GF8

private abbrev g (n : ℕ) : GF8 := GF8.ofNat' n

private def tMul (p q : T) : T :=
  let ⟨a, b, c, d⟩ := p
  let ⟨e, f, h, i⟩ := q
  (a * e + b * h, a * f + b * i, c * e + d * h, c * f + d * i)

private def tDet (p : T) : GF8 := p.1 * p.2.2.2 - p.2.1 * p.2.2.1

private def tOne : T := (g 1, g 0, g 0, g 1)

private def tU (x : GF8) : T := (g 1, x, g 0, g 1)

private theorem tDet_mul (p q : T) : tDet (tMul p q) = tDet p * tDet q := by
  obtain ⟨a, b, c, d⟩ := p
  obtain ⟨e, f, h, i⟩ := q
  simp only [tDet, tMul]
  ring

private theorem tDet_tOne : tDet tOne = 1 := by decide +kernel

private theorem tDet_tU (x : GF8) : tDet (tU x) = 1 := by
  have h1 : (g 1 : GF8) = 1 := by decide +kernel
  have h0 : (g 0 : GF8) = 0 := by decide +kernel
  simp [tDet, tU, h1, h0]

private abbrev U := {p : T // tDet p = 1}

private def Umul (p q : U) : U :=
  ⟨tMul p.1 q.1, by rw [tDet_mul, p.2, q.2, one_mul]⟩

private def Uone : U := ⟨tOne, tDet_tOne⟩

private def uOf (x : GF8) : U := ⟨tU x, tDet_tU x⟩

private def Ucube (p : U) : U := Umul (Umul p p) p

private def up (a b c d e f h i : GF8) (h1 : tDet (a, b, c, d) = 1)
    (h2 : tDet (e, f, h, i) = 1) : U × U :=
  (⟨(a, b, c, d), h1⟩, ⟨(e, f, h, i), h2⟩)

private def data12 : List (U × U) :=
  [ up (g 0) (g 6) (g 3) (g 1) (g 0) (g 6) (g 3) (g 7)
      (by decide +kernel) (by decide +kernel),
    up (g 0) (g 7) (g 4) (g 1) (g 1) (g 4) (g 3) (g 6)
      (by decide +kernel) (by decide +kernel),
    up (g 2) (g 3) (g 4) (g 3) (g 1) (g 1) (g 0) (g 1)
      (by decide +kernel) (by decide +kernel),
    up (g 4) (g 1) (g 3) (g 5) (g 2) (g 4) (g 7) (g 0)
      (by decide +kernel) (by decide +kernel),
    up (g 4) (g 3) (g 1) (g 5) (g 2) (g 1) (g 4) (g 7)
      (by decide +kernel) (by decide +kernel),
    up (g 4) (g 4) (g 2) (g 5) (g 0) (g 6) (g 3) (g 7)
      (by decide +kernel) (by decide +kernel),
    up (g 6) (g 2) (g 7) (g 7) (g 1) (g 0) (g 0) (g 1)
      (by decide +kernel) (by decide +kernel),
    up (g 6) (g 6) (g 4) (g 7) (g 1) (g 3) (g 0) (g 1)
      (by decide +kernel) (by decide +kernel)]

private def data14 : List (U × U) :=
  [ up (g 0) (g 2) (g 5) (g 1) (g 0) (g 3) (g 6) (g 7)
      (by decide +kernel) (by decide +kernel),
    up (g 0) (g 3) (g 6) (g 1) (g 0) (g 3) (g 6) (g 7)
      (by decide +kernel) (by decide +kernel),
    up (g 2) (g 2) (g 6) (g 3) (g 1) (g 5) (g 0) (g 1)
      (by decide +kernel) (by decide +kernel),
    up (g 2) (g 5) (g 5) (g 3) (g 2) (g 3) (g 6) (g 0)
      (by decide +kernel) (by decide +kernel),
    up (g 4) (g 5) (g 6) (g 5) (g 1) (g 0) (g 0) (g 1)
      (by decide +kernel) (by decide +kernel),
    up (g 4) (g 6) (g 5) (g 5) (g 1) (g 2) (g 6) (g 6)
      (by decide +kernel) (by decide +kernel),
    up (g 6) (g 1) (g 5) (g 7) (g 3) (g 6) (g 6) (g 1)
      (by decide +kernel) (by decide +kernel),
    up (g 6) (g 4) (g 6) (g 7) (g 1) (g 4) (g 0) (g 1)
      (by decide +kernel) (by decide +kernel)]

private def data24 : List (U × U) :=
  [ up (g 0) (g 3) (g 6) (g 1) (g 0) (g 5) (g 2) (g 4)
      (by decide +kernel) (by decide +kernel),
    up (g 0) (g 7) (g 4) (g 1) (g 0) (g 7) (g 4) (g 2)
      (by decide +kernel) (by decide +kernel),
    up (g 2) (g 1) (g 7) (g 3) (g 1) (g 5) (g 4) (g 3)
      (by decide +kernel) (by decide +kernel),
    up (g 2) (g 3) (g 4) (g 3) (g 0) (g 5) (g 2) (g 4)
      (by decide +kernel) (by decide +kernel),
    up (g 4) (g 3) (g 1) (g 5) (g 0) (g 7) (g 4) (g 2)
      (by decide +kernel) (by decide +kernel),
    up (g 6) (g 4) (g 6) (g 7) (g 1) (g 6) (g 0) (g 1)
      (by decide +kernel) (by decide +kernel),
    up (g 6) (g 6) (g 4) (g 7) (g 1) (g 4) (g 0) (g 1)
      (by decide +kernel) (by decide +kernel),
    up (g 6) (g 7) (g 2) (g 7) (g 1) (g 0) (g 0) (g 1)
      (by decide +kernel) (by decide +kernel)]

private def lock (x y : U) (data : List (U × U)) : List U :=
  [Uone, x, y, Umul x y] ++
    data.flatMap fun p => [p.2, Umul p.1 p.2, Umul (Umul p.1 p.1) p.2]

private def L12 : List U := lock (uOf (g 1)) (uOf (g 2)) data12

private def L14 : List U := lock (uOf (g 1)) (uOf (g 4)) data14

private def L24 : List U := lock (uOf (g 2)) (uOf (g 4)) data24

private theorem L12_even : ∀ x ∈ L12, Even (L12.count x) := by decide +kernel

private theorem L14_even : ∀ x ∈ L14, Even (L14.count x) := by decide +kernel

private theorem L24_even : ∀ x ∈ L24, Even (L24.count x) := by decide +kernel

private theorem data12_cube : ∀ p ∈ data12, Ucube p.1 = Uone := by decide +kernel

private theorem data14_cube : ∀ p ∈ data14, Ucube p.1 = Uone := by decide +kernel

private theorem data24_cube : ∀ p ∈ data24, Ucube p.1 = Uone := by decide +kernel

private theorem data12_ne : ∀ p ∈ data12, p.1 ≠ Uone := by decide +kernel

private theorem data14_ne : ∀ p ∈ data14, p.1 ≠ Uone := by decide +kernel

private theorem data24_ne : ∀ p ∈ data24, p.1 ≠ Uone := by decide +kernel

private noncomputable def toMat {K : Type} [Field K] (σ : GF8 ≃+* K) (p : T) :
    Matrix (Fin 2) (Fin 2) K :=
  !![σ p.1, σ p.2.1; σ p.2.2.1, σ p.2.2.2]

private theorem toMat_mul {K : Type} [Field K] (σ : GF8 ≃+* K) (p q : T) :
    toMat σ (tMul p q) = toMat σ p * toMat σ q := by
  obtain ⟨a, b, c, d⟩ := p
  obtain ⟨e, f, k, i⟩ := q
  ext x y
  fin_cases x <;> fin_cases y <;>
    simp [toMat, tMul, Matrix.mul_apply, Fin.sum_univ_two, map_add, map_mul]

private theorem toMat_one {K : Type} [Field K] (σ : GF8 ≃+* K) :
    toMat σ tOne = 1 := by
  have h1 : (g 1 : GF8) = 1 := by decide +kernel
  have h0 : (g 0 : GF8) = 0 := by decide +kernel
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toMat, tOne, h1, h0, Matrix.one_apply]

private theorem toMat_det {K : Type} [Field K] (σ : GF8 ≃+* K) (p : T) :
    (toMat σ p).det = σ (tDet p) := by
  obtain ⟨a, b, c, d⟩ := p
  simp [toMat, tDet, Matrix.det_fin_two, map_sub, map_mul]

private theorem toMat_injective {K : Type} [Field K] (σ : GF8 ≃+* K) :
    Function.Injective (toMat σ) := by
  intro p q h
  obtain ⟨a, b, c, d⟩ := p
  obtain ⟨e, f, k, i⟩ := q
  have h00 : σ a = σ e := by
    simpa [toMat] using congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 0) h
  have h01 : σ b = σ f := by
    simpa [toMat] using congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 1) h
  have h10 : σ c = σ k := by
    simpa [toMat] using congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 1 0) h
  have h11 : σ d = σ i := by
    simpa [toMat] using congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 1 1) h
  have ha : a = e := σ.injective h00
  have hb : b = f := σ.injective h01
  have hc : c = k := σ.injective h10
  have hd : d = i := σ.injective h11
  cases ha
  cases hb
  cases hc
  cases hd
  rfl

private noncomputable def UtoSL {K : Type} [Field K] (σ : GF8 ≃+* K) (p : U) :
    SL(2, K) :=
  ⟨toMat σ p.1, by rw [toMat_det, p.2, map_one]⟩

private theorem UtoSL_mul {K : Type} [Field K] (σ : GF8 ≃+* K) (p q : U) :
    UtoSL σ (Umul p q) = UtoSL σ p * UtoSL σ q := by
  apply Subtype.ext
  change toMat σ (tMul p.1 q.1) = toMat σ p.1 * toMat σ q.1
  exact toMat_mul σ p.1 q.1

private theorem UtoSL_one {K : Type} [Field K] (σ : GF8 ≃+* K) :
    UtoSL σ Uone = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [UtoSL, Uone, toMat_one]

private theorem UtoSL_uOf {K : Type} [Field K] [CharP K 2] (σ : GF8 ≃+* K)
    (x : GF8) : UtoSL σ (uOf x) = uMat (σ x) := by
  have h1 : (g 1 : GF8) = 1 := by decide +kernel
  have h0 : (g 0 : GF8) = 0 := by decide +kernel
  ext i j
  fin_cases i <;> fin_cases j <;> simp [UtoSL, uOf, toMat, tU, uMat, h1, h0]

private theorem UtoSL_cube {K : Type} [Field K] (σ : GF8 ≃+* K) (p : U) :
    UtoSL σ (Ucube p) = UtoSL σ p ^ 3 := by
  rw [Ucube, pow_three', UtoSL_mul, UtoSL_mul]

private theorem UtoSL_injective {K : Type} [Field K] (σ : GF8 ≃+* K) :
    Function.Injective (UtoSL σ) := by
  intro p q h
  apply Subtype.ext
  apply toMat_injective σ
  exact congrArg (fun g : SL(2, K) => (g : Matrix (Fin 2) (Fin 2) K)) h

private theorem UtoSL_ne_one {K : Type} [Field K] (σ : GF8 ≃+* K) {p : U}
    (hp : p ≠ Uone) : UtoSL σ p ≠ 1 := by
  intro h
  apply hp
  apply UtoSL_injective σ
  rw [h, UtoSL_one]

private theorem rho_triple_eq_zero {K : Type} [Field K] [CharP K 2]
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL(2, K) V)
    (hfpf : ∀ c : SL(2, K), c ^ 3 = 1 → c ≠ 1 → ∀ v : V,
      ρ c (ρ c v) + ρ c v + v = 0)
    (c z : SL(2, K)) (hc3 : c ^ 3 = 1) (hcne : c ≠ 1) (w : V) :
    ρ z w + ρ (c * z) w + ρ (c * c * z) w = 0 := by
  have h := hfpf c hc3 hcne (ρ z w)
  have h1 : ρ (c * z) w = ρ c (ρ z w) := by
    rw [map_mul, Module.End.mul_apply]
  have h2 : ρ (c * c * z) w = ρ c (ρ c (ρ z w)) := by
    rw [map_mul, Module.End.mul_apply, map_mul, Module.End.mul_apply]
  rw [h1, h2]
  simpa [add_comm, add_left_comm, add_assoc] using h

private theorem sum_map_flatMap_Usl {K : Type} [Field K] [CharP K 2]
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL(2, K) V) (σ : GF8 ≃+* K) (d : List (U × U))
    (v : V) :
    ((((d.flatMap fun p => [p.2, Umul p.1 p.2,
        Umul (Umul p.1 p.1) p.2]).map (UtoSL σ)).map fun g => ρ g v)).sum =
      (d.map fun p => ρ (UtoSL σ p.2) v + ρ (UtoSL σ (Umul p.1 p.2)) v +
        ρ (UtoSL σ (Umul (Umul p.1 p.1) p.2)) v).sum := by
  induction d with
  | nil => rfl
  | cons p d ih =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
        List.sum_cons, List.map_nil, List.sum_nil, ih]
      abel

private theorem sum_triples_eq_zero {K : Type} [Field K] [CharP K 2]
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL(2, K) V)
    (hfpf : ∀ c : SL(2, K), c ^ 3 = 1 → c ≠ 1 → ∀ v : V,
      ρ c (ρ c v) + ρ c v + v = 0)
    (σ : GF8 ≃+* K) (d : List (U × U))
    (hcube : ∀ p ∈ d, Ucube p.1 = Uone) (hne : ∀ p ∈ d, p.1 ≠ Uone) (v : V) :
    (d.map fun p => ρ (UtoSL σ p.2) v + ρ (UtoSL σ (Umul p.1 p.2)) v +
        ρ (UtoSL σ (Umul (Umul p.1 p.1) p.2)) v).sum = 0 := by
  induction d with
  | nil => rfl
  | cons p d ih =>
      rw [List.map_cons, List.sum_cons]
      have hp0 : ρ (UtoSL σ p.2) v + ρ (UtoSL σ (Umul p.1 p.2)) v +
          ρ (UtoSL σ (Umul (Umul p.1 p.1) p.2)) v = 0 := by
        simp only [UtoSL_mul]
        apply rho_triple_eq_zero ρ hfpf (UtoSL σ p.1) (UtoSL σ p.2)
        · rw [← UtoSL_cube, hcube p (by simp), UtoSL_one]
        · exact UtoSL_ne_one σ (hne p (by simp))
      have ih' := ih (fun q hq => hcube q (List.mem_cons_of_mem p hq))
        (fun q hq => hne q (List.mem_cons_of_mem p hq))
      rw [hp0, ih', zero_add]

private theorem sum_lock_eq {K : Type} [Field K] [CharP K 2]
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL(2, K) V)
    (hfpf : ∀ c : SL(2, K), c ^ 3 = 1 → c ≠ 1 → ∀ v : V,
      ρ c (ρ c v) + ρ c v + v = 0)
    (σ : GF8 ≃+* K) (x y : GF8) (d : List (U × U))
    (hcube : ∀ p ∈ d, Ucube p.1 = Uone) (hne : ∀ p ∈ d, p.1 ≠ Uone) (v : V) :
    (((lock (uOf x) (uOf y) d).map (UtoSL σ)).map fun g => ρ g v).sum =
      ρ (uMat (σ x) * uMat (σ y)) v + ρ (uMat (σ y)) v + ρ (uMat (σ x)) v + v := by
  have htail := sum_triples_eq_zero ρ hfpf σ d hcube hne v
  have hflat := sum_map_flatMap_Usl ρ σ d v
  simp only [lock, List.map_append, List.sum_append, List.map_cons, List.sum_cons,
    List.map_nil, List.sum_nil]
  rw [hflat, htail, add_zero]
  simp only [UtoSL_one, UtoSL_uOf, UtoSL_mul, map_one, Module.End.one_apply]
  abel

private theorem sum_lock_eq_zero {K : Type} [Field K] [CharP K 2]
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL(2, K) V) (σ : GF8 ≃+* K) (x y : GF8)
    (d : List (U × U))
    (heven : ∀ g ∈ lock (uOf x) (uOf y) d,
      Even ((lock (uOf x) (uOf y) d).count g)) (v : V) :
    (((lock (uOf x) (uOf y) d).map (UtoSL σ)).map fun g => ρ g v).sum = 0 := by
  classical
  have hmap : ∀ g ∈ (lock (uOf x) (uOf y) d).map (UtoSL σ),
      Even (((lock (uOf x) (uOf y) d).map (UtoSL σ)).count g) := by
    intro g hg
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hg
    rw [List.count_map_of_injective _ _ (UtoSL_injective σ) p]
    exact heven p hp
  exact list_sum_map_eq_zero_of_even_count _ _ ZModModule.add_self hmap

private theorem R_of_data {K : Type} [Field K] [CharP K 2]
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL(2, K) V)
    (hfpf : ∀ c : SL(2, K), c ^ 3 = 1 → c ≠ 1 → ∀ v : V,
      ρ c (ρ c v) + ρ c v + v = 0)
    (σ : GF8 ≃+* K) (x y : GF8) (d : List (U × U))
    (heven : ∀ g ∈ lock (uOf x) (uOf y) d,
      Even ((lock (uOf x) (uOf y) d).count g))
    (hcube : ∀ p ∈ d, Ucube p.1 = Uone) (hne : ∀ p ∈ d, p.1 ≠ Uone) :
    R ρ (σ x) (σ y) := by
  intro v
  have hzero := sum_lock_eq_zero ρ σ x y d heven v
  rw [sum_lock_eq ρ hfpf σ x y d hcube hne v] at hzero
  exact hzero

private theorem quadratic_basis {K : Type} [Field K] [CharP K 2] {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] (ρ : Representation (ZMod 2) SL(2, K) V)
    (hfpf : ∀ c : SL(2, K), c ^ 3 = 1 → c ≠ 1 → ∀ v : V,
      ρ c (ρ c v) + ρ c v + v = 0) (σ : GF8 ≃+* K) :
    Q ρ (σ (GF8.ofNat' 1)) (σ (GF8.ofNat' 2)) ∧
      Q ρ (σ (GF8.ofNat' 1)) (σ (GF8.ofNat' 4)) ∧
      Q ρ (σ (GF8.ofNat' 2)) (σ (GF8.ofNat' 4)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (R_iff_Q ρ _ _).1 (R_of_data ρ hfpf σ (g 1) (g 2) data12
      (by simpa only [L12] using L12_even) data12_cube data12_ne)
  · exact (R_iff_Q ρ _ _).1 (R_of_data ρ hfpf σ (g 1) (g 4) data14
      (by simpa only [L14] using L14_even) data14_cube data14_ne)
  · exact (R_iff_Q ρ _ _).1 (R_of_data ρ hfpf σ (g 2) (g 4) data24
      (by simpa only [L24] using L24_even) data24_cube data24_ne)

end EightCert

private theorem card_GF8 : Fintype.card GF8 = 8 := by decide +kernel

private noncomputable def fieldEquiv {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 8) : GF8 ≃+* K := by
  letI : Fintype K := Fintype.ofFinite K
  exact FiniteField.ringEquivOfCardEq (by rw [card_GF8, Fintype.card_eq_nat_card, hK])

private def decomp (x : GF8) : List GF8 :=
  (if x.toNat &&& 1 = 1 then [GF8.ofNat' 1] else []) ++
    (if x.toNat &&& 2 = 2 then [GF8.ofNat' 2] else []) ++
      (if x.toNat &&& 4 = 4 then [GF8.ofNat' 4] else [])

private theorem decomp_sum : ∀ x : GF8, (decomp x).sum = x := by decide +kernel

private theorem decomp_mem :
    ∀ x : GF8, ∀ b ∈ decomp x, b = GF8.ofNat' 1 ∨ b = GF8.ofNat' 2 ∨ b = GF8.ofNat' 4 := by
  decide +kernel

private theorem Qo_add_right {K : Type} [Field K] [CharP K 2]
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL(2, K) V) {x y y' : K}
    (h1 : Qo ρ x y) (h2 : Qo ρ x y') : Qo ρ x (y + y') := by
  have h1' : Qo ρ y x := (Qo_symm ρ x y).1 h1
  have h2' : Qo ρ y' x := (Qo_symm ρ x y').1 h2
  exact (Qo_symm ρ (y + y') x).1 (Qo_add ρ h1' h2')

private theorem Qo_sigma_sum_left {K : Type} [Field K] [CharP K 2]
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL(2, K) V) (σ : GF8 ≃+* K) {y : K}
    {l : List GF8} (h : ∀ b ∈ l, Qo ρ (σ b) y) : Qo ρ (σ l.sum) y := by
  induction l with
  | nil => simpa using Qo_zero ρ y
  | cons b l ih =>
      have hb : Qo ρ (σ b) y := h b (by simp)
      have hl : ∀ c ∈ l, Qo ρ (σ c) y := fun c hc => h c (by simp [hc])
      have hsum := Qo_add ρ hb (ih hl)
      simpa [map_add] using hsum

private theorem Qo_sigma_sum_right {K : Type} [Field K] [CharP K 2]
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL(2, K) V) (σ : GF8 ≃+* K) {x : K}
    {l : List GF8} (h : ∀ b ∈ l, Qo ρ x (σ b)) : Qo ρ x (σ l.sum) := by
  induction l with
  | nil => simpa using (Qo_symm ρ (0 : K) x).1 (Qo_zero ρ x)
  | cons b l ih =>
      have hb : Qo ρ x (σ b) := h b (by simp)
      have hl : ∀ c ∈ l, Qo ρ x (σ c) := fun c hc => h c (by simp [hc])
      have hsum := Qo_add_right ρ hb (ih hl)
      simpa [map_add] using hsum

private theorem Qo_basis_pair {K : Type} [Field K] [CharP K 2]
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL(2, K) V)
    (hfpf : ∀ c : SL(2, K), c ^ 3 = 1 → c ≠ 1 → ∀ v : V,
      ρ c (ρ c v) + ρ c v + v = 0) (σ : GF8 ≃+* K) :
    ∀ b ∈ ([GF8.ofNat' 1, GF8.ofNat' 2, GF8.ofNat' 4] : List GF8),
      ∀ c ∈ ([GF8.ofNat' 1, GF8.ofNat' 2, GF8.ofNat' 4] : List GF8),
        Qo ρ (σ b) (σ c) := by
  have h12 : Qo ρ (σ (GF8.ofNat' 1)) (σ (GF8.ofNat' 2)) :=
    (Q_iff_Qo ρ _ _).1 (EightCert.quadratic_basis ρ hfpf σ).1
  have h14 : Qo ρ (σ (GF8.ofNat' 1)) (σ (GF8.ofNat' 4)) :=
    (Q_iff_Qo ρ _ _).1 (EightCert.quadratic_basis ρ hfpf σ).2.1
  have h24 : Qo ρ (σ (GF8.ofNat' 2)) (σ (GF8.ofNat' 4)) :=
    (Q_iff_Qo ρ _ _).1 (EightCert.quadratic_basis ρ hfpf σ).2.2
  intro b hb c hc
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb hc
  rcases hb with rfl | rfl | rfl <;> rcases hc with rfl | rfl | rfl
  · exact Qo_self ρ _
  · exact h12
  · exact h14
  · exact (Qo_symm ρ _ _).1 h12
  · exact Qo_self ρ _
  · exact h24
  · exact (Qo_symm ρ _ _).1 h14
  · exact (Qo_symm ρ _ _).1 h24
  · exact Qo_self ρ _

private theorem Qo_all {K : Type} [Field K] [CharP K 2]
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL(2, K) V)
    (hfpf : ∀ c : SL(2, K), c ^ 3 = 1 → c ≠ 1 → ∀ v : V,
      ρ c (ρ c v) + ρ c v + v = 0) (σ : GF8 ≃+* K) (x y : GF8) :
    Qo ρ (σ x) (σ y) := by
  have hleft : ∀ b ∈ decomp x, Qo ρ (σ b) (σ y) := by
    intro b hb
    have hy : ∀ c ∈ decomp y, Qo ρ (σ b) (σ c) := by
      intro c hc
      rcases decomp_mem x b hb with rfl | rfl | rfl <;>
        rcases decomp_mem y c hc with rfl | rfl | rfl <;>
        exact Qo_basis_pair ρ hfpf σ _ (by simp) _ (by simp)
    have hy' := Qo_sigma_sum_right ρ σ hy
    rwa [decomp_sum y] at hy'
  have hx := Qo_sigma_sum_left ρ σ hleft
  rwa [decomp_sum x] at hx

theorem quadratic_of_card_eight {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 8) {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL(2, K) V)
    (hfpf : ∀ c : SL(2, K), c ^ 3 = 1 → c ≠ 1 → ∀ v : V,
      ρ c (ρ c v) + ρ c v + v = 0) :
    ∀ (x y : K) (v : V), ρ (uMat y) (ρ (uMat x) v - v) = ρ (uMat x) v - v := by
  let σ : GF8 ≃+* K := fieldEquiv hK
  have hQ : ∀ x y : GF8, Q ρ (σ x) (σ y) := fun x y =>
    (Q_iff_Qo ρ _ _).2 (Qo_all ρ hfpf σ x y)
  intro x y v
  obtain ⟨a, rfl⟩ := σ.surjective x
  obtain ⟨b, rfl⟩ := σ.surjective y
  exact hQ a b v

end CFSG.RepresentationTheory.SL2NatSum

