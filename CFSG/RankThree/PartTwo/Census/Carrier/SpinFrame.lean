module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Basic

public section

namespace CFSG.RankThree.PartTwo.Census.Carrier.SpinFrame

open Matrix

section Ring

variable {A : Type*} [CommRing A] {R : Type*} [Ring R] [Algebra A R]

theorem cast_mul_eq_zero {a b : ℤ} (h : a * b = 0) : ((a : ℤ) : A) * (b : A) = 0 := by
  rw [← Int.cast_mul, h, Int.cast_zero]

theorem mul_mul_sub_eq {x y z : R} {bxz byz : A} (hxz : x * z + z * x = algebraMap A R bxz)
    (hyz : y * z + z * y = algebraMap A R byz) :
    x * y * z - z * (x * y) = byz • x - bxz • y := by
  have e : x * y * z - z * (x * y) = x * (y * z + z * y) - (x * z + z * x) * y := by
    noncomm_ring
  rw [e, hyz, hxz, ← Algebra.commutes, ← Algebra.smul_def, ← Algebra.smul_def]

theorem mul_mul_mul_mul_eq_zero {x y : R} {qx qy : A} (hxy : x * y + y * x = 0)
    (hxx : x * x = algebraMap A R qx) (hyy : y * y = algebraMap A R qy) (hq : qx * qy = 0) :
    x * y * (x * y) = 0 := by
  have hyx : y * x = -(x * y) := eq_neg_of_add_eq_zero_right hxy
  have e : x * y * (x * y) = -((x * x) * (y * y)) := by
    calc x * y * (x * y) = x * (y * x) * y := by noncomm_ring
      _ = -((x * x) * (y * y)) := by rw [hyx]; noncomm_ring
  rw [e, hxx, hyy, ← map_mul, hq, map_zero, neg_zero]

theorem mul_mul_mul_mul_eq {x y z : R} {bxz byz qx qy : A} (hxy : x * y + y * x = 0)
    (hxx : x * x = algebraMap A R qx) (hyy : y * y = algebraMap A R qy) (hq : qx * qy = 0)
    (hxz : x * z + z * x = algebraMap A R bxz) (hyz : y * z + z * y = algebraMap A R byz) :
    x * y * z * (x * y) = (byz * qx) • y + (bxz * qy) • x := by
  have hyx : y * x = -(x * y) := eq_neg_of_add_eq_zero_right hxy
  have h1 : x * y * z = z * (x * y) + (byz • x - bxz • y) := by
    rw [← mul_mul_sub_eq hxz hyz]; abel
  have h2 : y * (x * y) = -(qy • x) := by
    calc y * (x * y) = (y * x) * y := by noncomm_ring
      _ = -(x * (y * y)) := by rw [hyx]; noncomm_ring
      _ = -(qy • x) := by rw [hyy, ← Algebra.commutes, ← Algebra.smul_def]
  have h3 : x * (x * y) = qx • y := by
    rw [← mul_assoc, hxx, ← Algebra.smul_def]
  rw [h1, add_mul, sub_mul, mul_assoc z, mul_mul_mul_mul_eq_zero hxy hxx hyy hq, mul_zero,
    zero_add, smul_mul_assoc, smul_mul_assoc, h3, h2, smul_neg, smul_smul, smul_smul,
    sub_neg_eq_add]

end Ring

structure Frame {ι : Type} [Fintype ι] [DecidableEq ι] (bm : Matrix ι ι ℤ) (qd : ι → ℤ)
    (N : Type) [Fintype N] [DecidableEq N] where
  gam : ι → Matrix N N ℤ
  anticomm : ∀ a b, gam a * gam b + gam b * gam a = bm a b • (1 : Matrix N N ℤ)
  sq : ∀ a, gam a * gam a = qd a • (1 : Matrix N N ℤ)
  pos : ι → N × N
  gam_pos : ∀ a b, gam b (pos a).1 (pos a).2 = if a = b then 1 else 0

namespace Frame

variable {ι : Type} [Fintype ι] [DecidableEq ι] {bm : Matrix ι ι ℤ} {qd : ι → ℤ}
  {N : Type} [Fintype N] [DecidableEq N] (F : Frame bm qd N) (A : Type*) [CommRing A]

@[expose] def gamA (a : ι) : Matrix N N A :=
  (Int.castRingHom A).mapMatrix (F.gam a)

theorem mapMatrix_smul_one (k : ℤ) :
    (Int.castRingHom A).mapMatrix (k • (1 : Matrix N N ℤ)) = (k : A) • (1 : Matrix N N A) := by
  ext r c
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply]
  by_cases h : r = c
  · subst h
    simp
  · simp [Matrix.one_apply_ne h]

theorem gamA_anticomm (a b : ι) :
    F.gamA A a * F.gamA A b + F.gamA A b * F.gamA A a =
      algebraMap A (Matrix N N A) (bm a b) := by
  have h := congrArg (Int.castRingHom A).mapMatrix (F.anticomm a b)
  rw [map_add, map_mul, map_mul, mapMatrix_smul_one] at h
  rw [gamA, gamA, h, Algebra.algebraMap_eq_smul_one]

theorem gamA_sq (a : ι) :
    F.gamA A a * F.gamA A a = algebraMap A (Matrix N N A) (qd a) := by
  have h := congrArg (Int.castRingHom A).mapMatrix (F.sq a)
  rw [map_mul, mapMatrix_smul_one] at h
  rw [gamA, h, Algebra.algebraMap_eq_smul_one]

@[expose] def coord (a : ι) (M : Matrix N N A) : A :=
  M (F.pos a).1 (F.pos a).2

theorem coord_gamA (a b : ι) : F.coord A a (F.gamA A b) = if a = b then 1 else 0 := by
  rw [coord, gamA, RingHom.mapMatrix_apply, Matrix.map_apply, F.gam_pos]
  split_ifs <;> simp

theorem coord_add (a : ι) (M M' : Matrix N N A) :
    F.coord A a (M + M') = F.coord A a M + F.coord A a M' :=
  rfl

theorem coord_smul (a : ι) (r : A) (M : Matrix N N A) :
    F.coord A a (r • M) = r * F.coord A a M :=
  rfl

theorem coord_sum {κ : Type*} (s : Finset κ) (a : ι) (M : κ → Matrix N N A) :
    F.coord A a (∑ k ∈ s, M k) = ∑ k ∈ s, F.coord A a (M k) := by
  simp only [coord, Matrix.sum_apply]

@[expose] def vec (c : ι → A) : Matrix N N A :=
  ∑ a, c a • F.gamA A a

theorem coord_vec (c : ι → A) (a : ι) : F.coord A a (F.vec A c) = c a := by
  rw [vec, coord_sum]
  simp only [coord_smul, coord_gamA, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]

theorem vec_add (c d : ι → A) : F.vec A (c + d) = F.vec A c + F.vec A d := by
  simp only [vec, Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem vec_smul (r : A) (c : ι → A) : F.vec A (r • c) = r • F.vec A c := by
  simp only [vec, Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul]

theorem vec_sum {κ : Type*} (s : Finset κ) (c : κ → ι → A) :
    F.vec A (∑ k ∈ s, c k) = ∑ k ∈ s, F.vec A (c k) := by
  simp only [vec, Finset.sum_apply, Finset.sum_smul]
  exact Finset.sum_comm

theorem vec_single (a : ι) : F.vec A (Pi.single a 1) = F.gamA A a := by
  rw [vec, Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

@[expose] def InSpan (M : Matrix N N A) : Prop :=
  M = F.vec A fun a => F.coord A a M

theorem inSpan_iff {M : Matrix N N A} : F.InSpan A M ↔ ∃ c, M = F.vec A c := by
  constructor
  · intro h
    exact ⟨_, h⟩
  · rintro ⟨c, rfl⟩
    rw [InSpan]
    congr 1
    funext a
    rw [coord_vec]

theorem inSpan_vec (c : ι → A) : F.InSpan A (F.vec A c) :=
  (F.inSpan_iff A).2 ⟨c, rfl⟩

theorem inSpan_gamA (a : ι) : F.InSpan A (F.gamA A a) := by
  rw [← vec_single]
  exact F.inSpan_vec A _

theorem inSpan_mul_vec_mul {g g' : Matrix N N A} (hg : ∀ a, F.InSpan A (g * F.gamA A a * g'))
    (c : ι → A) : F.InSpan A (g * F.vec A c * g') := by
  rw [inSpan_iff]
  refine ⟨∑ a, c a • fun b => F.coord A b (g * F.gamA A a * g'), ?_⟩
  rw [vec_sum]
  simp only [vec_smul]
  rw [vec, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, ← hg a]

theorem inSpan_add {M M' : Matrix N N A} (h : F.InSpan A M) (h' : F.InSpan A M') :
    F.InSpan A (M + M') := by
  obtain ⟨c, rfl⟩ := (F.inSpan_iff A).1 h
  obtain ⟨d, rfl⟩ := (F.inSpan_iff A).1 h'
  rw [← vec_add]
  exact F.inSpan_vec A _

theorem inSpan_smul (r : A) {M : Matrix N N A} (h : F.InSpan A M) : F.InSpan A (r • M) := by
  obtain ⟨c, rfl⟩ := (F.inSpan_iff A).1 h
  rw [← vec_smul]
  exact F.inSpan_vec A _

theorem inSpan_neg {M : Matrix N N A} (h : F.InSpan A M) : F.InSpan A (-M) := by
  rw [← neg_one_smul A M]
  exact F.inSpan_smul A _ h

theorem inSpan_sub {M M' : Matrix N N A} (h : F.InSpan A M) (h' : F.InSpan A M') :
    F.InSpan A (M - M') := by
  rw [sub_eq_add_neg]
  exact F.inSpan_add A h (F.inSpan_neg A h')


@[expose] def normGroup : Subgroup (GL N A) where
  carrier := {g | ∀ a, F.InSpan A ((g : Matrix N N A) * F.gamA A a * (↑g⁻¹ : Matrix N N A)) ∧
    F.InSpan A ((↑g⁻¹ : Matrix N N A) * F.gamA A a * (g : Matrix N N A))}
  one_mem' := fun a => by
    simp only [inv_one, Units.val_one, one_mul, mul_one]
    exact ⟨F.inSpan_gamA A a, F.inSpan_gamA A a⟩
  mul_mem' := by
    intro g h hg hh a
    simp only [Set.mem_ofPred_eq] at hg hh ⊢
    obtain ⟨c, hc⟩ := (F.inSpan_iff A).1 (hh a).1
    obtain ⟨d, hd⟩ := (F.inSpan_iff A).1 (hg a).2
    refine ⟨?_, ?_⟩
    · have e : ((g * h : GL N A) : Matrix N N A) * F.gamA A a * (↑(g * h)⁻¹ : Matrix N N A) =
          (g : Matrix N N A) * ((h : Matrix N N A) * F.gamA A a * (↑h⁻¹ : Matrix N N A)) *
            (↑g⁻¹ : Matrix N N A) := by
        simp only [_root_.mul_inv_rev, Units.val_mul]; noncomm_ring
      rw [e, hc]
      exact F.inSpan_mul_vec_mul A (fun b => (hg b).1) c
    · have e : (↑(g * h)⁻¹ : Matrix N N A) * F.gamA A a * ((g * h : GL N A) : Matrix N N A) =
          (↑h⁻¹ : Matrix N N A) * ((↑g⁻¹ : Matrix N N A) * F.gamA A a * (g : Matrix N N A)) *
            (h : Matrix N N A) := by
        simp only [_root_.mul_inv_rev, Units.val_mul]; noncomm_ring
      rw [e, hd]
      exact F.inSpan_mul_vec_mul A (fun b => (hh b).2) d
  inv_mem' := by
    intro g hg a
    simp only [Set.mem_ofPred_eq, inv_inv] at hg ⊢
    exact ⟨(hg a).2, (hg a).1⟩

@[expose] def rho (g : GL N A) : Matrix ι ι A :=
  fun b a => F.coord A b ((g : Matrix N N A) * F.gamA A a * (↑g⁻¹ : Matrix N N A))

variable {F A}

theorem conj_gamA {g : GL N A} (hg : g ∈ F.normGroup A) (a : ι) :
    (g : Matrix N N A) * F.gamA A a * (↑g⁻¹ : Matrix N N A) = ∑ b, F.rho A g b a • F.gamA A b :=
  (hg a).1

theorem conj_vec {g : GL N A} (hg : g ∈ F.normGroup A) (c : ι → A) :
    (g : Matrix N N A) * F.vec A c * (↑g⁻¹ : Matrix N N A) = F.vec A (F.rho A g *ᵥ c) := by
  rw [vec, Finset.mul_sum, Finset.sum_mul]
  simp only [mul_smul_comm, smul_mul_assoc, conj_gamA hg, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm, vec]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  simp only [Matrix.mulVec, dotProduct, mul_comm]

theorem rho_mul {g h : GL N A} (hg : g ∈ F.normGroup A) (hh : h ∈ F.normGroup A) :
    F.rho A (g * h) = F.rho A g * F.rho A h := by
  ext b a
  have e : ((g * h : GL N A) : Matrix N N A) * F.gamA A a * (↑(g * h)⁻¹ : Matrix N N A) =
      (g : Matrix N N A) * ((h : Matrix N N A) * F.gamA A a * (↑h⁻¹ : Matrix N N A)) *
        (↑g⁻¹ : Matrix N N A) := by
    simp only [_root_.mul_inv_rev, Units.val_mul]; noncomm_ring
  have hv : (h : Matrix N N A) * F.gamA A a * (↑h⁻¹ : Matrix N N A) =
      F.vec A fun d => F.rho A h d a := (hh a).1
  show F.coord A b _ = _
  rw [e, hv, conj_vec hg, coord_vec, Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem conj_eq_of_rho_eq_one {g : GL N A} (hg : g ∈ F.normGroup A) (h : F.rho A g = 1)
    (a : ι) : (g : Matrix N N A) * F.gamA A a * (↑g⁻¹ : Matrix N N A) = F.gamA A a := by
  rw [conj_gamA hg, h, Finset.sum_eq_single a]
  · rw [Matrix.one_apply_eq, one_smul]
  · intro b _ hb
    rw [Matrix.one_apply_ne hb, zero_smul]
  · simp

theorem rho_one : F.rho A 1 = 1 := by
  ext b a
  simp only [rho, inv_one, Units.val_one, one_mul, mul_one, coord_gamA, Matrix.one_apply]

theorem rho_transpose_mul_mul_rho [Nonempty N] {g : GL N A} (hg : g ∈ F.normGroup A) :
    (F.rho A g)ᵀ * (Int.castRingHom A).mapMatrix bm * F.rho A g =
      (Int.castRingHom A).mapMatrix bm := by
  ext a b
  have e : (g : Matrix N N A) * (F.gamA A a * F.gamA A b + F.gamA A b * F.gamA A a) *
      (↑g⁻¹ : Matrix N N A) =
      ((g : Matrix N N A) * F.gamA A a * (↑g⁻¹ : Matrix N N A)) *
          ((g : Matrix N N A) * F.gamA A b * (↑g⁻¹ : Matrix N N A)) +
        ((g : Matrix N N A) * F.gamA A b * (↑g⁻¹ : Matrix N N A)) *
          ((g : Matrix N N A) * F.gamA A a * (↑g⁻¹ : Matrix N N A)) := by
    have hgg : (↑g⁻¹ : Matrix N N A) * (g : Matrix N N A) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc (g : Matrix N N A) * (F.gamA A a * F.gamA A b + F.gamA A b * F.gamA A a) *
          (↑g⁻¹ : Matrix N N A)
        = (g : Matrix N N A) * F.gamA A a * 1 * F.gamA A b * (↑g⁻¹ : Matrix N N A) +
            (g : Matrix N N A) * F.gamA A b * 1 * F.gamA A a * (↑g⁻¹ : Matrix N N A) := by
          noncomm_ring
      _ = _ := by rw [← hgg]; noncomm_ring
  have h1 : (∑ c, F.rho A g c a • F.gamA A c) * (∑ d, F.rho A g d b • F.gamA A d) =
      ∑ c, ∑ d, (F.rho A g c a * F.rho A g d b) • (F.gamA A c * F.gamA A d) := by
    rw [Finset.sum_mul_sum]
    simp only [smul_mul_smul_comm]
  have h2 : (∑ d, F.rho A g d b • F.gamA A d) * (∑ c, F.rho A g c a • F.gamA A c) =
      ∑ c, ∑ d, (F.rho A g c a * F.rho A g d b) • (F.gamA A d * F.gamA A c) := by
    rw [Finset.sum_mul_sum, Finset.sum_comm]
    simp only [smul_mul_smul_comm, mul_comm (F.rho A g _ b)]
  have hab : (g : Matrix N N A) * (F.gamA A a * F.gamA A b + F.gamA A b * F.gamA A a) *
      (↑g⁻¹ : Matrix N N A) = algebraMap A (Matrix N N A) (bm a b) := by
    rw [gamA_anticomm, ← Algebra.commutes, mul_assoc, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, mul_one]
  have key : algebraMap A (Matrix N N A) (bm a b) = algebraMap A (Matrix N N A)
      (∑ c, ∑ d, F.rho A g c a * F.rho A g d b * (bm c d : A)) := by
    rw [← hab, e, conj_gamA hg, conj_gamA hg, h1, h2, ← Finset.sum_add_distrib, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.sum_add_distrib, map_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← smul_add, gamA_anticomm, map_mul, Algebra.smul_def]
  obtain ⟨r⟩ := ‹Nonempty N›
  have h := congrFun (congrFun key r) r
  simp only [Algebra.algebraMap_eq_smul_one, Matrix.smul_apply, Matrix.one_apply_eq,
    smul_eq_mul, mul_one] at h
  change ((F.rho A g)ᵀ * (Int.castRingHom A).mapMatrix bm * F.rho A g) a b = ((bm a b : ℤ) : A)
  rw [h]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
    Int.coe_castRingHom, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  ring

section Root

variable (F A) {x y : ι}

@[expose] def rootMat (x y : ι) : Matrix N N A :=
  F.gamA A x * F.gamA A y

theorem gamA_anticomm_eq_zero (hxy : bm x y = 0) :
    F.gamA A x * F.gamA A y + F.gamA A y * F.gamA A x = 0 := by
  rw [gamA_anticomm, hxy, Int.cast_zero, map_zero]

theorem rootMat_sq (hxy : bm x y = 0) (hq : qd x * qd y = 0) :
    F.rootMat A x y * F.rootMat A x y = 0 :=
  mul_mul_mul_mul_eq_zero (F.gamA_anticomm_eq_zero A hxy) (F.gamA_sq A x) (F.gamA_sq A y)
    (cast_mul_eq_zero hq)

theorem rootMat_comm (z : ι) :
    F.rootMat A x y * F.gamA A z - F.gamA A z * F.rootMat A x y =
      ((bm y z : ℤ) : A) • F.gamA A x - ((bm x z : ℤ) : A) • F.gamA A y :=
  mul_mul_sub_eq (F.gamA_anticomm A x z) (F.gamA_anticomm A y z)

theorem rootMat_sandwich (hxy : bm x y = 0) (hq : qd x * qd y = 0) (z : ι) :
    F.rootMat A x y * F.gamA A z * F.rootMat A x y =
      (((bm y z : ℤ) : A) * (qd x : A)) • F.gamA A y +
        (((bm x z : ℤ) : A) * (qd y : A)) • F.gamA A x :=
  mul_mul_mul_mul_eq (F.gamA_anticomm_eq_zero A hxy) (F.gamA_sq A x) (F.gamA_sq A y)
    (cast_mul_eq_zero hq) (F.gamA_anticomm A x z) (F.gamA_anticomm A y z)

@[expose] def rootUnit (hxy : bm x y = 0) (hq : qd x * qd y = 0) (u : A) : GL N A where
  val := 1 + u • F.rootMat A x y
  inv := 1 - u • F.rootMat A x y
  val_inv := by
    rw [add_mul, one_mul, mul_sub, mul_one, smul_mul_smul_comm, F.rootMat_sq A hxy hq, smul_zero,
      sub_zero, sub_add_cancel]
  inv_val := by
    rw [sub_mul, one_mul, mul_add, mul_one, smul_mul_smul_comm, F.rootMat_sq A hxy hq, smul_zero,
      add_zero, add_sub_cancel_right]

theorem coe_rootUnit (hxy : bm x y = 0) (hq : qd x * qd y = 0) (u : A) :
    ((F.rootUnit A hxy hq u : GL N A) : Matrix N N A) = 1 + u • F.rootMat A x y :=
  rfl

theorem coe_rootUnit_inv (hxy : bm x y = 0) (hq : qd x * qd y = 0) (u : A) :
    (↑(F.rootUnit A hxy hq u)⁻¹ : Matrix N N A) = 1 - u • F.rootMat A x y :=
  rfl

theorem one_add_smul_mul_mul_one_sub_smul (u : A) (X Z : Matrix N N A) :
    (1 + u • X) * Z * (1 - u • X) = Z + u • (X * Z - Z * X) - (u * u) • (X * Z * X) := by
  simp only [add_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, mul_assoc]
  module

theorem rootUnit_conj (hxy : bm x y = 0) (hq : qd x * qd y = 0) (u : A) (z : ι) :
    ((F.rootUnit A hxy hq u : GL N A) : Matrix N N A) * F.gamA A z *
        (↑(F.rootUnit A hxy hq u)⁻¹ : Matrix N N A) =
      F.gamA A z + u • (((bm y z : ℤ) : A) • F.gamA A x - ((bm x z : ℤ) : A) • F.gamA A y) -
        (u * u) • ((((bm y z : ℤ) : A) * (qd x : A)) • F.gamA A y +
          (((bm x z : ℤ) : A) * (qd y : A)) • F.gamA A x) := by
  rw [coe_rootUnit, coe_rootUnit_inv, one_add_smul_mul_mul_one_sub_smul, F.rootMat_comm A z,
    F.rootMat_sandwich A hxy hq z]

theorem inSpan_rootUnit_conj (hxy : bm x y = 0) (hq : qd x * qd y = 0) (u : A) (z : ι) :
    F.InSpan A (((F.rootUnit A hxy hq u : GL N A) : Matrix N N A) * F.gamA A z *
      (↑(F.rootUnit A hxy hq u)⁻¹ : Matrix N N A)) := by
  rw [rootUnit_conj]
  refine F.inSpan_sub A (F.inSpan_add A (F.inSpan_gamA A z) (F.inSpan_smul A u
    (F.inSpan_sub A (F.inSpan_smul A _ (F.inSpan_gamA A x))
      (F.inSpan_smul A _ (F.inSpan_gamA A y))))) (F.inSpan_smul A _ (F.inSpan_add A
    (F.inSpan_smul A _ (F.inSpan_gamA A y)) (F.inSpan_smul A _ (F.inSpan_gamA A x))))

theorem rootUnit_inv (hxy : bm x y = 0) (hq : qd x * qd y = 0) (u : A) :
    (F.rootUnit A hxy hq u)⁻¹ = F.rootUnit A hxy hq (-u) := by
  ext : 1
  rw [coe_rootUnit_inv, coe_rootUnit, neg_smul, sub_eq_add_neg]

theorem rootUnit_mem_normGroup (hxy : bm x y = 0) (hq : qd x * qd y = 0) (u : A) :
    F.rootUnit A hxy hq u ∈ F.normGroup A := by
  intro z
  refine ⟨F.inSpan_rootUnit_conj A hxy hq u z, ?_⟩
  have h := F.inSpan_rootUnit_conj A hxy hq (-u) z
  rwa [← rootUnit_inv, inv_inv] at h

theorem rho_rootUnit (hxy : bm x y = 0) (hq : qd x * qd y = 0) (u : A) (b z : ι) :
    F.rho A (F.rootUnit A hxy hq u) b z =
      (if b = z then 1 else 0) +
        u * (((bm y z : ℤ) : A) * (if b = x then 1 else 0) -
          ((bm x z : ℤ) : A) * (if b = y then 1 else 0)) -
        u * u * (((bm y z : ℤ) : A) * (qd x : A) * (if b = y then 1 else 0) +
          ((bm x z : ℤ) : A) * (qd y : A) * (if b = x then 1 else 0)) := by
  show F.coord A b _ = _
  rw [rootUnit_conj]
  simp only [coord_add, coord_smul, coord_gamA, sub_eq_add_neg, ← neg_one_smul A (_ : Matrix N N A)]
  ring

end Root

end Frame

abbrev BI (m : ℕ) : Type :=
  Fin m ⊕ Fin m ⊕ Unit

namespace BI

variable {m : ℕ}

abbrev cr (i : Fin m) : BI m :=
  .inl i

abbrev an (i : Fin m) : BI m :=
  .inr (.inl i)

abbrev zeta : BI m :=
  .inr (.inr ())

@[expose] def emb : Fin m ⊕ Fin m → BI m :=
  Sum.elim cr an

@[simp]
theorem emb_inl (i : Fin m) : emb (.inl i) = cr i :=
  rfl

@[simp]
theorem emb_inr (i : Fin m) : emb (.inr i) = an i :=
  rfl

theorem emb_injective : Function.Injective (emb (m := m)) := by
  rintro (i | i) (j | j) h <;> simp_all [emb]

theorem emb_ne_zeta (p : Fin m ⊕ Fin m) : emb p ≠ zeta := by
  rcases p with i | i <;> simp [emb]

theorem sum_eq {M : Type*} [AddCommMonoid M] (f : BI m → M) :
    ∑ a, f a = ∑ p, f (emb p) + f zeta := by
  simp only [Fintype.sum_sum_type, Fintype.univ_unit, Finset.sum_singleton, emb, Sum.elim_inl,
    Sum.elim_inr, add_assoc]

end BI

open BI

@[expose] def bmB (m : ℕ) : Matrix (BI m) (BI m) ℤ := fun a b =>
  match a, b with
  | .inl i, .inr (.inl j) => if i = j then 1 else 0
  | .inr (.inl i), .inl j => if i = j then 1 else 0
  | .inr (.inr _), .inr (.inr _) => 2
  | _, _ => 0

@[expose] def qdB (m : ℕ) : BI m → ℤ := fun a =>
  match a with
  | .inr (.inr _) => 1
  | _ => 0

namespace BI

variable {m : ℕ}

@[simp] theorem bmB_cr_cr (i j : Fin m) : bmB m (cr i) (cr j) = 0 := rfl
@[simp] theorem bmB_cr_an (i j : Fin m) : bmB m (cr i) (an j) = if i = j then 1 else 0 := rfl
@[simp] theorem bmB_an_cr (i j : Fin m) : bmB m (an i) (cr j) = if i = j then 1 else 0 := rfl
@[simp] theorem bmB_an_an (i j : Fin m) : bmB m (an i) (an j) = 0 := rfl
@[simp] theorem bmB_cr_zeta (i : Fin m) : bmB m (cr i) zeta = 0 := rfl
@[simp] theorem bmB_zeta_cr (i : Fin m) : bmB m zeta (cr i) = 0 := rfl
@[simp] theorem bmB_an_zeta (i : Fin m) : bmB m (an i) zeta = 0 := rfl
@[simp] theorem bmB_zeta_an (i : Fin m) : bmB m zeta (an i) = 0 := rfl
@[simp] theorem bmB_zeta_zeta : bmB m zeta zeta = 2 := rfl
@[simp] theorem qdB_cr (i : Fin m) : qdB m (cr i) = 0 := rfl
@[simp] theorem qdB_an (i : Fin m) : qdB m (an i) = 0 := rfl
@[simp] theorem qdB_zeta : qdB m zeta = 1 := rfl

theorem bmB_emb_zeta (p : Fin m ⊕ Fin m) : bmB m (emb p) zeta = 0 := by
  rcases p with i | i <;> rfl

theorem bmB_zeta_emb (p : Fin m ⊕ Fin m) : bmB m zeta (emb p) = 0 := by
  rcases p with i | i <;> rfl

theorem qdB_emb (p : Fin m ⊕ Fin m) : qdB m (emb p) = 0 := by
  rcases p with i | i <;> rfl

theorem cast_bmB_zeta {K : Type*} [CommRing K] (h2 : (2 : K) = 0) (b : BI m) :
    ((bmB m zeta b : ℤ) : K) = 0 := by
  rcases b with i | i | u
  · simp
  · simp
  · rw [show (Sum.inr (Sum.inr u) : BI m) = zeta from rfl, bmB_zeta_zeta, Int.cast_ofNat, h2]

theorem cast_bmB_zeta' {K : Type*} [CommRing K] (h2 : (2 : K) = 0) (b : BI m) :
    ((bmB m b zeta : ℤ) : K) = 0 := by
  rcases b with i | i | u
  · simp
  · simp
  · rw [show (Sum.inr (Sum.inr u) : BI m) = zeta from rfl, bmB_zeta_zeta, Int.cast_ofNat, h2]

theorem cast_bmB_emb {K : Type*} [CommRing K] (h2 : (2 : K) = 0) (p q : Fin m ⊕ Fin m) :
    ((bmB m (emb p) (emb q) : ℤ) : K) = Matrix.J (Fin m) K p q := by
  have hneg : (-1 : K) = 1 := by
    rw [neg_eq_iff_add_eq_zero, one_add_one_eq_two, h2]
  rcases p with i | i <;> rcases q with j | j <;>
    simp [Matrix.J, Matrix.fromBlocks, Matrix.one_apply, apply_ite (Int.cast : ℤ → K)]
  split_ifs <;> simp [hneg]

end BI

namespace Frame

variable {m : ℕ} {N : Type} [Fintype N] [DecidableEq N]
  (F : Frame (bmB m) (qdB m) N) {K : Type*} [Field K]

open BI

theorem rho_zeta [Nonempty N] (h2 : (2 : K) = 0) {g : GL N K} (hg : g ∈ F.normGroup K) {a : BI m}
    (ha : a ≠ zeta) : F.rho K g a zeta = 0 := by
  set R := F.rho K g
  have hR := rho_transpose_mul_mul_rho hg
  set w : BI m → K := fun d => ∑ c, R c zeta * ((bmB m c d : ℤ) : K) with hw
  have hwR : w ᵥ* R = 0 := by
    funext b
    have h := congrFun (congrFun hR zeta) b
    simp only [Matrix.mul_apply, Matrix.transpose_apply, RingHom.mapMatrix_apply,
      Matrix.map_apply, Int.coe_castRingHom, cast_bmB_zeta h2] at h
    simp only [Matrix.vecMul, dotProduct, hw, Pi.zero_apply]
    rw [← h]
  have hinv : R * F.rho K g⁻¹ = 1 := by
    rw [← rho_mul hg (inv_mem hg), mul_inv_cancel, rho_one]
  have hw0 : w = 0 := by
    rw [← Matrix.vecMul_one w, ← hinv, ← Matrix.vecMul_vecMul, hwR, Matrix.zero_vecMul]
  rcases a with i | i | u
  · have h := congrFun hw0 (an i)
    simp only [hw, Pi.zero_apply] at h
    rw [BI.sum_eq] at h
    simpa [emb, Fintype.sum_sum_type, apply_ite (Int.cast : ℤ → K), Finset.sum_ite_eq] using h
  · have h := congrFun hw0 (cr i)
    simp only [hw, Pi.zero_apply] at h
    rw [BI.sum_eq] at h
    simpa [emb, Fintype.sum_sum_type, apply_ite (Int.cast : ℤ → K), Finset.sum_ite_eq] using h
  · exact absurd rfl ha

@[expose] def sympMat (g : GL N K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K :=
  fun p q => F.rho K g (emb p) (emb q)

theorem sympMat_mul [Nonempty N] (h2 : (2 : K) = 0) {g h : GL N K} (hg : g ∈ F.normGroup K)
    (hh : h ∈ F.normGroup K) : F.sympMat (g * h) = F.sympMat g * F.sympMat h := by
  ext p q
  simp only [sympMat, rho_mul hg hh, Matrix.mul_apply]
  rw [BI.sum_eq, F.rho_zeta h2 hg (emb_ne_zeta p), zero_mul, add_zero]

theorem sympMat_one : F.sympMat (1 : GL N K) = 1 := by
  ext p q
  simp only [sympMat, rho_one, Matrix.one_apply, emb_injective.eq_iff]

theorem sympMat_transpose_mul_J_mul [Nonempty N] (h2 : (2 : K) = 0) {g : GL N K}
    (hg : g ∈ F.normGroup K) :
    (F.sympMat g)ᵀ * Matrix.J (Fin m) K * F.sympMat g = Matrix.J (Fin m) K := by
  ext p q
  have h := congrFun (congrFun (rho_transpose_mul_mul_rho hg) (emb p)) (emb q)
  simp only [Matrix.mul_apply, Matrix.transpose_apply, RingHom.mapMatrix_apply,
    Matrix.map_apply, Int.coe_castRingHom] at h
  rw [← cast_bmB_emb h2, ← h]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, sympMat, BI.sum_eq, cast_bmB_zeta h2,
    cast_bmB_zeta' h2, cast_bmB_emb h2, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]

@[expose] def symplecticHom [Nonempty N] (h2 : (2 : K) = 0) :
    F.normGroup K →* TauCeti.GLSymplectic (Fin m) K where
  toFun g := ⟨⟨F.sympMat (g : GL N K), F.sympMat (g : GL N K)⁻¹, by
      rw [← sympMat_mul F h2 g.2 (inv_mem g.2), mul_inv_cancel, sympMat_one], by
      rw [← sympMat_mul F h2 (inv_mem g.2) g.2, inv_mul_cancel, sympMat_one]⟩,
    TauCeti.GLSymplectic.mem_iff'.2 (F.sympMat_transpose_mul_J_mul h2 g.2)⟩
  map_one' := Subtype.ext (Units.ext F.sympMat_one)
  map_mul' g h := Subtype.ext (Units.ext (F.sympMat_mul h2 g.2 h.2))

theorem coe_symplecticHom [Nonempty N] (h2 : (2 : K) = 0) (g : F.normGroup K) :
    (((F.symplecticHom h2 g : TauCeti.GLSymplectic (Fin m) K) : GL (Fin m ⊕ Fin m) K) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) = F.sympMat (g : GL N K) :=
  rfl

theorem add_smul_mul_add_smul {R : Type*} [Ring R] [Algebra K R] (X Y : R) (μ : K) :
    (X + μ • Y) * (X + μ • Y) = X * X + μ • (X * Y + Y * X) + (μ * μ) • (Y * Y) := by
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul]
  abel

theorem conj_mul_conj {g : GL N K} (b : BI m) :
    ((g : Matrix N N K) * F.gamA K b * (↑g⁻¹ : Matrix N N K)) *
      ((g : Matrix N N K) * F.gamA K b * (↑g⁻¹ : Matrix N N K)) =
      algebraMap K (Matrix N N K) (qdB m b) := by
  have hgg : (↑g⁻¹ : Matrix N N K) * (g : Matrix N N K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc ((g : Matrix N N K) * F.gamA K b * (↑g⁻¹ : Matrix N N K)) *
        ((g : Matrix N N K) * F.gamA K b * (↑g⁻¹ : Matrix N N K))
      = (g : Matrix N N K) * F.gamA K b * ((↑g⁻¹ : Matrix N N K) * (g : Matrix N N K)) *
          F.gamA K b * (↑g⁻¹ : Matrix N N K) := by noncomm_ring
    _ = (g : Matrix N N K) * (F.gamA K b * F.gamA K b) * (↑g⁻¹ : Matrix N N K) := by
        rw [hgg]; noncomm_ring
    _ = _ := by
        rw [gamA_sq, ← Algebra.commutes, mul_assoc, ← Units.val_mul, mul_inv_cancel,
          Units.val_one, mul_one]

theorem rho_eq_one_of_symplecticHom_eq_one [Nonempty N] (h2 : (2 : K) = 0) {g : F.normGroup K}
    (hg1 : F.symplecticHom h2 g = 1) : F.rho K g = 1 := by
  have hS : F.sympMat (g : GL N K) = 1 := by
    have := congrArg (fun x : TauCeti.GLSymplectic (Fin m) K =>
      ((x : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)) hg1
    simpa only [coe_symplecticHom, OneMemClass.coe_one, Units.val_one] using this
  have hemb : ∀ p q, F.rho K g (emb p) (emb q) = if p = q then 1 else 0 := fun p q => by
    have := congrFun (congrFun hS p) q
    rwa [Matrix.one_apply] at this
  have hinj : ∀ {c : K}, algebraMap K (Matrix N N K) c = 0 → c = 0 := fun {c} h =>
    (algebraMap K (Matrix N N K)).injective (h.trans (map_zero _).symm)
  have hz : F.rho K g zeta zeta = 1 := by
    have h := F.conj_mul_conj (g := (g : GL N K)) zeta
    rw [conj_gamA g.2, BI.sum_eq] at h
    simp only [F.rho_zeta h2 g.2 (emb_ne_zeta _), zero_smul, Finset.sum_const_zero,
      zero_add] at h
    rw [smul_mul_smul_comm, gamA_sq, qdB_zeta, Int.cast_one, map_one, Algebra.smul_def,
      mul_one] at h
    have h1 : F.rho K g zeta zeta * F.rho K g zeta zeta - 1 = 0 :=
      hinj (by rw [map_sub, h, map_one, sub_self])
    have hsq : (F.rho K g zeta zeta - 1) * (F.rho K g zeta zeta - 1) = 0 := by
      have e : (F.rho K g zeta zeta - 1) * (F.rho K g zeta zeta - 1) =
          (F.rho K g zeta zeta * F.rho K g zeta zeta - 1) - 2 * (F.rho K g zeta zeta - 1) := by
        ring
      rw [e, h1, h2, zero_mul, sub_zero]
    exact sub_eq_zero.1 (mul_self_eq_zero.1 hsq)
  have hq : ∀ q, F.rho K g zeta (emb q) = 0 := fun q => by
    have h := F.conj_mul_conj (g := (g : GL N K)) (emb q)
    rw [conj_gamA g.2, BI.sum_eq] at h
    simp only [hemb, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true] at h
    rw [add_smul_mul_add_smul, gamA_sq, gamA_sq, gamA_anticomm, qdB_emb, bmB_emb_zeta, qdB_zeta,
      Int.cast_zero, Int.cast_one, map_zero, map_one, smul_zero, zero_add, zero_add,
      Algebra.smul_def, mul_one] at h
    exact mul_self_eq_zero.1 (hinj h)
  ext b a
  rcases a with i | i | u
  · rcases b with j | j | v
    · exact (hemb (.inl j) (.inl i)).trans (by simp [Matrix.one_apply])
    · exact (hemb (.inr j) (.inl i)).trans (by simp)
    · exact (hq (.inl i)).trans (by simp)
  · rcases b with j | j | v
    · exact (hemb (.inl j) (.inr i)).trans (by simp)
    · exact (hemb (.inr j) (.inr i)).trans (by simp [Matrix.one_apply])
    · exact (hq (.inr i)).trans (by simp)
  · rcases b with j | j | v
    · exact (F.rho_zeta h2 g.2 (emb_ne_zeta (.inl j))).trans (by simp)
    · exact (F.rho_zeta h2 g.2 (emb_ne_zeta (.inr j))).trans (by simp)
    · exact hz.trans (by simp)

theorem bmB_cr_an_eq_zero {j k : Fin m} (hjk : j ≠ k) : bmB m (cr j) (an k) = 0 := by
  simp [hjk]

theorem qdB_cr_mul_qdB_an (j k : Fin m) : qdB m (cr j) * qdB m (an k) = 0 := rfl

theorem qdB_cr_mul_qdB_zeta (k : Fin m) : qdB m (cr k) * qdB m zeta = 0 := rfl

theorem qdB_zeta_mul_qdB_an (k : Fin m) : qdB m zeta * qdB m (an k) = 0 := rfl

theorem sympMat_rootUnit_cr_an {j k : Fin m} (hjk : j ≠ k) (u : K) :
    F.sympMat (F.rootUnit K (bmB_cr_an_eq_zero hjk) (qdB_cr_mul_qdB_an j k) u) =
      1 + Matrix.single (Sum.inl j) (Sum.inl k) u - Matrix.single (Sum.inr k) (Sum.inr j) u := by
  ext p q
  simp only [sympMat, rho_rootUnit, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply,
    emb_injective.eq_iff, Matrix.single_apply]
  rcases p with a | a <;> rcases q with b | b
  all_goals simp [emb, apply_ite (Int.cast : ℤ → K), ite_and, eq_comm]
  all_goals split_ifs <;> simp_all

theorem sympMat_rootUnit_cr_zeta (k : Fin m) (u : K) :
    F.sympMat (F.rootUnit K (bmB_cr_zeta k) (qdB_cr_mul_qdB_zeta k) u) =
      1 + Matrix.single (Sum.inl k) (Sum.inr k) (-(u * u)) := by
  ext p q
  simp only [sympMat, rho_rootUnit, Matrix.add_apply, Matrix.one_apply,
    emb_injective.eq_iff, Matrix.single_apply]
  rcases p with a | a <;> rcases q with b | b
  all_goals simp [emb, apply_ite (Int.cast : ℤ → K), ite_and, eq_comm]
  all_goals split_ifs <;> simp_all

theorem sympMat_rootUnit_zeta_an (k : Fin m) (u : K) :
    F.sympMat (F.rootUnit K (bmB_zeta_an k) (qdB_zeta_mul_qdB_an k) u) =
      1 + Matrix.single (Sum.inr k) (Sum.inl k) (-(u * u)) := by
  ext p q
  simp only [sympMat, rho_rootUnit, Matrix.add_apply, Matrix.one_apply,
    emb_injective.eq_iff, Matrix.single_apply]
  rcases p with a | a <;> rcases q with b | b
  all_goals simp [emb, apply_ite (Int.cast : ℤ → K), ite_and, eq_comm]
  all_goals split_ifs <;> simp_all

end Frame

abbrev DI (m : ℕ) : Type :=
  Fin m ⊕ Fin m

@[expose] def bmD (m : ℕ) : Matrix (DI m) (DI m) ℤ := fun a b =>
  match a, b with
  | .inl i, .inr j => if i = j then 1 else 0
  | .inr i, .inl j => if i = j then 1 else 0
  | _, _ => 0

@[expose] def qdD (m : ℕ) : DI m → ℤ := fun _ => 0

section TypeD

variable {m : ℕ}

@[simp] theorem bmD_inl_inl (i j : Fin m) : bmD m (.inl i) (.inl j) = 0 := rfl
@[simp] theorem bmD_inl_inr (i j : Fin m) : bmD m (.inl i) (.inr j) = if i = j then 1 else 0 := rfl
@[simp] theorem bmD_inr_inl (i j : Fin m) : bmD m (.inr i) (.inl j) = if i = j then 1 else 0 := rfl
@[simp] theorem bmD_inr_inr (i j : Fin m) : bmD m (.inr i) (.inr j) = 0 := rfl
@[simp] theorem qdD_apply (a : DI m) : qdD m a = 0 := rfl

theorem sum_smul_mul_self_eq_zero {A : Type*} [CommRing A] {R : Type*} [Ring R] [Algebra A R]
    {κ : Type*} [DecidableEq κ] (s : Finset κ) (x : κ → A) (X : κ → R)
    (hsq : ∀ i, X i * X i = 0) (hanti : ∀ i j, i ≠ j → X i * X j + X j * X i = 0) :
    (∑ i ∈ s, x i • X i) * (∑ i ∈ s, x i • X i) = 0 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have hc : (∑ i ∈ s, x i • X i) * X a + X a * (∑ i ∈ s, x i • X i) = 0 := by
      rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun i hi => ?_
      rw [smul_mul_assoc, mul_smul_comm, ← smul_add, hanti i a (fun h => ha (h ▸ hi)),
        smul_zero]
    have e : (x a • X a + ∑ i ∈ s, x i • X i) * (x a • X a + ∑ i ∈ s, x i • X i) =
        (x a * x a) • (X a * X a) + x a • ((∑ i ∈ s, x i • X i) * X a +
          X a * (∑ i ∈ s, x i • X i)) + (∑ i ∈ s, x i • X i) * (∑ i ∈ s, x i • X i) := by
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul]
      abel
    rw [e, hsq, hc, ih, smul_zero, smul_zero, add_zero, add_zero]

namespace Frame

variable {N : Type} [Fintype N] [DecidableEq N] (F : Frame (bmD m) (qdD m) N)
  (A : Type*) [CommRing A]

theorem vec_mul_vec_D (c : DI m → A) :
    F.vec A c * F.vec A c = algebraMap A (Matrix N N A) (∑ i, c (.inl i) * c (.inr i)) := by
  set X : Matrix N N A := ∑ i, c (.inl i) • F.gamA A (.inl i)
  set Y : Matrix N N A := ∑ i, c (.inr i) • F.gamA A (.inr i)
  have hv : F.vec A c = X + Y := by
    rw [vec, Fintype.sum_sum_type]
  have hX : X * X = 0 := sum_smul_mul_self_eq_zero _ _ _
    (fun i => by rw [gamA_sq, qdD_apply, Int.cast_zero, map_zero])
    (fun i j _ => by rw [gamA_anticomm, bmD_inl_inl, Int.cast_zero, map_zero])
  have hY : Y * Y = 0 := sum_smul_mul_self_eq_zero _ _ _
    (fun i => by rw [gamA_sq, qdD_apply, Int.cast_zero, map_zero])
    (fun i j _ => by rw [gamA_anticomm, bmD_inr_inr, Int.cast_zero, map_zero])
  have hXY : X * Y + Y * X =
      algebraMap A (Matrix N N A) (∑ i, c (.inl i) * c (.inr i)) := by
    have e : ∀ i j, (c (.inl i) • F.gamA A (.inl i)) * (c (.inr j) • F.gamA A (.inr j)) +
        (c (.inr j) • F.gamA A (.inr j)) * (c (.inl i) • F.gamA A (.inl i)) =
        algebraMap A (Matrix N N A) (if i = j then c (.inl i) * c (.inr j) else 0) := by
      intro i j
      rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm (c (.inr j)), ← smul_add,
        gamA_anticomm, bmD_inl_inr, Algebra.smul_def, ← map_mul]
      split_ifs <;> simp
    have hYX : Y * X = ∑ i, ∑ j,
        (c (.inr j) • F.gamA A (.inr j)) * (c (.inl i) • F.gamA A (.inl i)) := by
      rw [Finset.sum_mul_sum, Finset.sum_comm]
    rw [Finset.sum_mul_sum, hYX, ← Finset.sum_add_distrib]
    simp_rw [← Finset.sum_add_distrib, e]
    rw [show (∑ x : Fin m, ∑ y : Fin m, algebraMap A (Matrix N N A)
        (if x = y then c (.inl x) * c (.inr y) else 0)) = algebraMap A (Matrix N N A)
        (∑ x : Fin m, ∑ y : Fin m, if x = y then c (.inl x) * c (.inr y) else 0) by
      simp only [map_sum]]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_ite_eq Finset.univ i, ite_eq_left (Finset.mem_univ i)]
  rw [hv, add_mul, mul_add, mul_add, hX, hY, zero_add, add_zero, hXY]

variable {F A}

theorem plusQuad_rho [Nonempty N] {K : Type*} [Field K] {g : GL N K} (hg : g ∈ F.normGroup K)
    (c : DI m → K) :
    ∑ i, (F.rho K g *ᵥ c) (.inl i) * (F.rho K g *ᵥ c) (.inr i) =
      ∑ i, c (.inl i) * c (.inr i) := by
  have h1 := F.vec_mul_vec_D K (F.rho K g *ᵥ c)
  have h2 : F.vec K (F.rho K g *ᵥ c) * F.vec K (F.rho K g *ᵥ c) =
      (g : Matrix N N K) * (F.vec K c * F.vec K c) * (↑g⁻¹ : Matrix N N K) := by
    have hgg : (↑g⁻¹ : Matrix N N K) * (g : Matrix N N K) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [← conj_vec hg]
    calc (g : Matrix N N K) * F.vec K c * (↑g⁻¹ : Matrix N N K) *
          ((g : Matrix N N K) * F.vec K c * (↑g⁻¹ : Matrix N N K))
        = (g : Matrix N N K) * F.vec K c * ((↑g⁻¹ : Matrix N N K) * (g : Matrix N N K)) *
            F.vec K c * (↑g⁻¹ : Matrix N N K) := by noncomm_ring
      _ = _ := by rw [hgg]; noncomm_ring
  rw [h1, F.vec_mul_vec_D K c, ← Algebra.commutes, mul_assoc, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, mul_one] at h2
  exact (algebraMap K (Matrix N N K)).injective h2

@[expose] def orthHom : F.normGroup A →* GL (DI m) A where
  toFun g := ⟨F.rho A g, F.rho A (g : GL N A)⁻¹, by
      rw [← rho_mul g.2 (inv_mem g.2), mul_inv_cancel, rho_one], by
      rw [← rho_mul (inv_mem g.2) g.2, inv_mul_cancel, rho_one]⟩
  map_one' := Units.ext rho_one
  map_mul' g h := Units.ext (rho_mul g.2 h.2)

theorem coe_orthHom (g : F.normGroup A) :
    ((F.orthHom (A := A) g : GL (DI m) A) : Matrix (DI m) (DI m) A) = F.rho A g :=
  rfl

end Frame

end TypeD

end CFSG.RankThree.PartTwo.Census.Carrier.SpinFrame
