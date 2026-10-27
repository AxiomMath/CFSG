module

public import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin.NoE9Z4MinGrp

open scoped commutatorElement

variable {G : Type*} [Group G]

structure PairCtx (Q U Z Hs : Subgroup G) (z : G) : Prop where
  z_ne : z ≠ 1
  z_mem : z ∈ Z
  Z_eq : ∀ g ∈ Z, g = 1 ∨ g = z
  Z_le_U : Z ≤ U
  U_le_Q : U ≤ Q
  Q_le_H : Q ≤ Hs
  U_comm : ∀ u ∈ U, ∀ u' ∈ U, u * u' = u' * u
  U_sq : ∀ u ∈ U, u * u = 1
  z_cent : ∀ h ∈ Hs, h * z = z * h
  normQ : ∀ h ∈ Hs, ∀ x ∈ Q, h * x * h⁻¹ ∈ Q
  normU : ∀ h ∈ Hs, ∀ u ∈ U, h * u * h⁻¹ ∈ U
  pair_mem : ∀ u ∈ U, ∀ x ∈ Q, ⁅u, x⁆ ∈ Z
  ker_left : ∀ x ∈ Q, (∀ u ∈ U, ⁅u, x⁆ = 1) → x ∈ U
  ker_right : ∀ u ∈ U, (∀ x ∈ Q, ⁅u, x⁆ = 1) → u ∈ Z

namespace PairCtx

variable {Q U Z Hs : Subgroup G} {z : G} (P : PairCtx Q U Z Hs z)
include P

@[expose] def T (x y q : G) : G := ⁅⁅x, y⁆, q⁆

theorem Z_central {h : G} (hh : h ∈ Hs) {c : G} (hc : c ∈ Z) : h * c = c * h := by
  rcases P.Z_eq c hc with rfl | rfl
  · simp
  · exact P.z_cent h hh

theorem Z_comm {c c' : G} (hc : c ∈ Z) (hc' : c' ∈ Z) : c * c' = c' * c := by
  rcases P.Z_eq c hc with rfl | rfl
  · simp
  · rcases P.Z_eq c' hc' with rfl | rfl
    · simp
    · rfl

theorem Z_sq {c : G} (hc : c ∈ Z) : c * c = 1 := P.U_sq c (P.Z_le_U hc)

theorem U_le_H : U ≤ Hs := P.U_le_Q.trans P.Q_le_H

theorem pair_U_U {c u : G} (hc : c ∈ U) (hu : u ∈ U) : ⁅c, u⁆ = 1 := by
  rw [commutatorElement_def, P.U_comm c hc u hu]
  group

theorem pair_one_of_mem_Z {c : G} (hc : c ∈ Z) {x : G} (hx : x ∈ Q) : ⁅c, x⁆ = 1 := by
  have h := P.Z_central (P.Q_le_H hx) hc
  rw [commutatorElement_def, ← h]
  group

theorem pair_mul_left {u u' : G} (hu : u ∈ U) (hu' : u' ∈ U) {x : G} (hx : x ∈ Q) :
    ⁅u * u', x⁆ = ⁅u, x⁆ * ⁅u', x⁆ := by
  have hc' : u * ⁅u', x⁆ = ⁅u', x⁆ * u := P.Z_central (P.U_le_H hu) (P.pair_mem u' hu' x hx)
  have h1 : ⁅u * u', x⁆ = ⁅u', x⁆ * ⁅u, x⁆ := by
    have h2 : u * (u' * x * u'⁻¹ * x⁻¹) = (u' * x * u'⁻¹ * x⁻¹) * u := hc'
    calc ⁅u * u', x⁆ = u * (u' * x * u'⁻¹ * x⁻¹) * (x * u⁻¹ * x⁻¹) := by
          simp only [commutatorElement_def]; group
      _ = (u' * x * u'⁻¹ * x⁻¹) * u * (x * u⁻¹ * x⁻¹) := by rw [h2]
      _ = ⁅u', x⁆ * ⁅u, x⁆ := by simp only [commutatorElement_def]; group
  rw [h1]
  exact P.Z_comm (P.pair_mem u' hu' x hx) (P.pair_mem u hu x hx)

theorem pair_mul_right {u : G} (hu : u ∈ U) {x x' : G} (hx : x ∈ Q) (hx' : x' ∈ Q) :
    ⁅u, x * x'⁆ = ⁅u, x⁆ * ⁅u, x'⁆ := by
  have hc' : x * ⁅u, x'⁆ = ⁅u, x'⁆ * x := P.Z_central (P.Q_le_H hx) (P.pair_mem u hu x' hx')
  have h2 : x * (u * x' * u⁻¹ * x'⁻¹) = (u * x' * u⁻¹ * x'⁻¹) * x := hc'
  calc ⁅u, x * x'⁆ = (u * x * u⁻¹ * x⁻¹) * (x * (u * x' * u⁻¹ * x'⁻¹)) * x⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = (u * x * u⁻¹ * x⁻¹) * ((u * x' * u⁻¹ * x'⁻¹) * x) * x⁻¹ := by rw [h2]
    _ = ⁅u, x⁆ * ⁅u, x'⁆ := by simp only [commutatorElement_def]; group

theorem pair_sq {u : G} (hu : u ∈ U) {x : G} (hx : x ∈ Q) : ⁅u, x⁆ * ⁅u, x⁆ = 1 :=
  P.Z_sq (P.pair_mem u hu x hx)

theorem pair_conj {h : G} (hh : h ∈ Hs) {u : G} (hu : u ∈ U) {x : G} (hx : x ∈ Q) :
    ⁅h * u * h⁻¹, h * x * h⁻¹⁆ = ⁅u, x⁆ := by
  have hc := P.Z_central hh (P.pair_mem u hu x hx)
  calc ⁅h * u * h⁻¹, h * x * h⁻¹⁆ = h * ⁅u, x⁆ * h⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = ⁅u, x⁆ := by rw [hc]; group

theorem pair_inv_right {u : G} (hu : u ∈ U) {x : G} (hx : x ∈ Q) :
    ⁅u, x⁻¹⁆ = ⁅u, x⁆⁻¹ := by
  have h := P.pair_mul_right hu (inv_mem hx) hx
  rw [inv_mul_cancel, commutatorElement_def] at h
  simp only [commutatorElement_def] at h ⊢
  have h' : u * 1 * u⁻¹ * 1⁻¹ = 1 := by group
  rw [h'] at h
  exact eq_inv_of_mul_eq_one_left h.symm

theorem pair_ext {x y : G} (hx : x ∈ Q) (hy : y ∈ Q) (h : ∀ u ∈ U, ⁅u, x⁆ = ⁅u, y⁆) :
    x⁻¹ * y ∈ U := by
  refine P.ker_left _ (Q.mul_mem (inv_mem hx) hy) fun u hu => ?_
  rw [P.pair_mul_right hu (inv_mem hx) hy, P.pair_inv_right hu hx, h u hu]
  exact inv_mul_cancel _

theorem comm_mem_U {x y : G} (hx : x ∈ Q) (hy : y ∈ Q) : ⁅x, y⁆ ∈ U := by
  have h1 : (y * x)⁻¹ * (x * y) ∈ U := by
    refine P.pair_ext (Q.mul_mem hy hx) (Q.mul_mem hx hy) fun u hu => ?_
    rw [P.pair_mul_right hu hy hx, P.pair_mul_right hu hx hy]
    exact P.Z_comm (P.pair_mem u hu y hy) (P.pair_mem u hu x hx)
  have h2 := P.normU (y * x) (P.Q_le_H (Q.mul_mem hy hx)) _ h1
  have : y * x * ((y * x)⁻¹ * (x * y)) * (y * x)⁻¹ = ⁅x, y⁆ := by
    simp only [commutatorElement_def]; group
  rwa [this] at h2

theorem sq_mem_U {x : G} (hx : x ∈ Q) : x * x ∈ U := by
  have h := P.pair_ext (Q.mul_mem hx hx) (Q.one_mem) fun u hu => by
    rw [P.pair_mul_right hu hx hx, P.pair_sq hu hx]
    simp [commutatorElement_def]
  simpa using inv_mem h

theorem T_mem_Z {x y q : G} (hx : x ∈ Q) (hy : y ∈ Q) (hq : q ∈ Q) : T x y q ∈ Z :=
  P.pair_mem _ (P.comm_mem_U hx hy) q hq

theorem T_of_mem_U_left {x y q : G} (hx : x ∈ U) (hy : y ∈ Q) (hq : q ∈ Q) :
    T x y q = 1 :=
  P.pair_one_of_mem_Z (P.pair_mem x hx y hy) hq

theorem pair_conj_comm {x : G} (hx : x ∈ Q) {c : G} (hc : c ∈ U) {q : G} (hq : q ∈ Q) :
    ⁅x * c * x⁻¹, q⁆ = ⁅c, q⁆ := by
  have h1 : x⁻¹ * q * x = q * ⁅q⁻¹, x⁻¹⁆ := by
    simp only [commutatorElement_def]; group
  have h2 : ⁅q⁻¹, x⁻¹⁆ ∈ U := P.comm_mem_U (inv_mem hq) (inv_mem hx)
  have h3 := P.pair_conj (P.Q_le_H hx) hc (Q.mul_mem (Q.mul_mem (inv_mem hx) hq) hx)
  have h4 : x * (x⁻¹ * q * x) * x⁻¹ = q := by group
  rw [h4] at h3
  rw [h3, h1, P.pair_mul_right hc hq (P.U_le_Q h2)]
  rw [P.pair_U_U hc h2, mul_one]

theorem T_mul_left {x x' y q : G} (hx : x ∈ Q) (hx' : x' ∈ Q) (hy : y ∈ Q) (hq : q ∈ Q) :
    T (x * x') y q = T x y q * T x' y q := by
  have hA : x * ⁅x', y⁆ * x⁻¹ ∈ U := P.normU x (P.Q_le_H hx) _ (P.comm_mem_U hx' hy)
  have hB : ⁅x, y⁆ ∈ U := P.comm_mem_U hx hy
  have e : ⁅x * x', y⁆ = (x * ⁅x', y⁆ * x⁻¹) * ⁅x, y⁆ := by
    simp only [commutatorElement_def]; group
  unfold T
  rw [e, P.pair_mul_left hA hB hq, P.pair_conj_comm hx (P.comm_mem_U hx' hy) hq]
  exact P.Z_comm (P.pair_mem _ (P.comm_mem_U hx' hy) q hq) (P.pair_mem _ hB q hq)

theorem T_mul_mid {x y y' q : G} (hx : x ∈ Q) (hy : y ∈ Q) (hy' : y' ∈ Q) (hq : q ∈ Q) :
    T x (y * y') q = T x y q * T x y' q := by
  have hA : ⁅x, y⁆ ∈ U := P.comm_mem_U hx hy
  have hB : y * ⁅x, y'⁆ * y⁻¹ ∈ U := P.normU y (P.Q_le_H hy) _ (P.comm_mem_U hx hy')
  have e : ⁅x, y * y'⁆ = ⁅x, y⁆ * (y * ⁅x, y'⁆ * y⁻¹) := by
    simp only [commutatorElement_def]; group
  unfold T
  rw [e, P.pair_mul_left hA hB hq, P.pair_conj_comm hy (P.comm_mem_U hx hy') hq]

theorem T_mul_right {x y q q' : G} (hx : x ∈ Q) (hy : y ∈ Q) (hq : q ∈ Q) (hq' : q' ∈ Q) :
    T x y (q * q') = T x y q * T x y q' :=
  P.pair_mul_right (P.comm_mem_U hx hy) hq hq'

omit P in
theorem T_self (x q : G) : T x x q = 1 := by
  unfold T
  simp [commutatorElement_def]

theorem T_swap {x y q : G} (hx : x ∈ Q) (hy : y ∈ Q) (hq : q ∈ Q) : T y x q = T x y q := by
  have h : ⁅y, x⁆ = ⁅x, y⁆⁻¹ := (commutatorElement_inv x y).symm
  have hU := P.comm_mem_U hx hy
  have h2 := P.pair_mul_left (inv_mem hU) hU hq
  rw [inv_mul_cancel] at h2
  have h3 : ⁅(1 : G), q⁆ = 1 := by simp [commutatorElement_def]
  rw [h3] at h2
  have h4 := P.pair_sq hU hq
  unfold T
  rw [h]
  have h5 : ⁅⁅x, y⁆⁻¹, q⁆ = ⁅⁅x, y⁆, q⁆⁻¹ := eq_inv_of_mul_eq_one_left h2.symm
  rw [h5]
  exact (eq_inv_of_mul_eq_one_left h4).symm

theorem T_congr_left {x x' y q : G} (hx : x ∈ Q) (hx' : x' ∈ Q) (hy : y ∈ Q) (hq : q ∈ Q)
    (h : x⁻¹ * x' ∈ U) : T x y q = T x' y q := by
  have h1 := P.T_mul_left hx (Q.mul_mem (inv_mem hx) hx') hy hq
  rw [mul_inv_cancel_left, P.T_of_mem_U_left h hy hq, mul_one] at h1
  exact h1.symm

theorem T_congr_mid {x y y' q : G} (hx : x ∈ Q) (hy : y ∈ Q) (hy' : y' ∈ Q) (hq : q ∈ Q)
    (h : y⁻¹ * y' ∈ U) : T x y q = T x y' q := by
  have hu : y⁻¹ * y' ∈ Q := Q.mul_mem (inv_mem hy) hy'
  have h1 := P.T_mul_mid hx hy hu hq
  rw [mul_inv_cancel_left, ← P.T_swap hx hu hq, P.T_of_mem_U_left h hx hq, mul_one] at h1
  exact h1.symm

theorem T_congr_right {x y q q' : G} (hx : x ∈ Q) (hy : y ∈ Q) (hq : q ∈ Q) (hq' : q' ∈ Q)
    (h : q⁻¹ * q' ∈ U) : T x y q = T x y q' := by
  have hu : q⁻¹ * q' ∈ Q := Q.mul_mem (inv_mem hq) hq'
  have h0 : T x y (q⁻¹ * q') = 1 := P.pair_U_U (P.comm_mem_U hx hy) h
  have h1 := P.T_mul_right hx hy hq hu
  rw [mul_inv_cancel_left, h0, mul_one] at h1
  exact h1.symm

theorem T_conj {h : G} (hh : h ∈ Hs) {x y q : G} (hx : x ∈ Q) (hy : y ∈ Q) (hq : q ∈ Q) :
    T (h * x * h⁻¹) (h * y * h⁻¹) (h * q * h⁻¹) = T x y q := by
  have e : ⁅h * x * h⁻¹, h * y * h⁻¹⁆ = h * ⁅x, y⁆ * h⁻¹ := by
    simp only [commutatorElement_def]; group
  unfold T
  rw [e]
  exact P.pair_conj hh (P.comm_mem_U hx hy) hq

theorem Q_comm_mem_Z {x y : G} (hx : x ∈ Q) (hy : y ∈ Q)
    (hT : ∀ q ∈ Q, T x y q = 1) : ⁅x, y⁆ ∈ Z :=
  P.ker_right _ (P.comm_mem_U hx hy) hT

theorem T_of_mem_U_right {x y q : G} (hx : x ∈ Q) (hy : y ∈ Q) (hq : q ∈ U) :
    T x y q = 1 :=
  P.pair_U_U (P.comm_mem_U hx hy) hq

theorem pair_conj_inv {h : G} (hh : h ∈ Hs) {u : G} (hu : u ∈ U) {x : G} (hx : x ∈ Q) :
    ⁅u, h * x * h⁻¹⁆ = ⁅h⁻¹ * u * h, x⁆ := by
  have h1 := P.pair_conj (inv_mem hh) hu (P.normQ h hh x hx)
  rw [← h1]
  congr 1 <;> group

theorem conj_of_comm_mem_Z {g u : G} (hg : g ∈ Hs) (h : ⁅g, u⁆ ∈ Z) :
    g * u * g⁻¹ = ⁅g, u⁆ * u ∧ g⁻¹ * u * g = ⁅g, u⁆ * u := by
  have e1 : g * u * g⁻¹ = ⁅g, u⁆ * u := by simp only [commutatorElement_def]; group
  refine ⟨e1, ?_⟩
  have hc := P.Z_central (inv_mem hg) h
  have hsq := P.Z_sq h
  have e2 : u = ⁅g, u⁆ * (g⁻¹ * u * g) := by
    calc u = g⁻¹ * (g * u * g⁻¹) * g := by group
      _ = g⁻¹ * (⁅g, u⁆ * u) * g := by rw [e1]
      _ = (g⁻¹ * ⁅g, u⁆) * (u * g) := by group
      _ = (⁅g, u⁆ * g⁻¹) * (u * g) := by rw [hc]
      _ = ⁅g, u⁆ * (g⁻¹ * u * g) := by group
  have hcinv : ⁅g, u⁆⁻¹ = ⁅g, u⁆ := inv_eq_of_mul_eq_one_right hsq
  have h3 := eq_inv_mul_of_mul_eq e2.symm
  rw [hcinv] at h3
  exact h3

end PairCtx

end CFSG.Quasithin.NoE9Z4MinGrp
