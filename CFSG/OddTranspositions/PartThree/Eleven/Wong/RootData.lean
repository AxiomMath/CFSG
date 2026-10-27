module

public import CFSG.OddTranspositions.PartThree.Eleven.Wong.CentData
public import CFSG.GroupTheory.PCore.Defs
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

public section

namespace CFSG.OddTranspositions.PartThree.Wong

open Subgroup

variable {G : Type} [Group G]

@[expose] def thetaHom : Multiplicative (ZMod 5) →* SL5 where
  toFun a := thetaM a.toAdd
  map_one' := by decide
  map_mul' := by decide

structure SplitData.Outer (D : SplitData G) (s : G) : Prop where
  card_X : Nat.card D.X = 480
  X_le_normalizer_A : D.X ≤ normalizer (D.A : Set G)
  A_inf_centralizer_v : D.A ⊓ centralizer {D.v} = D.J
  centralizer_t_inf_X : centralizer {D.t} ⊓ D.X = closure {D.t, D.u} ⊔ D.A
  eq_or_eq : s = D.a * D.w ∨ s = D.a * D.w * D.v
  sq : s ^ 2 = D.u
  conj_t : D.t⁻¹ * s * D.t = s⁻¹
  X_eq : D.X = D.A ⊔ closure {s, D.t}
  A_inf : D.A ⊓ closure {s, D.t} = ⊥
  dihedral : Nonempty (closure {s, D.t} ≃* DihedralGroup 4)
  psi : ∀ x x' : SL5, psiM * (x' : Matrix (Fin 2) (Fin 2) (ZMod 5)) =
    (x : Matrix (Fin 2) (Fin 2) (ZMod 5)) * psiM → s⁻¹ * D.d x * s = D.d x'
  y_mem_normalizer : s * D.w ∈ normalizer (D.D1 : Set G)
  y_conj_v : (s * D.w)⁻¹ * D.v * (s * D.w) = D.v
  y_conj_w : (s * D.w)⁻¹ * D.w * (s * D.w) = D.v * D.w
  y_sq : (s * D.w) ^ 2 = D.u * D.v
  y_conj_t : (s * D.w)⁻¹ * D.t * (s * D.w) = D.t * D.u
  y_conj_tu : (s * D.w)⁻¹ * (D.t * D.u) * (s * D.w) = D.t
  y_conj_theta : ∀ q : ZMod 5, (s * D.w)⁻¹ * D.d (thetaM q) * (s * D.w) = D.d (thetaM (3 * q))

structure RootData (G : Type) [Group G] extends SplitData G where
  s : G
  outer : toSplitData.Outer s

namespace RootData

variable (D : RootData G)

@[expose] def y : G := D.s * D.w

@[expose] def q1 : Multiplicative (ZMod 5) →* G := D.i1.comp thetaHom

@[expose] def q2 : Multiplicative (ZMod 5) →* G := D.i2.comp thetaHom

@[expose] def q12 : Multiplicative (ZMod 5) →* G where
  toFun a := D.q1 a * D.q2 a⁻¹
  map_one' := by simp
  map_mul' a b := by
    have hc : Commute (D.q2 a⁻¹) (D.q1 b) := (D.commute _ _).symm
    rw [mul_inv, map_mul, map_mul, mul_assoc, mul_assoc, ← mul_assoc (D.q2 a⁻¹), hc.eq,
      mul_assoc, ← map_mul D.q2 a⁻¹ b⁻¹, mul_comm a⁻¹ b⁻¹, map_mul]

@[expose] def q3 : Multiplicative (ZMod 5) →* G := (MulAut.conj D.y⁻¹).toMonoidHom.comp D.q12

@[expose] def q4 : Multiplicative (ZMod 5) →* G := (MulAut.conj D.c2⁻¹).toMonoidHom.comp D.q3

@[expose] def P1 : Subgroup G := D.q1.range

@[expose] def P2 : Subgroup G := D.q2.range

@[expose] def P3 : Subgroup G := D.q3.range

@[expose] def P4 : Subgroup G := D.q4.range

@[expose] def R : Subgroup G := D.P1 ⊔ D.P2

@[expose] def D2 : Subgroup G := D.q12.range

@[expose] def H : Subgroup G := closure {D.h1, D.h2}

@[expose] def Q : Subgroup G :=
  (CFSG.oddCore (centralizer (D.D1 : Set G))).map (centralizer (D.D1 : Set G)).subtype

@[expose] def V : Subgroup G :=
  (CFSG.oddCore (centralizer (D.P1 : Set G))).map (centralizer (D.P1 : Set G)).subtype

@[expose] def U : Subgroup G := D.P2 ⊔ D.V

@[expose] def twist : SL5 →* G := (MulAut.conj (D.h2⁻¹ * D.y * D.c2)⁻¹).toMonoidHom.comp D.d

end RootData

end CFSG.OddTranspositions.PartThree.Wong
