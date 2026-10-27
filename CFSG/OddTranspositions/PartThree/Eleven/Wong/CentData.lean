module

public import CFSG.OddTranspositions.PartThree.Eleven.Wong.Hyp
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.OddTranspositions.PartThree.Wong

open Subgroup

abbrev SL5 : Type := Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)

@[expose] def hM : SL5 := ⟨!![2, 0; 0, 3], by decide⟩

@[expose] def cM : SL5 := ⟨!![0, -1; 1, 0], by decide⟩

@[expose] def thetaM (q : ZMod 5) : SL5 := ⟨!![1, 0; q, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def psiM : Matrix (Fin 2) (Fin 2) (ZMod 5) := !![0, 2; 1, 0]

structure SwapData (G : Type) [Group G] where
  i1 : SL5 →* G
  i2 : SL5 →* G
  t : G
  u : G
  hyp : WongHyp t i1.range i2.range
  inj1 : Function.Injective i1
  inj2 : Function.Injective i2
  orderOf_u : orderOf u = 2
  swap : ∀ x : SL5, u⁻¹ * i1 x * u = i2 x
  u_not_mem : u ∉ i1.range ⊔ i2.range

structure SplitData (G : Type) [Group G] extends SwapData G where
  z : G
  not_isConj_t_u : ¬ IsConj t u
  isConj_t_tu : IsConj t (t * u)
  isConj_u_v : IsConj u (i1 hM * i2 hM)
  isConj_t_or_u : ∀ x : G, orderOf x = 2 → IsConj t x ∨ IsConj u x
  isSylow : ∃ P : Sylow 2 G, (P : Subgroup G) = closure {i1 hM, i1 cM, i2 hM, i2 cM, u}
  z_t : z⁻¹ * t * z = u * (i1 hM * i2 hM)
  z_u : z⁻¹ * u * z = t * (i1 hM * i2 hM)
  z_v : z⁻¹ * (i1 hM * i2 hM) * z = i1 hM * i2 hM
  z_sq : z ^ 2 ∈ closure {i1 hM, i1 cM, i2 hM, i2 cM, u}

namespace SwapData

variable {G : Type} [Group G] (D : SwapData G)

theorem orderOf_t : orderOf D.t = 2 := D.hyp.orderOf_t

theorem commute (x y : SL5) : Commute (D.i1 x) (D.i2 y) :=
  D.hyp.commute _ ⟨x, rfl⟩ _ ⟨y, rfl⟩

theorem range_inf : D.i1.range ⊓ D.i2.range = zpowers D.t := D.hyp.inf_eq

@[expose] def h1 : G := D.i1 hM
@[expose] def h2 : G := D.i2 hM
@[expose] def c1 : G := D.i1 cM
@[expose] def c2 : G := D.i2 cM
@[expose] def v : G := D.h1 * D.h2
@[expose] def w : G := D.c1 * D.c2
@[expose] def r : G := D.t * D.u
@[expose] def K : Subgroup G := D.i1.range ⊔ D.i2.range
@[expose] def S : Subgroup G := closure {D.h1, D.c1, D.h2, D.c2, D.u}
@[expose] def E : Subgroup G := closure {D.t, D.u, D.v, D.w}

@[expose] def d : SL5 →* G where
  toFun x := D.i1 x * D.i2 x
  map_one' := by simp
  map_mul' x y := by
    rw [map_mul, map_mul, mul_assoc, mul_assoc, ← mul_assoc (D.i2 x), (D.commute y x).symm.eq,
      mul_assoc]

@[expose] def A : Subgroup G := D.d.range
@[expose] def X : Subgroup G := centralizer {D.u}
@[expose] def T : Subgroup G := centralizer {D.u} ⊓ centralizer {D.v}
@[expose] def J : Subgroup G := closure {D.v, D.w}
@[expose] def W : Subgroup G := closure {D.u, D.v, D.w}
@[expose] def D1 : Subgroup G := closure (Set.range fun q : ZMod 5 => D.d (thetaM q))

end SwapData

namespace SplitData

variable {G : Type} [Group G] (D : SplitData G)

@[expose] def a : G := D.z⁻¹ * D.h1 * D.z
@[expose] def b : G := D.z⁻¹ * D.h2 * D.z
@[expose] def M : Subgroup G := closure {D.a, D.b, D.w}

end SplitData

end CFSG.OddTranspositions.PartThree.Wong
