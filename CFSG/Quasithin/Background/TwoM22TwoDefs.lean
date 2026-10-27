module

public import CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.Quasithin.TwoM22

open Subgroup CFSG.Blueprint

structure IsTwoM22TwoModel {W : Type*} [Group W] (M : Subgroup W) (T : W) : Prop where
  perfect : Group.IsPerfect ↥M
  exists_quot : ∃ q : ↥M →* ↥NativeSporadic.M22, Function.Surjective q ∧ q.ker = center ↥M
  card_center : Nat.card (center ↥M) = 2
  mul_self_T : T * T = 1
  T_not_mem : T ∉ M
  conj_T_mem : ∀ m ∈ M, T * m * T⁻¹ ∈ M
  mem_of_commute : ∀ g : W, (∀ m ∈ M, g * m = m * g) → g ∈ M
  mul_self_eq_one : ∀ m ∈ M, (∀ x ∈ M, m * T * (m * T) * x = x * (m * T * (m * T))) →
    m * T * (m * T) = 1

end CFSG.Quasithin.TwoM22
