module

public import Mathlib.GroupTheory.Solvable

public section

namespace CFSG.Quasithin.H13.F431.Un

open scoped commutatorElement

universe u

section Lie

variable {Mb : Type u} [Group Mb]

structure UnLoc442Lie (T : Subgroup Mb) (z t : Mb) (Vb Ub Rb Kb : Subgroup Mb) : Prop where
  V_le : Vb ≤ Subgroup.centralizer ({t} : Set Mb)
  V_norm : ∀ x ∈ Subgroup.centralizer ({t} : Set Mb), ∀ v ∈ Vb, x * v * x⁻¹ ∈ Vb
  V_ab : ∀ a ∈ Vb, ∀ b ∈ Vb, a * b = b * a
  V_sq : ∀ a ∈ Vb, a ^ 2 = 1
  z_V : z ∈ Vb
  U_le : Ub ≤ Vb
  U_norm : ∀ x ∈ Subgroup.centralizer ({t} : Set Mb), ∀ u ∈ Ub, x * u * x⁻¹ ∈ Ub
  t_U : t ∈ Ub
  K_le : Kb ≤ Subgroup.centralizer ({t} : Set Mb)
  K_perf : ⁅Kb, Kb⁆ = Kb
  V_K : Vb ≤ Kb
  K_cent : ∀ k ∈ Kb, ∀ u ∈ Ub, k * u = u * k
  coset : ∀ v ∈ Vb, v ∉ Ub →
    ∃ x ∈ Subgroup.centralizer ({t} : Set Mb), ∃ u ∈ Ub, v = x * z * x⁻¹ * u
  nonsolv : ∃ L : Subgroup Mb, L ≤ Subgroup.centralizer ({t} : Set Mb) ∧
    ¬ Group.IsSolvable ↥L ∧ ∀ L' : Subgroup Mb, L' ≤ L →
      (∀ x ∈ L', ∀ v ∈ Vb, x * v * x⁻¹ * v⁻¹ ∈ Ub) → Group.IsSolvable ↥L'
  R_le : Rb ≤ Vb
  R_two : ∃ a ∈ Rb, ∃ b ∈ Rb, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b
  R_cls : ∀ r ∈ Rb, r ≠ 1 → ∃ x ∈ Subgroup.centralizer ({t} : Set Mb), r = x * z * x⁻¹
  R_U : ∀ r ∈ Rb, r ∈ Ub → r = 1
  z_cent : ∀ y ∈ T, y * z = z * y
  P_U : ∀ y ∈ T ⊓ Subgroup.centralizer ({t} : Set Mb), ∀ u ∈ Ub, y * u = u * y

end Lie

end CFSG.Quasithin.H13.F431.Un
