module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.Quasithin.Background.TwoReduced

public section

namespace CFSG.Quasithin.H13.F431.Un

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open
open scoped commutatorElement

section Std

variable (C : Type) [Group C]

structure UnStdV (U P P' : Subgroup C) (z t : C) (V4 : Subgroup C) : Prop where
  V4_le : V4 ≤ U
  V4_ab : ∀ a ∈ V4, ∀ b ∈ V4, a * b = b * a
  V4_sq : ∀ a ∈ V4, a ^ 2 = 1
  V4_zt : z ∈ V4 ∧ t ∈ V4
  V4_eq : V4 = centerOf (pCoreOf 2 P')
  V4_unique : ∀ E : Subgroup C, E ≤ U → (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) →
    (∀ a ∈ E, a ^ 2 = 1) → Nat.card E = Nat.card V4 → E = V4
  z_ZP : z ∈ centerOf (perfectCore P)
  ZP_trans : ∀ x ∈ centerOf (perfectCore P), x ≠ 1 → ∃ m ∈ P, m * z * m⁻¹ = x
  cz : Subgroup.centralizer ({z} : Set C) ≤ P
  ct : Subgroup.centralizer ({t} : Set C) ≤ P'
  nz : ¬ Subgroup.centralizer ({z} : Set C) ≤ P'
  nt : ¬ Subgroup.centralizer ({t} : Set C) ≤ P

structure UnStdLoc (U : Subgroup C) (z t : C) (V Uc R K : Subgroup C) : Prop where
  comm : z * t = t * z
  sylow_t : IsSylowTwoOf (U ⊓ Subgroup.centralizer ({t} : Set C))
    (Subgroup.centralizer ({t} : Set C))
  V_le : V ≤ Subgroup.centralizer ({t} : Set C)
  V_aut : ∀ φ : MulAut C, φ t = t → ∀ v ∈ V, φ v ∈ V
  V_ab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a
  V_sq : ∀ a ∈ V, a ^ 2 = 1
  z_V : z ∈ V
  U_le : Uc ≤ V
  U_aut : ∀ φ : MulAut C, φ t = t → ∀ u ∈ Uc, φ u ∈ Uc
  t_U : t ∈ Uc
  K_le : K ≤ Subgroup.centralizer ({t} : Set C)
  K_perf : ⁅K, K⁆ = K
  V_K : V ≤ K
  K_cent : ∀ k ∈ K, ∀ u ∈ Uc, k * u = u * k
  coset : ∀ v ∈ V, v ∉ Uc →
    ∃ x ∈ Subgroup.centralizer ({t} : Set C), ∃ u ∈ Uc, v = x * z * x⁻¹ * u
  nonsolv : ∃ L : Subgroup C, L ≤ Subgroup.centralizer ({t} : Set C) ∧
    ¬ Group.IsSolvable ↥L ∧ ∀ L' : Subgroup C, L' ≤ L →
      (∀ x ∈ L', ∀ v ∈ V, x * v * x⁻¹ * v⁻¹ ∈ Uc) → Group.IsSolvable ↥L'
  R_le : R ≤ V
  R_two : ∃ a ∈ R, ∃ b ∈ R, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b
  R_cls : ∀ r ∈ R, r ≠ 1 → ∃ x ∈ Subgroup.centralizer ({t} : Set C), r = x * z * x⁻¹
  R_U : ∀ r ∈ R, r ∈ Uc → r = 1
  z_cent : ∀ y ∈ U, y * z = z * y
  P_U : ∀ y ∈ U ⊓ Subgroup.centralizer ({t} : Set C), ∀ u ∈ Uc, y * u = u * y

end Std

end CFSG.Quasithin.H13.F431.Un
