module

public import CFSG.Quasithin.EmptyFaithful.S153EDefs2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise MatrixGroups

namespace S153P

section Defs

variable {G : Type} [Group G]

structure Abs56 (U Z Mc : Subgroup G) (z y : G) : Prop where
  Z_eq : Z = Subgroup.zpowers z
  z_ne : z ≠ 1
  z_sq : z * z = 1
  Mc_eq : Mc = Subgroup.centralizer (Z : Set G)
  U_norm : ∀ h ∈ Mc, ∀ u ∈ U, h * u * h⁻¹ ∈ U
  z_mem : z ∈ U
  U_comm : ∀ u ∈ U, ∀ v ∈ U, ⁅u, v⁆ ∈ Z
  U_sq : ∀ u ∈ U, u * u ∈ Z
  U_center : ∀ u ∈ U, (∀ v ∈ U, ⁅u, v⁆ = 1) → u ∈ Z
  Z_central : ∀ u ∈ U, u * z = z * u
  zp_mem : y⁻¹ * z * y ∈ U
  zp_ne : y⁻¹ * z * y ≠ z
  yz : y * z * y⁻¹ = z * (y⁻¹ * z * y)

abbrev zp (z y : G) : G := y⁻¹ * z * y
abbrev Jg (U : Subgroup G) (y : G) : Subgroup G := U ⊔ conjSubgroup U y
abbrev V0g (Z : Subgroup G) (y : G) : Subgroup G := Z ⊔ conjSubgroup Z y
abbrev Fg (U Mc : Subgroup G) (y : G) : Subgroup G := U ⊓ conjSubgroup Mc y
abbrev Xg (U Mc : Subgroup G) (y : G) : Subgroup G := conjSubgroup (Fg U Mc y) y
abbrev Eg (U Mc : Subgroup G) (y : G) : Subgroup G := Fg U Mc y ⊓ Xg U Mc y
abbrev Ng (U Mc : Subgroup G) (y : G) : Subgroup G := Fg U Mc y ⊔ Xg U Mc y

@[expose] def Abs56Concl [Finite G] (U Z Mc : Subgroup G) (y : G) : Prop :=
  Nat.card ↥(V0g Z y) = 4 ∧
  (∃ r : ℕ, IsSumOfNatSL2ModulesN153 r (Jg U y) (pCoreOf 2 (Jg U y)) (pCoreOf 2 (Jg U y)) (Eg U Mc y)) ∧
  pCoreOf 2 (Jg U y) = Fg U Mc y ⊔ Xg U Mc y ∧
  pCoreOf 2 (Jg U y) = Jg U y ⊓ Subgroup.centralizer ((V0g Z y : Subgroup G) : Set G) ∧
  ⁅Eg U Mc y, Jg U y⁆ ≤ V0g Z y ∧
  Subgroup.normalizer ((V0g Z y : Subgroup G) : Set G) ≤ Subgroup.normalizer ((Eg U Mc y : Subgroup G) : Set G)

@[expose] def Abs56Main : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (U Z Mc : Subgroup G) (z y : G), Abs56 U Z Mc z y → Abs56Concl U Z Mc y

structure Pts (z zp u₀ u₀' : G) : Prop where
  z_sq : z * z = 1
  zp_sq : zp * zp = 1
  comm : z * zp = zp * z
  z_ne_one : z ≠ 1
  zp_ne_one : zp ≠ 1
  z_ne_zp : z ≠ zp
  u₀_z : u₀ * z * u₀⁻¹ = z
  u₀_zp : u₀ * zp * u₀⁻¹ = z * zp
  u₀'_z : u₀' * z * u₀'⁻¹ = z * zp
  u₀'_zp : u₀' * zp * u₀'⁻¹ = zp

abbrev V0of (z zp : G) : Subgroup G := Subgroup.zpowers z ⊔ Subgroup.zpowers zp

end Defs

end S153P

end CFSG.Quasithin
