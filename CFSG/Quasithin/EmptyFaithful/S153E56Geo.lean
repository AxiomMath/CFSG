module

public import CFSG.Quasithin.EmptyFaithful.S153EDefs2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise

section Geo

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

structure Geo56 (cx : Ctx15350 T Mc M V₁ V₂ t) (s : ℕ) (y t₁ : G) : Prop where
  U_ext : CFSG.IsExtraspecial 2 ↥(UH153 T M V₁ Mc)
  Z_center : centerOf (UH153 T M V₁ Mc) = quasithinOmegaOneCenter T
  rank : mIdx (UH153 T M V₁ Mc) (quasithinOmegaOneCenter T) = 2 * (s + 2)
  Z'_le_U : conjSubgroup (quasithinOmegaOneCenter T) y ≤ UH153 T M V₁ Mc
  Z_le_U' : quasithinOmegaOneCenter T ≤ conjSubgroup (UH153 T M V₁ Mc) y
  Z_inf_Z' : quasithinOmegaOneCenter T ⊓ conjSubgroup (quasithinOmegaOneCenter T) y = ⊥
  E_eq : Egp153 T M V₁ Mc y = UH153 T M V₁ Mc ⊓ conjSubgroup (UH153 T M V₁ Mc) y
  E_sing : quasithinOmegaOneCenter T ≤ Egp153 T M V₁ Mc y ∧
    (∀ e ∈ Egp153 T M V₁ Mc y, e ^ 2 = 1) ∧
    mIdx (Egp153 T M V₁ Mc y) (quasithinOmegaOneCenter T) = s + 2
  V0_le_E : quasithinOmegaOneCenter T ⊔ conjSubgroup (quasithinOmegaOneCenter T) y ≤ Egp153 T M V₁ Mc y
  F_eq : Fgp153 T M V₁ Mc y = UH153 T M V₁ Mc ⊓
    Subgroup.centralizer ((conjSubgroup (quasithinOmegaOneCenter T) y : Subgroup G) : Set G)
  X_eq : Xgp153 T M V₁ Mc y = conjSubgroup (UH153 T M V₁ Mc) y ⊓
    Subgroup.centralizer ((quasithinOmegaOneCenter T : Subgroup G) : Set G)
  X_le_Mc : Xgp153 T M V₁ Mc y ≤ Mc
  X_inf_Q : Xgp153 T M V₁ Mc y ⊓ pCoreOf 2 Mc = Egp153 T M V₁ Mc y
  V_norm_E : VZ T M ≤ Subgroup.normalizer ((Egp153 T M V₁ Mc y : Subgroup G) : Set G)
  V_comm_E : ⁅Egp153 T M V₁ Mc y, VZ T M⁆ ≤
    quasithinOmegaOneCenter T ⊔ conjSubgroup (quasithinOmegaOneCenter T) y
  EN : Subgroup.normalizer
      ((quasithinOmegaOneCenter T ⊔ conjSubgroup (quasithinOmegaOneCenter T) y : Subgroup G) : Set G) ≤
    Subgroup.normalizer ((Egp153 T M V₁ Mc y : Subgroup G) : Set G)
  X_perp : ∀ x ∈ Xgp153 T M V₁ Mc y, ∀ v ∈ VZ T M ⊓ UH153 T M V₁ Mc,
    x * v * x⁻¹ * v⁻¹ ∈ quasithinOmegaOneCenter T
  EEt : Egp153 T M V₁ Mc y ⊓ conjSubgroup (Egp153 T M V₁ Mc y) t₁ ≤ quasithinOmegaOneCenter T

end Geo

end CFSG.Quasithin
