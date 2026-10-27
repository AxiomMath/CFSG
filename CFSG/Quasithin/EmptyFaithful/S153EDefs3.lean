module

public import CFSG.Quasithin.EmptyFaithful.S153EDefs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise

@[expose] def IsSylowThreeOf153 {G : Type*} [Group G] (P K : Subgroup G) : Prop :=
  P ≤ K ∧ IsPGroup 3 P ∧ ¬ 3 ∣ P.relIndex K

section Concl59

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

structure Concl15359 (_cx : Ctx15350 T Mc M V₁ V₂ t) : Prop where
  one : UH153 T M V₁ Mc = pCoreOf 2 Mc
  two : IsSylowTwoOf (T ⊓ oTwoUpper Mc) (Y153 Mc M ⊔ UH153 T M V₁ Mc)
  three : (T ⊓ oTwoUpper Mc).relIndex T = 2
  four : M = Y153 Mc M ⊔ T

end Concl59

section N8

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

structure N8Data153 (_cx : Ctx15350 T Mc M V₁ V₂ t) (DM JM : Subgroup G) (v z : G) : Prop where
  DM_syl : IsSylowThreeOf153 DM (M ⊓ Subgroup.centralizer (V₁ : Set G))
  card_DM : Nat.card DM = 3
  v_gen : Subgroup.zpowers v = ZS153 T M V₁ ⊓ V₁
  v_ne : v ≠ 1
  z_gen : Subgroup.zpowers z = quasithinOmegaOneCenter T
  DM_syl_v : IsSylowThreeOf153 DM (Subgroup.centralizer ({v} : Set G))
  cent_eq : M ⊓ Subgroup.centralizer (DM : Set G) = DM ⊔ JM
  inf_eq : DM ⊓ JM = ⊥
  comm : ∀ a ∈ DM, ∀ b ∈ JM, a * b = b * a
  JM_iso : Nonempty (↥JM ≃* Equiv.Perm (Fin 4))
  JM_core : pCoreOf 2 JM = V₁
  transv : ∀ x ∈ JM, orderOf x = 2 → x ∉ V₁ → Nat.card ↥⁅VZ T M, Subgroup.zpowers x⁆ = 2
  TJ_syl : IsSylowTwoOf (T ⊓ JM) JM
  TJ_dih : Nonempty (↥(T ⊓ JM) ≃* DihedralGroup 4)
  TJ_center : centerOf (T ⊓ JM) = Subgroup.zpowers v

structure Concl15360 (_cx : Ctx15350 T Mc M V₁ V₂ t) (DM DH JM : Subgroup G) (z : G) : Prop where
  one : ¬ ∃ g : G, conjSubgroup DH g = DM
  two_UCT : ∀ t₂ ∈ T ⊓ JM, orderOf t₂ = 2 → t₂ ∉ V₁ → t₂ ∉ UCT153 T M V₁ Mc
  two_z : ∀ t₂ ∈ T ⊓ JM, orderOf t₂ = 2 → t₂ ∉ V₁ → ∀ g : G, g * z * g⁻¹ ≠ t₂

end N8

end CFSG.Quasithin
