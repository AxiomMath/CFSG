module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Assembly.QuasithinDefs

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.QuasithinUnique

@[expose] def CharTwoMod {G : Type} [Group G] (H U : Subgroup G) [(U.subgroupOf H).Normal]
    (x : ↥H) : Prop :=
  CharTwo (Subgroup.centralizer
    ({(QuotientGroup.mk x : ↥H ⧸ U.subgroupOf H)} : Set (↥H ⧸ U.subgroupOf H)))

structure E7LeviData {G : Type} [Group G] (L : Subgroup G) (σ b : G) (P J D : Subgroup G) :
    Prop where
  σ_mem : σ ∈ P
  P_le : P ≤ L
  P_two : IsPGroup 2 P
  P_comm : ∀ x ∈ P, ∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.zpowers σ
  P_cent : ∀ x ∈ P, x * σ = σ * x
  centP : ∀ x ∈ L, (∀ y ∈ P, x * y = y * x) → x ∈ Subgroup.zpowers σ
  J_le : J ≤ L
  J_cent : ∀ x ∈ J, x * σ = σ * x
  D_le : D ≤ J
  D_norm : D ≤ Subgroup.normalizer (P : Set G)
  D_SL : Nonempty (↥D ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
  b_mem : b ∈ D
  b_ord : orderOf b = 3

@[expose] def modW {G : Type} [Group G] (U : Subgroup G) (t₀ σ : G) : Subgroup G :=
  ⁅U, Subgroup.zpowers σ⁆ ⊔ Subgroup.zpowers t₀

structure E7ModuleData {G : Type} [Group G] (U : Subgroup G) (t₀ σ : G) (L P : Subgroup G) :
    Prop where
  t₀_mem : t₀ ∈ U
  U_comm : ∀ u ∈ U, ∀ v ∈ U, u * v * u⁻¹ * v⁻¹ ∈ Subgroup.zpowers t₀
  P_W : ∀ x ∈ P, ∀ w ∈ modW U t₀ σ, x * w * x⁻¹ * w⁻¹ ∈ Subgroup.zpowers t₀
  L_W : ∀ x ∈ L, x * σ * x⁻¹ * σ⁻¹ ∈ U →
    (∀ w ∈ modW U t₀ σ, x * w * x⁻¹ * w⁻¹ ∈ Subgroup.zpowers t₀) → x ∈ P

structure BetaData {G : Type} [Group G] (Y L A : Subgroup G) (b₀ β σ : G) : Prop where
  β_ord : orderOf β = 3
  β_mem : β ∈ Y
  L_le : L ≤ Y
  L_cent : ∀ x ∈ L, x * β = β * x
  L_disj : ∀ x ∈ L, x ∈ Subgroup.zpowers β → x = 1
  Y_cent : ∀ y ∈ Y, y * β = β * y → y ∈ Subgroup.zpowers β ⊔ L
  A_le : A ≤ L
  A_elem : IsElemAbelian 3 A
  A_card : Nat.card A = 27
  b₀_cent : Subgroup.centralizer ({b₀} : Set G) ≤ Y
  A_conj : ∀ F : Subgroup G, F ≤ A → Nat.card F = 9 → ∃ y ∈ Y, y * b₀ * y⁻¹ ∈ F
  σ_mem : σ ∈ L
  σ_ord : orderOf σ = 2
  A_cent : ∀ a ∈ A, a * σ = σ * a
  centP : ∀ x ∈ L, (∀ y ∈ pCoreOf 2 (L ⊓ Subgroup.centralizer ({σ} : Set G)), x * y = y * x) →
    x ∈ Subgroup.zpowers σ
  P_le : pCoreOf 2 (L ⊓ Subgroup.centralizer ({σ} : Set G)) ≤
    pCoreOf 2 (Subgroup.centralizer ({σ} : Set G))
  Q_le : pCoreOf 2 (Subgroup.centralizer ({σ} : Set G)) ≤ Y

end CFSG.StandardType.FrameRoute.FS81

end
