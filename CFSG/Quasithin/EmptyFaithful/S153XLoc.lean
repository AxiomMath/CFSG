module

public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.ModFA5Cfg

public section

namespace CFSG.Quasithin.X1469

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.ModF
open scoped commutatorElement

variable {G : Type} [Group G]

abbrev rz (Iz : Subgroup G) : Subgroup G := pCoreOf 2 Iz

abbrev z0 (Iz : Subgroup G) : Subgroup G := omegaOneCenterOf (pCoreOf 2 Iz)

abbrev Esub (K Iz : Subgroup G) : Subgroup G := ⁅blockU K, K ⊓ Iz⁆

abbrev Zsub (S K : Subgroup G) : Subgroup G :=
  blockU K ⊓ Subgroup.centralizer ((S ⊓ K : Subgroup G) : Set G)

abbrev E0 (K₁ K₂ Iz : Subgroup G) : Subgroup G := Esub K₁ Iz ⊔ Esub K₂ Iz

abbrev Kp (c₁ c₂ : G) : Subgroup G := Subgroup.zpowers c₁ ⊔ Subgroup.zpowers c₂

abbrev Pp (K₁ K₂ Iz : Subgroup G) (c₁ c₂ : G) : Subgroup G := ⁅rz Iz, Kp c₁ c₂⁆ ⊔ E0 K₁ K₂ Iz

structure LocalCfg [Finite G] (I S Iz K₁ K₂ T : Subgroup G) (r z : G) : Prop where
  cfg : A5Cfg I S Iz K₁ K₂
  charTwo : CharTwo I
  hD : S ⊓ Subgroup.centralizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) = ⊥
  hnot : ¬ K₁ ≤ Iz
  ht : ∃ t ∈ S, B6.conjSub t K₁ = K₂
  hST : S ≤ T
  hTN : T ≤ Subgroup.normalizer (S : Set G)
  hrel : S.relIndex T = 2
  hrT : r ∈ T
  hrS : r ∉ S
  hb : ∀ R₀ : Subgroup G, R₀ ≤ S → R₀ ≠ ⊥ → ¬ (T ⊔ I ≤ Subgroup.normalizer (R₀ : Set G))
  hzS : z ∈ S
  hz1 : z ≠ 1
  hz2 : z ^ 2 = 1
  hzc : ∀ y ∈ T, y * z = z * y
  hIz : Iz = I ⊓ Subgroup.centralizer ({z} : Set G)

structure BlockFacts (S Iz K : Subgroup G) (c₁ : G) : Prop where
  mem : c₁ ∈ K ⊓ Iz
  odd : Odd (orderOf c₁)
  Y_le_N_B : K ⊓ Iz ≤ Subgroup.normalizer ((S ⊓ K : Subgroup G) : Set G)
  card_E : Nat.card ↥(Esub K Iz) = 8
  card_Z : Nat.card ↥(Zsub S K) = 2
  Z_le_E : Zsub S K ≤ Esub K Iz
  faith_E : ∀ b ∈ S ⊓ K, (∀ e ∈ Esub K Iz, b * e * b⁻¹ = e) → b ∈ blockU K
  irred_E : ∀ N : Subgroup G, N ≤ Esub K Iz → K ⊓ Iz ≤ Subgroup.normalizer (N : Set G) →
    N ≤ Zsub S K ∨ N = Esub K Iz
  fix_E : ∀ e ∈ Esub K Iz, (∀ y ∈ K ⊓ Iz, e * y * e⁻¹ * y⁻¹ ∈ Zsub S K) → e ∈ Zsub S K
  irred_B : ∀ N : Subgroup G, N ≤ S ⊓ K → K ⊓ Iz ≤ Subgroup.normalizer (N : Set G) →
    N ≤ blockU K ∨ S ⊓ K ≤ N ⊔ blockU K
  fix_B : ∀ b ∈ S ⊓ K, (∀ y ∈ K ⊓ Iz, b * y * b⁻¹ * y⁻¹ ∈ blockU K) → b ∈ blockU K
  gen_B : ∀ b ∈ S ⊓ K, ∃ b' ∈ S ⊓ K, ∃ u ∈ blockU K,
    b = (b' * c₁ * b'⁻¹ * c₁⁻¹) * u
  cent_B : ∀ u ∈ blockU K, (∀ b ∈ S ⊓ K,
    u * (b * c₁ * b⁻¹ * c₁⁻¹) = (b * c₁ * b⁻¹ * c₁⁻¹) * u) → u ∈ Zsub S K
  centmod_B : ∀ u ∈ blockU K, (∀ b ∈ S ⊓ K,
    u * (b * c₁ * b⁻¹ * c₁⁻¹) * u⁻¹ * (b * c₁ * b⁻¹ * c₁⁻¹)⁻¹ ∈ Zsub S K) → u ∈ Esub K Iz

structure PairGen (I S Iz K₁ K₂ : Subgroup G) (t z : G) : Prop where
  t_mem : t ∈ S
  t_conj : B6.conjSub t K₁ = K₂
  comm : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a
  hnot₂ : ¬ K₂ ≤ Iz
  S_le_Iz : S ≤ Iz
  R_le_S : rz Iz ≤ S
  Iz_N_R : Iz ≤ Subgroup.normalizer ((rz Iz : Subgroup G) : Set G)
  Iz_N_Q : Iz ≤ Subgroup.normalizer ((pCoreOf 2 I : Subgroup G) : Set G)
  K₁_N_U : K₁ ≤ Subgroup.normalizer ((blockU K₁ : Subgroup G) : Set G)
  K₂_N_U : K₂ ≤ Subgroup.normalizer ((blockU K₂ : Subgroup G) : Set G)
  U₁_elem : IsElemAbelian 2 (blockU K₁)
  U₂_elem : IsElemAbelian 2 (blockU K₂)
  U_inf : blockU K₁ ⊓ blockU K₂ = ⊥
  U₁_le_B : blockU K₁ ≤ S ⊓ K₁
  U₂_le_B : blockU K₂ ≤ S ⊓ K₂
  B₁_le_R : S ⊓ K₁ ≤ rz Iz
  B₂_le_R : S ⊓ K₂ ≤ rz Iz
  Q_le_R : pCoreOf 2 I ≤ rz Iz
  U₁_le_Q : blockU K₁ ≤ pCoreOf 2 I
  U₂_le_Q : blockU K₂ ≤ pCoreOf 2 I
  Q_decomp : ∀ g ∈ pCoreOf 2 I, ∃ u₁ ∈ blockU K₁, ∃ u₂ ∈ blockU K₂, g = u₁ * u₂
  R_decomp : ∀ g ∈ rz Iz, ∃ s₁ ∈ S ⊓ K₁, ∃ s₂ ∈ S ⊓ K₂, g = s₁ * s₂
  swap_U : ∀ u ∈ blockU K₁, t * u * t⁻¹ ∈ blockU K₂
  swap_U' : ∀ u ∈ blockU K₂, t⁻¹ * u * t ∈ blockU K₁
  swap_B : ∀ b ∈ S ⊓ K₁, t * b * t⁻¹ ∈ S ⊓ K₂
  swap_B' : ∀ b ∈ S ⊓ K₂, t⁻¹ * b * t ∈ S ⊓ K₁
  swap_E : ∀ e ∈ Esub K₁ Iz, t * e * t⁻¹ ∈ Esub K₂ Iz
  swap_E' : ∀ e ∈ Esub K₂ Iz, t⁻¹ * e * t ∈ Esub K₁ Iz
  Iz_normalizes_E : Iz ≤ Subgroup.normalizer ((E0 K₁ K₂ Iz : Subgroup G) : Set G)
  Z₁_le_z0 : Zsub S K₁ ≤ z0 Iz
  Z₂_le_z0 : Zsub S K₂ ≤ z0 Iz
  z_mem_Q : z ∈ pCoreOf 2 I

structure LocalFacts (I S Iz : Subgroup G) (r z : G) : Prop where
  card_z0 : Nat.card (z0 Iz) = 4
  z_mem : z ∈ z0 Iz
  irred_Rz : ∀ N : Subgroup G, N ≤ rz Iz → Iz ≤ Subgroup.normalizer (N : Set G) →
    N ≤ pCoreOf 2 I ∨ N ⊔ pCoreOf 2 I = rz Iz
  exists_sub : ∃ K' P E₀ : Subgroup G,
    K' ≤ Iz ∧ P ≤ rz Iz ∧ E₀ ≤ P ∧ Iz ≤ Subgroup.normalizer (E₀ : Set G) ∧
    ⁅pCoreOf 2 I, K'⁆ ≤ E₀ ∧ P ≤ ⁅rz Iz, K'⁆ ⊔ E₀ ∧
    rz Iz ≤ P ⊔ pCoreOf 2 I ∧
    (∀ g ∈ rz Iz, (∀ p ∈ P, g * p * g⁻¹ * p⁻¹ = 1) → g ∈ z0 Iz) ∧
    (∀ u ∈ pCoreOf 2 I, (∀ p ∈ P, u * p * u⁻¹ * p⁻¹ ∈ z0 Iz) → u ∈ P) ∧
    (∀ p ∈ P, (∀ p' ∈ P, p * p' * p⁻¹ * p'⁻¹ ∈ Subgroup.zpowers z) → p ∈ z0 Iz) ∧
    (∀ N : Subgroup G, N ≤ E₀ → Iz ≤ Subgroup.normalizer (N : Set G) →
      N ≤ z0 Iz ∨ E₀ ≤ N ⊔ z0 Iz) ∧
    (∃ x₀ ∈ E₀, x₀ ∉ z0 Iz ∧ ∀ y ∈ S, x₀ * y * x₀⁻¹ * y⁻¹ ∈ z0 Iz) ∧
    (∃ e ∈ E₀, r * e * r⁻¹ ∉ pCoreOf 2 I)

end CFSG.Quasithin.X1469
