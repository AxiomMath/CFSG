module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.Context

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

variable {G : Type} [Group G] [Finite G]

structure Case811L227 (c : Counterexample4 G) where
  P : Subgroup G
  sylow : CFSG.ABGLocalTools.IsSylowOf 3 P c.S.M
  card_P : Nat.card P = 81
  elemAbelian_S : CFSG.Open.IsElemAbelian 3 (P ⊓ c.L)
  card_S : Nat.card (P ⊓ c.L : Subgroup G) = 27
  unique : ∀ E : Subgroup G, E ≤ P → CFSG.Open.IsElemAbelian 3 E → Nat.card E = 27 →
    E = P ⊓ c.L
  z : G
  center_eq : P ⊓ Subgroup.centralizer (P : Set G) = Subgroup.zpowers z
  orderOf_z : orderOf z = 3
  y : G
  y_mem : y ∈ P
  y_not_mem_L : y ∉ c.L
  orderOf_y : orderOf y = 3
  inf_centralizer_eq : ∀ x ∈ P, x ∉ c.L → orderOf x = 3 →
    P ⊓ c.L ⊓ Subgroup.centralizer ({x} : Set G) = Subgroup.zpowers z
  card_inf_centralizer : ∀ x ∈ P, x ∉ c.L → orderOf x = 3 →
    Nat.card (P ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) = 9
  exists_conj_eq_mul : ∀ x ∈ P, x ∉ c.L → orderOf x = 3 →
    ∃ s ∈ P ⊓ c.L, s * x * s⁻¹ = x * z ∨ s * x * s⁻¹ = x * z⁻¹
  exists_conj : ∀ x ∈ P, x ∉ c.L → orderOf x = 3 → ∀ w : G, x⁻¹ * w ∈ P ⊓ c.L →
    orderOf w = 3 → ∃ s ∈ P ⊓ c.L, w = s * x * s⁻¹
  normalizer_le : ∀ Y : Subgroup G, Y ≤ P ⊓ c.L → Y ≠ ⊥ →
    Subgroup.normalizer (Y : Set G) ≤ c.S.M
  not_conj_inv : ∀ m ∈ c.S.M, y * (m * y * m⁻¹) ∉ P ⊓ c.L

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
