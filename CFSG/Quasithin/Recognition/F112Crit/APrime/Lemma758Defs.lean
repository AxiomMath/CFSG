module

public import CFSG.Quasithin.Background.Ordering
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.Quasithin.F112Crit.APrime

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G]

structure ParabolicA (G₁ G₂ M : Subgroup G) : Prop where
  le : M ≤ G₂
  le_normalizer : G₂ ≤ Subgroup.normalizer (M : Set G)
  le_conjClosure : M ≤ conjClosure (pCoreOf 2 G₁) G₂
  isSylowTwoOf : IsSylowTwoOf (pCoreOf 2 G₁) M
  relIndex : (pCoreOf 2 G₁).relIndex M = 3
  not_le_normalizer : ¬ M ≤ Subgroup.normalizer (pCoreOf 2 G₁ : Set G)
  pCoreOf_eq : pCoreOf 2 M = pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂
  charTwo : CharTwo M
  card : ∃ a : ℕ, Nat.card M = 2 ^ a * 3
  sup_eq : M ⊔ (G₁ ⊓ G₂) = G₂
  inf_eq : M ⊓ G₁ = pCoreOf 2 G₁
  commutator_mem : ∀ x ∈ M, ∀ q ∈ pCoreOf 2 G₂,
    x * q * x⁻¹ * q⁻¹ ∈ pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂

end CFSG.Quasithin.F112Crit.APrime

end
