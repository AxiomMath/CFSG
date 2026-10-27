module

public import CFSG.Quasithin.EmptyFaithful.S153MTwoDef

public section

namespace CFSG.Quasithin.S146zU

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

structure PairPkg {V : Type} [CommGroup V] [Finite V] (Γ L₁ L₂ : Subgroup (MulAut V))
    (τ : MulAut V) : Prop where
  twoNat : S153M.TwoNat L₁ L₂ τ
  comm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a
  card₁ : Nat.card ↥L₁ = 4080
  card₂ : Nat.card ↥L₂ = 4080
  ffJ_eq : ffJ Γ = L₁ ⊔ L₂
  norm : ∀ x ∈ Γ, ∀ l ∈ L₁ ⊔ L₂, x * l * x⁻¹ ∈ L₁ ⊔ L₂
  cen : ∀ x ∈ Γ, (∀ l ∈ L₁ ⊔ L₂, x * l = l * x) → x = 1

end CFSG.Quasithin.S146zU
