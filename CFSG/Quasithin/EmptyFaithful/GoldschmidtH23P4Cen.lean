module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4OutBase

public section

namespace CFSG.Quasithin.H23P4

open CFSG.QuasithinUnique

@[expose] def CenOvergroup (Γ : Type*) [Group Γ] : Prop :=
  ∀ S₀ U : Subgroup Γ, IsSylowTwoOf S₀ ⊤ → S₀ ≤ U → ∀ b : ℕ, 0 < b → S₀.relIndex U = 5 ^ b →
    ∀ z ∈ S₀, (∀ s ∈ S₀, s * z = z * s) → ∀ u ∈ U, u * z = z * u

structure RowTits (Γ : Type*) [Group Γ] : Prop where
  center : Subgroup.center Γ = ⊥
  out : CFSG.Quasithin.H23Out.Out5Pow Γ
  cen : CenOvergroup Γ

end CFSG.Quasithin.H23P4
