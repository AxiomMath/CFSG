module

public import CFSG.Quasithin.EmptyFaithful.S151cDich

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

section Str

variable {V : Type} [CommGroup V]

structure E9Z4Str (X Tb P : Subgroup (MulAut V)) : Prop where
  sq : ∀ v : V, v ^ 2 = 1
  fix : fixV P = ⊥
  eq : X = P ⊔ Tb
  normalP : NormalIn X P
  rk_four : rk V = 4
  card_P : Nat.card P = 9
  comm_P : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a
  exp_P : ∀ a ∈ P, a ^ 3 = 1
  card_Tb : Nat.card Tb = 4
  cyclic_Tb : IsCyclic Tb
  inv : ∃ t ∈ Tb, orderOf t = 2 ∧ ∀ a ∈ P, t * a * t⁻¹ = a⁻¹
  planes : ∃ P₁ P₂ : Subgroup (MulAut V), P₁ ≤ P ∧ P₂ ≤ P ∧ Nat.card P₁ = 3 ∧ Nat.card P₂ = 3 ∧
    P₁ ⊔ P₂ = P ∧ Disjoint (commV P₁) (commV P₂) ∧ commV P₁ ⊔ commV P₂ = ⊤ ∧
    commV P₁ ≤ fixV P₂ ∧ commV P₂ ≤ fixV P₁ ∧ ∃ σ ∈ Tb, conjBy σ P₁ = P₂

end Str

end CFSG.Quasithin
