module

public import CFSG.Quasithin.Background.F7
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112SliceTypes
public import CFSG.Quasithin.Recognition.F112Crit.APrime.Offenders

public section

namespace CFSG.Quasithin.F112Crit.APrime

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Quasithin.CosetGeom (stab ballStab nbrs vtype Vv critDist dist)

variable {G : Type} [Group G]

structure AmalgamS3 (G₀ G₁ G₂ T L : Subgroup G) : Prop where
  hyp : AmalgamHyp G₀ G₁ G₂ T
  charTwo₂ : CharTwo G₂
  le : L ≤ G₂
  le_normalizer : G₂ ≤ Subgroup.normalizer (L : Set G)
  vS3 : VS3 L
  pCoreOf_eq : pCoreOf 2 L = pCoreOf 2 G₂
  inf_eq : L ⊓ G₁ = T
  sup_eq : L ⊔ (G₁ ⊓ G₂) = G₂

structure AmalgamA (G₀ G₁ G₂ T L : Subgroup G) : Prop extends AmalgamS3 G₀ G₁ G₂ T L where
  center : centerOf G₁ = ⊥
  gen : ∀ g ∈ G₁, g ∉ G₂ → T ⊔ conjSub g T = G₁

structure ConfigA (G₀ G₁ G₂ T L E : Subgroup G) : Prop extends AmalgamA G₀ G₁ G₂ T L where
  hypV : AmalgamHypV G₀ G₁ G₂ T E
  ne_bot : E ≠ ⊥
  star : StarBound E (pCoreOf 2 G₁) G₁
  odd : Odd (critDist G₀ G₁ G₂ E)

structure S3Point (G₀ G₁ G₂ : Subgroup G) (δ : CosetGeom G₀ G₁ G₂) : Prop where
  charTwo : CharTwo (stab δ)
  ncard_nbrs : (nbrs δ).ncard = 3
  le_pCoreOf_of_le_ballStab : ∀ P : Subgroup G, P ≤ ballStab 1 δ → IsPGroup 2 P →
    P ≤ pCoreOf 2 (stab δ)
  relIndex_le_two : ∀ ε ∈ nbrs δ, ∀ P : Subgroup G, P ≤ stab δ ⊓ stab ε → IsPGroup 2 P →
    (P ⊓ pCoreOf 2 (stab δ)).relIndex P ≤ 2
  exists_two_elt : ∀ ε ∈ nbrs δ,
    ∃ t ∈ stab δ ⊓ stab ε, (∃ k : ℕ, t ^ 2 ^ k = 1) ∧ t ∉ pCoreOf 2 (stab δ)
  smul_ne : ∀ f : ↥G₀, (f : G) ∈ stab δ → (∃ k : ℕ, (f : G) ^ 2 ^ k = 1) →
    (f : G) ∉ pCoreOf 2 (stab δ) → ∀ ε ∈ nbrs δ, f • ε = ε → ∀ ε' ∈ nbrs δ, ε' ≠ ε → f • ε' ≠ ε'
  exists_swap : ∀ ε₁ ∈ nbrs δ, ∀ ε₂ ∈ nbrs δ, ε₁ ≠ ε₂ →
    ∃ g : ↥G₀, (g : G) ∈ stab δ ∧ g • ε₁ = ε₂ ∧ g • ε₂ = ε₁
  exists_swap_fix : ∀ ε ∈ nbrs δ, ∀ ε₁ ∈ nbrs δ, ∀ ε₂ ∈ nbrs δ, ε₁ ≠ ε → ε₂ ≠ ε → ε₁ ≠ ε₂ →
    ∃ g : ↥G₀, (g : G) ∈ stab δ ∧ g • ε = ε ∧ g • ε₁ = ε₂ ∧ g • ε₂ = ε₁
  transitive_of_normal : ∀ N : Subgroup G, N ≤ stab δ → stab δ ≤ Subgroup.normalizer (N : Set G) →
    (∃ f ∈ N, (∃ k : ℕ, f ^ 2 ^ k = 1) ∧ f ∉ pCoreOf 2 (stab δ)) →
    ∀ ε ∈ nbrs δ, ∀ ε' ∈ nbrs δ, ∃ g : ↥G₀, (g : G) ∈ N ∧ g • ε = ε'

structure LocalS3 (G₀ G₁ G₂ : Subgroup G) : Prop where
  sup_stab : ∀ γ ε : CosetGeom G₀ G₁ G₂, ε ∈ nbrs γ → stab γ ⊔ stab ε = G₀
  point : ∀ δ : CosetGeom G₀ G₁ G₂, vtype δ = true → S3Point G₀ G₁ G₂ δ

structure LocalA (G₀ G₁ G₂ E : Subgroup G) : Prop extends LocalS3 G₀ G₁ G₂ where
  star : ∀ γ : CosetGeom G₀ G₁ G₂, vtype γ = false →
    StarBound (Vv E γ) (pCoreOf 2 (stab γ)) (stab γ)
  elemAbelian : ∀ γ : CosetGeom G₀ G₁ G₂, vtype γ = false → IsElemAbelian 2 (Vv E γ)
  ne_bot : ∀ γ : CosetGeom G₀ G₁ G₂, vtype γ = false → Vv E γ ≠ ⊥
  le_pCoreOf : ∀ γ : CosetGeom G₀ G₁ G₂, vtype γ = false → Vv E γ ≤ pCoreOf 2 (stab γ)
  pCoreOf_le_centralizer : ∀ γ : CosetGeom G₀ G₁ G₂, vtype γ = false →
    pCoreOf 2 (stab γ) ≤ Subgroup.centralizer (Vv E γ : Set G)
  le_stab : ∀ γ : CosetGeom G₀ G₁ G₂, vtype γ = false → ∀ ε : CosetGeom G₀ G₁ G₂,
    dist γ ε ≤ critDist G₀ G₁ G₂ E → Vv E γ ≤ stab ε
  le_pCoreOf_of_dist_lt : ∀ γ : CosetGeom G₀ G₁ G₂, vtype γ = false →
    ∀ ε : CosetGeom G₀ G₁ G₂, dist γ ε < critDist G₀ G₁ G₂ E → Vv E γ ≤ pCoreOf 2 (stab ε)
  elemAbelian_δ : 2 < critDist G₀ G₁ G₂ E → ∀ δ : CosetGeom G₀ G₁ G₂, vtype δ = true →
    IsElemAbelian 2 (Vv E δ)
  relIndex_inf : ∀ γ δ : CosetGeom G₀ G₁ G₂, vtype γ = false → δ ∈ nbrs γ →
    (pCoreOf 2 (stab γ) ⊓ pCoreOf 2 (stab δ)).relIndex (pCoreOf 2 (stab γ)) = 2
  not_le_normalizer : ∀ γ δ : CosetGeom G₀ G₁ G₂, vtype γ = false → δ ∈ nbrs γ →
    ¬ stab δ ≤ Subgroup.normalizer ((pCoreOf 2 (stab γ) ⊓ pCoreOf 2 (stab δ) : Subgroup G) : Set G)

end CFSG.Quasithin.F112Crit.APrime

end
