module

public import CFSG.Quasithin.Recognition.F112Crit.S3OddFiveCases
public import CFSG.Quasithin.Recognition.F112Crit.OddFiveCenter
public import CFSG.Quasithin.Recognition.F112Crit.OddRhoPair
public import CFSG.Quasithin.Recognition.F112Crit.OddFiveQ
public import CFSG.Quasithin.Recognition.F112Crit.BenderRigid

public section

namespace CFSG.Quasithin.F112Crit

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open CosetGeom (graph stab ballStab nbrs vtype γ₀ γ₁)

variable {G : Type} [Group G] [Finite G]

namespace Setting

variable {L₁ L₂ S Z : Subgroup G}

local notation "ν₀" => γ₀ (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S)
local notation "ν₁" => γ₁ (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S)

theorem false_of_odd_five_of_trich (hs : Setting L₁ L₂ S Z)
    (hS3 : VS3 L₁) (hL : IsRankOneListed (oTwoQuot ↥L₂))
    (hns : ¬ Group.IsSolvable (oTwoQuot ↥L₂))
    (hb : Odd (critB (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S) Z))
    (hb5 : 5 ≤ critB (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S) Z)
    (htri : ∀ μ' ∈ nbrs ν₁, ν₀ ≠ μ' →
      pCoreOf 2 (stab ν₁) ⊓ pCoreOf 2 (stab ν₀) ≤ ballStab 1 μ' ∨
      (∀ ε ∈ nbrs μ', ∀ ε' ∈ nbrs μ', ε ≠ ν₁ → ε' ≠ ν₁ →
        ∃ r : ↥(L₁ ⊔ L₂ ⊔ S), (r : G) ∈ pCoreOf 2 (stab ν₁) ⊓ pCoreOf 2 (stab ν₀) ∧
          r • ε = ε') ∨
      ((∀ k ∈ pCoreOf 2 (stab ν₁) ⊓ pCoreOf 2 (stab ν₀), ∀ g ∈ pCoreOf 2 (stab ν₁),
          k * g * k⁻¹ * g⁻¹ ∈ ballStab 1 μ') ∧
        (∀ a ∈ pCoreOf 2 (stab ν₁), ∀ b ∈ pCoreOf 2 (stab ν₁),
          ∃ k ∈ pCoreOf 2 (stab ν₁) ⊓ pCoreOf 2 (stab ν₀),
            k⁻¹ * (a * b * a⁻¹ * b⁻¹) ∈ ballStab 1 μ') ∧
        (∀ k ∈ pCoreOf 2 (stab ν₁) ⊓ pCoreOf 2 (stab ν₀), k * k ∈ ballStab 1 μ') ∧
        ∃ a ∈ pCoreOf 2 (stab ν₁), ∃ b ∈ pCoreOf 2 (stab ν₁),
          a * b * a⁻¹ * b⁻¹ ∉ ballStab 1 μ')) : False := by
  obtain ⟨n, i, -, hK, -⟩ := exists_isBenderQuot_of_listed hL hns
  have hC := isCartanQuot_of_listed hL hns
  have hR := isRigidQuot_of_listed hL hns
  have hc := hs.toCritAmalgam
  have hμ : vtype ν₀ = false := CosetGeom.vtype_γ₀
  have hδ : ν₁ ∈ nbrs ν₀ := CosetGeom.adj_γ₀_γ₁
  have h0 : ν₀ ∈ nbrs ν₁ := (CosetGeom.adj_γ₀_γ₁ (G₀ := L₁ ⊔ L₂ ⊔ S) (G₁ := P₂ L₁ L₂ S)
    (G₂ := P₁ L₁ L₂ S)).symm
  obtain ⟨X, hX⟩ := hs.exists_isEdgeHall hμ hδ
  exact false_of_pCoreOf_inf_center hc.amalgam CosetGeom.vtype_γ₁ h0 hX
    (hs.torusGraph hK hC hS3 hμ hδ hX) (not_pCoreOf_stab_γ₀_le_ballStab hc hb)
    (fun _ hg _ hδ' hne hfix =>
      (hs.benderRigidVertex hK hC hR).mem_ballStab_of_mem_pCoreOf hc.amalgam hδ hg hδ' hne hfix)
    (fun _ hδ' _ hδ'' hne => hs.exists_pCoreOf_moves_pair hK hS3 hb hμ hδ' hδ'' hne)
    (hs.pCoreOf_inf_center_of_trich hS3 hK hC hb hb5 htri)

end Setting

end CFSG.Quasithin.F112Crit

end
