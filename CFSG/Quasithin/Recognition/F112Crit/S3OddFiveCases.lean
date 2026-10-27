module

public import CFSG.Quasithin.Recognition.F112Crit.S3OddFiveTrans
public import CFSG.Quasithin.Recognition.F112Crit.OddFiveNotU
public import CFSG.Quasithin.Recognition.F112Crit.OddFiveOne

public section

namespace CFSG.Quasithin.F112Crit

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open CosetGeom (graph stab ballStab nbrs vtype γ₀ γ₁)

variable {G : Type} [Group G] [Finite G]

namespace Setting

variable {L₁ L₂ S Z : Subgroup G}

local notation "ν₀" => γ₀ (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S)
local notation "ν₁" => γ₁ (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S)

theorem pCoreOf_inf_center_of_trich (hs : Setting L₁ L₂ S Z) (hS3 : VS3 L₁) {q i : ℕ}
    (hK : IsBenderQuot (oTwoQuot ↥L₂) q i) (hC : IsCartanQuot (oTwoQuot ↥L₂))
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
          a * b * a⁻¹ * b⁻¹ ∉ ballStab 1 μ')) :
    ∀ μ ∈ nbrs ν₁, ∀ μ' ∈ nbrs ν₁, μ ≠ μ' →
      (∀ k ∈ pCoreOf 2 (stab ν₁) ⊓ pCoreOf 2 (stab μ), ∀ g ∈ pCoreOf 2 (stab ν₁),
          k * g * k⁻¹ * g⁻¹ ∈ ballStab 1 μ') ∧
        (∀ a ∈ pCoreOf 2 (stab ν₁), ∀ b ∈ pCoreOf 2 (stab ν₁),
          ∃ k ∈ pCoreOf 2 (stab ν₁) ⊓ pCoreOf 2 (stab μ),
            k⁻¹ * (a * b * a⁻¹ * b⁻¹) ∈ ballStab 1 μ') ∧
        (∀ k ∈ pCoreOf 2 (stab ν₁) ⊓ pCoreOf 2 (stab μ), k * k ∈ ballStab 1 μ') ∧
        ∃ a ∈ pCoreOf 2 (stab ν₁), ∃ b ∈ pCoreOf 2 (stab ν₁),
          a * b * a⁻¹ * b⁻¹ ∉ ballStab 1 μ' := by
  have hc := hs.toCritAmalgam
  have hP : APrime.S3Point _ _ _ ν₁ :=
    (APrime.amalgamS3_of_setting hs.hyp hS3 hs.S_le).s3Point_γ₁
  have h0 : ν₀ ∈ nbrs ν₁ := (CosetGeom.adj_γ₀_γ₁ (G₀ := L₁ ⊔ L₂ ⊔ S) (G₁ := P₂ L₁ L₂ S)
    (G₂ := P₁ L₁ L₂ S)).symm
  have hfix : ∀ g : ↥(L₁ ⊔ L₂ ⊔ S), (g : G) ∈ stab ν₁ → g • ν₁ = ν₁ := fun _ hg =>
    CosetGeom.smul_eq_of_mem_stab hg
  obtain ⟨μ₁, hμ₁, hne₁⟩ : ∃ μ₁ ∈ nbrs ν₁, ν₀ ≠ μ₁ := by
    by_contra hcon
    have hle := Set.ncard_le_ncard (fun x hx => Set.mem_singleton_iff.mpr
      (not_not.mp fun h => hcon ⟨x, hx, Ne.symm h⟩) : nbrs ν₁ ⊆ {ν₀}) (Set.finite_singleton _)
    rw [Set.ncard_singleton, hP.ncard_nbrs] at hle
    omega
  rcases htri μ₁ hμ₁ hne₁ with h1 | h2 | h3
  ·
    exfalso
    refine hs.false_of_pCoreOf_inf_le_ballStab hS3 hb hb5 fun μ' hμ' => ?_
    by_cases hμ'0 : μ' = ν₀
    · subst hμ'0
      have hQ := CosetGeom.pCoreOf_stab_le_ballStab_one hc.amalgam ν₀
      rw [hc.stab_γ₀_eq] at hQ
      exact inf_le_left.trans hQ
    · obtain ⟨g, hg, hg0, hg1⟩ := hP.exists_stab_smul_pair h0 hμ₁ hne₁ h0 hμ' (Ne.symm hμ'0)
      have h1' := pCoreOf_inf_le_ballStab_smul g h1
      rw [hfix g hg, hg0, hg1, hc.stab_γ₀_eq, hc.stab_γ₁_eq] at h1'
      exact (inf_comm _ _).le.trans h1'
  ·
    exfalso
    refine hs.false_of_pCoreOf_inf_trans_base hK hC hS3 hb hb5
      fun μ' hμ' hμ'0 ε hε ε' hε' hε1 hε'1 => ?_
    obtain ⟨g, hg, hg0, hg1⟩ := hP.exists_stab_smul_pair h0 hμ₁ hne₁ h0 hμ' (Ne.symm hμ'0)
    have h2' := pCoreOf_inf_trans_smul g h2
    rw [hfix g hg, hg0, hg1] at h2'
    obtain ⟨r, hr, hrε⟩ := h2' ε hε ε' hε' hε1 hε'1
    rw [hc.stab_γ₀_eq, hc.stab_γ₁_eq] at hr
    exact ⟨r, Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hr).2, (Subgroup.mem_inf.mp hr).1⟩, hrε⟩
  ·
    intro μ hμ μ' hμ' hne
    obtain ⟨g, hg, hg0, hg1⟩ := hP.exists_stab_smul_pair h0 hμ₁ hne₁ hμ hμ' hne
    have h3' := pCoreOf_inf_center_smul g h3
    rwa [hfix g hg, hg0, hg1] at h3'

end Setting

end CFSG.Quasithin.F112Crit

end
