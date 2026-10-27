module

public import CFSG.RankThree.PartTwo.KFacts.AutPSp4Even
public import CFSG.RankThree.PartOne.SP4C.TauTorus

public section

namespace CFSG.RankThree.PartOne.NF7H

open CFSG.RankThree.PartTwo.KFacts CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.QuasithinUnique.Lin2.Five (fieldAut_eq_one_of_mem_inner)

section Aut

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem sq_eq_one_of_conj_mul_field {α : MulAut (StatedProj (StatedSp 2 F))} {A : gsp 2 F}
    {σ : F ≃+* F} (hα : α = conjAut 2 F A * fieldAut 2 F σ) (h2 : α * α = 1) : σ * σ = 1 := by
  have hN := range_conjAut_normal_of_charTwo (F := F)
  have hcN : conjAut 2 F A ∈ (conjAut 2 F).range := ⟨A, rfl⟩
  have hφα : fieldAut 2 F σ = (conjAut 2 F A)⁻¹ * α := by
    rw [hα]; group
  have hφφ : fieldAut 2 F σ * fieldAut 2 F σ ∈ (conjAut 2 F).range := by
    have h1 : fieldAut 2 F σ * fieldAut 2 F σ =
        (conjAut 2 F A)⁻¹ * (α * (conjAut 2 F A)⁻¹ * α⁻¹) * (α * α) := by
      conv_lhs => rw [hφα]
      group
    rw [h1, h2, mul_one]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hcN)
      (hN.conj_mem _ (Subgroup.inv_mem _ hcN) α)
  obtain ⟨B, hB⟩ := hφφ
  obtain ⟨y, hy⟩ := conjAut_mem_inner_of_charTwo B
  refine fieldAut_eq_one_of_mem_inner (σ := σ * σ) ⟨y, ?_⟩
  rw [map_mul, ← hB]
  exact hy

end Aut

section Torus

open CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.SP4C

variable {p : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem pow_sq_of_sq_eq_one {σ : K ≃+* K} (hσ : σ * σ = 1) {k : ℤ}
    (hk : ∀ v : D8Mod p K, sigVec σ v = v ^ k) : ∀ v : D8Mod p K, v ^ (k * k) = v := by
  intro v
  have h1 : sigVec σ (sigVec σ v) = v := by
    refine Prod.ext (Subtype.ext (Units.ext ?_)) (Subtype.ext (Units.ext ?_))
    · show σ (σ ((v.1 : Kˣ) : K)) = ((v.1 : Kˣ) : K)
      exact congrArg (fun τ : K ≃+* K => τ ((v.1 : Kˣ) : K)) hσ
    · show σ (σ ((v.2 : Kˣ) : K)) = ((v.2 : Kˣ) : K)
      exact congrArg (fun τ : K ≃+* K => τ ((v.2 : Kˣ) : K)) hσ
  have h2 : sigVec σ (sigVec σ v) = v ^ (k * k) := by
    calc sigVec σ (sigVec σ v) = (sigVec σ v) ^ k := hk _
      _ = (v ^ k) ^ k := by rw [hk v]
      _ = v ^ (k * k) := (zpow_mul v k k).symm
  exact h2.symm.trans h1

end Torus

end CFSG.RankThree.PartOne.NF7H
