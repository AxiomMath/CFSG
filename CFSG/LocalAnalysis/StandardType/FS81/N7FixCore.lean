module

public import CFSG.LocalAnalysis.StandardType.FS81.GoldSharedSylow
public import CFSG.LocalAnalysis.StandardType.FS81.GoldSharedNine
public import CFSG.LocalAnalysis.StandardType.FS81.GoldSharedSection
public import CFSG.LocalAnalysis.StandardType.FS81.N7FixSylow
public import CFSG.LocalAnalysis.StandardType.FS81.N7FixDent
public import CFSG.LocalAnalysis.StandardType.FS81.N7FixQuot
public import CFSG.LocalAnalysis.StandardType.FS81.N7FixQuotTwo

public section

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix

theorem n7Fix_core (hG : GoldExclusionSylow) {X : Type} [Group X] [Finite X]
    (S : N7Setup X) : False := by
  obtain ⟨P, hPH⟩ := S.exists_sylow_le_H
  have hF1P : S.F1 ≤ (P : Subgroup X) := S.F1_le_sylow hPH
  obtain ⟨τ, hτ, hτc⟩ := S.exists_central_E6 hPH P.isPGroup'
  have hτF : τ ∈ S.F1 := Subgroup.subset_closure hτ
  have hab : IsMulCommutative S.F1 := ⟨⟨fun a b => Subtype.ext (S.F1_comm a.2 b.2)⟩⟩
  have hD : ∀ a ∈ S.F1, ∀ d : X, d * τ = τ * d → d⁻¹ * a * d ∈ (P : Subgroup X) →
      d⁻¹ * a * d ∈ S.F1 := fun a ha d hd hP' => S.stronglyClosed_centralizer hτ a ha d hd (hPH hP')
  have hcl := stronglyClosed_of_centralizer P (hF1P hτF) hτc S.F1
    (S.closure_conj_eq_F1 hPH hF1P hτ).symm hab hD
  rcases hG X S.odd_core P S.F1 hF1P hab hcl with hnorm | ⟨R, T₀, hFT, hTR, hRN, hRn, hTn, hT2,
      hodd, hne⟩
  · obtain ⟨x, hx⟩ := S.not_inv
    refine hx (S.eq_smul_e0_of_fixed fun f hf => ?_)
    have hf' : x⁻¹ * f * x ∈ S.F1 := by
      simpa using hnorm.conj_mem f hf x⁻¹
    have h1 : S.ρ (x⁻¹ * f * x) *ᵥ e0 = e0 := S.F1_le_H hf'
    have h2 : S.ρ f * S.ρ x = S.ρ x * S.ρ (x⁻¹ * f * x) := by
      rw [← map_mul, ← map_mul]
      congr 1
      group
    rw [Matrix.mulVec_mulVec, h2, ← Matrix.mulVec_mulVec, h1]
  · rw [S.normalizer_F1] at hRN hRn
    exact hne (le_of_sylow_section hFT hTR hRN hRn hTn hT2 hodd
      (fun T hFT' hTH hn hT => S.le_F1_of_normal_two hFT' hTH hn hT)
      (fun R' hFR hRH hn hodd' => S.le_F1_of_odd_normal hFR hRH hn hodd'))

end CFSG.StandardType.FrameRoute.FS81

end
