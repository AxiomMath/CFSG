module

public import CFSG.RankThree.GF2n.Stroth80.Sec715IrrASteps
public import CFSG.RankThree.GF2n.Stroth80.Sec715IrrATwoLines
public import CFSG.RankThree.GF2n.Stroth80.Sec715IrrConfigAStmt

public section

namespace CFSG.RankThree.GF2n.Stroth80.S715L

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank S714
open scoped Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal] {hc : Ctx M Q Z B} {n : ℕ} {K : Type} [Field K] [Finite K]
  {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} {ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)}
  {b : M₀.E}

theorem configAData_of_isLayerConfigA (hS : IsTensorSetup hc n M₀ ρ b) {t : G}
    {ht : t ∈ LB M Q B} (hA : IsLayerConfigA hS ht) :
    ∃ (L₃ L₄ : Type) (_ : AddCommGroup L₃) (_ : Module K L₃) (_ : AddCommGroup L₄)
      (_ : Module K L₄) (ρ₃ : ↥(bar M Q (Rt M (LB M Q B) t)) →* (L₃ ≃ₗ[K] L₃))
      (ρ₄ : ↥(bar M Q (Rt M (LB M Q B) t)) →* (L₄ ≃ₗ[K] L₄))
      (eM : wvQ hS t ≃ₗ[K] (Fin 2 → L₃)) (eN : ↥(deltaSub hS t) ≃ₗ[K] (Fin 2 → L₄))
      (μ : L₃ →ₗ[K] L₄ →ₗ[K] ↥(hc.VtSub hS.model t)) (q₃ : QuadraticForm K L₃)
      (q₄ : QuadraticForm K L₄) (φ ψ : Matrix (Fin 2) (Fin 2) K) (κ : K),
      ConfigAData hS ht ρ₃ ρ₄ eM eN μ q₃ q₄ φ ψ κ := by
  obtain ⟨L₃, L₄, i₁, i₂, i₃, i₄, ρ₃, ρ₄, eM, eN, μ, q₃, q₄, φ, ψ, κ, c₁, c₂, c₃, c₄, c₅, c₆, c₇,
    c₈, c₉, c₁₀, c₁₁, c₁₂, c₁₃, c₁₄, c₁₅, c₁₆, c₁₇, c₁₈⟩ := hA
  exact ⟨L₃, L₄, i₁, i₂, i₃, i₄, ρ₃, ρ₄, eM, eN, μ, q₃, q₄, φ, ψ, κ,
    ⟨c₁, c₂, c₃, c₄, c₅, c₆, c₇, c₈, c₉, c₁₀, c₁₁, c₁₂, c₁₃, c₁₄, c₁₅, c₁₆, c₁₇, c₁₈⟩⟩

theorem sec715IrrA_of (h310chi : Stroth310ChiStatement) (h52a : Stroth52aStatement)
    (hCRW : Sec7CRWStatement) (hMp : Sec7CentreMpStatement)
    (hNonOrth : Sec715NonOrthNbrsStatement) (hLine : Sec715HasLineStatement)
    (hSame : Sec715SameLineOrthStatement) (hRootE : Sec715RootEltStatement) :
    Sec715IrrConfigAStatement := by
  intro G _ _ M Q Z B _ hc n t r hs hr hp hn Z0 hZ0 hZN K _ _ γ M₀ ρ b hS φ₈ hφr hφk e he hTI hA
  obtain ⟨L₃, L₄, i₁, i₂, i₃, i₄, ρ₃, ρ₄, eM, eN, μ, q₃, q₄, φ, ψ, κ, hD⟩ :=
    configAData_of_isLayerConfigA hS hA
  obtain ⟨g₁, g₂, h₁, h₂, v₁, hv₁, v₂, hv₂, e₁, e₂, hB⟩ :=
    hNonOrth G M Q Z B hc n t r hs hr hp hn Z0 hZ0 hZN K γ M₀ ρ b hS φ₈ hφr hφk e he hTI L₃ L₄
      ρ₃ ρ₄ eM eN μ q₃ q₄ φ ψ κ hD
  have hL := hLine G M Q Z B hc n t r hs hr hp hn Z0 hZ0 hZN K γ M₀ ρ b hS φ₈ hφr hφk e he hTI L₃
    L₄ ρ₃ ρ₄ eM eN μ q₃ q₄ φ ψ κ hD
  obtain ⟨f₁, y₁, hf₁, hy₁, -, hl₁⟩ := hL g₁ h₁.1 h₁.2.1 h₁.2.2.1
  obtain ⟨f₂, y₂, hf₂, hy₂, -, hl₂⟩ := hL g₂ h₂.1 h₂.2.1 h₂.2.2.1
  have hdet : det2 f₁ f₂ ≠ 0 := fun h0 =>
    hB (hSame G M Q Z B hc n t r hs hr hp hn Z0 hZ0 hZN K γ M₀ ρ b hS φ₈ hφr hφk e he hTI L₃ L₄
      ρ₃ ρ₄ eM eN μ q₃ q₄ φ ψ κ hD g₁ g₂ f₁ f₂ y₁ y₂ h₁ h₂ hf₁ hf₂ hy₁ hy₂ hl₁ hl₂ h0 v₁ hv₁ v₂ hv₂
      e₁ e₂)
  exact irr_of_two_lines h310chi h52a hCRW hMp hS hs hr hZ0 hD
    (hRootE G M Q Z B hc n t r hs hr hp hn Z0 hZ0 hZN K γ M₀ ρ b hS φ₈ hφr hφk e he hTI L₃ L₄ ρ₃ ρ₄
      eM eN μ q₃ q₄ φ ψ κ hD) h₁ h₂ hf₁ hf₂ hy₁ hy₂ hl₁ hl₂ hdet

end CFSG.RankThree.GF2n.Stroth80.S715L
