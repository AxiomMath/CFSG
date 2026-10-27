module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KGen.Core

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KGen

open Matrix

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]

theorem genLine_of_perfect {p : ℕ} {Γ : Subgroup (GL ι K)} {e₀ : ι → K} {L₀ : Subgroup ↥Γ}
    (hfix : ∀ v ∈ L₀, (((v : ↥Γ) : GL ι K) : Matrix ι ι K) *ᵥ e₀ = e₀)
    (hperf : ⁅L₀, L₀⁆ = L₀) {g : ↥Γ} (hg : g ∈ L₀) (hgp : orderOf g = p) (hp : p ≠ 1)
    {w₀ : ↥Γ} (hw₀ : w₀ ∉ KTabD.lineStab Γ e₀) (hwg : w₀ * g * w₀⁻¹ ∈ Subgroup.zpowers g) :
    KGenProof.GenLine p Γ e₀ := by
  refine ⟨L₀.map Γ.subtype, (g : GL ι K), (w₀ : GL ι K), ?_, ?_, ?_, ⟨g, hg, rfl⟩, ?_, ?_,
    w₀.2, fun h => hw₀ (KTabD.mem_lineStab.mpr h), ?_⟩
  · rintro _ ⟨v, -, rfl⟩
    exact v.2
  · rintro _ ⟨v, hv, rfl⟩
    exact hfix v hv
  · rw [← Subgroup.map_commutator, hperf]
  · rw [← Subgroup.coe_pow, ← hgp, pow_orderOf_eq_one, Subgroup.coe_one]
  · intro h
    exact hp (hgp ▸ orderOf_eq_one_iff.mpr (Subtype.ext h))
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hwg
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [← Subgroup.coe_zpow, hk]; rfl⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.KGen
