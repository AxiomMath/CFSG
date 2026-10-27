module

public import CFSG.LocalAnalysis.StandardType.PhanEFlagCode

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Flag

open CFSG.Monster.B.Geometry CFSG.LieType.Chevalley.CosetBuilding
  CFSG.ClassicalInvolution.Phan.PhanE

variable {K : Type} [Field K] [Finite K] {f : ℕ} [CharP K 2]

theorem phanEResidueModel_of_chart {ι : Type} {M : CoxeterMatrix ι} {W : Type} [Group W]
    {cs : CoxeterSystem M W} {C : Type} {δ : C → C → W} {w₀ : W} {t : C → C} {J I : Set ι}
    {a x₁ : C} [Finite (cs.parabolic J)] (hB : IsWeylDistanceBuilding cs δ)
    (hw : ∀ w, cs.length (w * w₀) + cs.length w = cs.length w₀)
    (ht : Gate.IsFlipInvolution cs δ w₀ t) (hI : Gate.flipCore cs δ t J a = residue cs δ I x₁)
    (hIJ : I ⊆ J) (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) (code : PhanCode)
    (Θ : ChamberIso ((buildingOver cs δ J).restrict (residue cs δ J a)) (code.sys K))
    (hR0 : ∀ c : ↥(residue cs δ J a), (c : C) ∈ residue cs δ I x₁ ↔ Θ.Φ c ∈ code.R0 K)
    (hψ : ∀ c c' : ↥(residue cs δ J a), (c : C) ∈ residue cs δ I x₁ →
      (c' : C) = Gate.flipPsi cs δ t J a c → Θ.Φ c' = code.psi K f hK (Θ.Φ c)) :
    PhanEResidueModel cs δ K f t J a code := by
  obtain ⟨x, hxR0, hxlen⟩ :=
    exists_length_flipPsi_eq_longest_of_chamberIso Θ hB hw ht hI hIJ hR0 hψ
      (PhanCode.exists_diam_psi hK hq code)
  have hD : cs.length (longest cs J) = code.diam :=
    length_longest_eq_of_chamberIso Θ hB (PhanCode.cdist_le_diam code)
      (PhanCode.exists_cdist_eq_diam code)
  refine ⟨Θ, fun c => ?_⟩
  rw [mem_flipMaxSet_iff_of_chamberIso Θ hB hw ht hI hIJ ⟨x, hxR0, hxlen⟩ hR0 hψ c, hD,
    PhanCode.intrSet_eq hK hq code]

end CFSG.ClassicalInvolution.Phan.PhanE.Flag

end
