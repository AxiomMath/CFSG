module

public import CFSG.LocalAnalysis.StandardType.GGQTwoChartTwoThreeCent
public import CFSG.LieType.BorelTits.FormFlag

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalInvolution.Phan
open scoped Matrix

variable {F0 : Type} [Field F0] [Finite F0] [CharP F0 2]

theorem qtwoDB3_borelTits (hF0 : Nat.card F0 = 4) {m : ℕ} (hm : 2 ≤ m)
    (Dh : Subgroup (Fin m → F0ˣ)) (hdist : ∀ i j : Fin m, i ≠ j → ∃ c ∈ Dh, c i ≠ c j)
    (U : Subgroup (GL (Fin m) F0)) (hU1 : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    (hUu : ∀ u ∈ U, CFSG.LieType.Universal.Unitary.conjTr
        (CFSG.LieType.BorelTits.unitaryInvolution F0 2 1)
        ((u : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *
        ((u : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) = 1)
    (hnorm : ∀ c ∈ Dh, qTwoChartTwoThree_diag c ∈ Subgroup.normalizer (U : Set (GL (Fin m) F0))) :
    False := by
  classical
  have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 F0 :=
    ⟨Nat.prime_two, le_refl 1, by rw [hF0]; norm_num⟩
  have hbar : (h.bar : F0 → F0) =
      fun c => CFSG.LieType.BorelTits.unitaryInvolution F0 2 1 c := by
    funext c
    rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_apply,
      CFSG.LieType.BorelTits.unitaryInvolution_apply]
  have hWu : ∀ w ∈ U, (((w : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0).map h.bar)ᵀ *
      ((w : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) = 1 := by
    intro w hw
    have h1 := hUu w hw
    rw [hbar]
    exact h1
  have hSW : ∀ d ∈ (Dh : Set (Fin m → F0ˣ)), ∀ w ∈ U,
      CFSG.SectionRank.OddCover.diagHom m d * w *
          (CFSG.SectionRank.OddCover.diagHom m d)⁻¹ ∈ U ∧
      (CFSG.SectionRank.OddCover.diagHom m d)⁻¹ * w *
          CFSG.SectionRank.OddCover.diagHom m d ∈ U := by
    intro d hd w hw
    have hdiag : CFSG.SectionRank.OddCover.diagHom m d = qTwoChartTwoThree_diag d := by
      apply Units.ext
      rw [CFSG.SectionRank.OddCover.coe_diagHom]
      rfl
    have hn := hnorm d hd
    rw [Subgroup.mem_normalizer_iff] at hn
    constructor
    · rw [hdiag]
      exact (hn w).mp hw
    · rw [hdiag]
      have hmem : qTwoChartTwoThree_diag d * ((qTwoChartTwoThree_diag d)⁻¹ * w *
          qTwoChartTwoThree_diag d) * (qTwoChartTwoThree_diag d)⁻¹ ∈ U := by
        rw [show qTwoChartTwoThree_diag d * ((qTwoChartTwoThree_diag d)⁻¹ * w *
          qTwoChartTwoThree_diag d) * (qTwoChartTwoThree_diag d)⁻¹ = w by group]
        exact hw
      exact (hn _).mpr hmem
  obtain ⟨s, t, hst, hpair⟩ :=
    CFSG.StandardType.SURepair.exists_pair_of_isPGroup_two h hU2 hU1 hWu hSW
  obtain ⟨c, hc, hcs⟩ := hdist s t hst
  exact hcs (hpair c hc)

end CFSG.StandardType.QTwo

end
