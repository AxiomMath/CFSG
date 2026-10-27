module

public import CFSG.Sporadic.Schreier.SteinbergBSLyOuterRestriction
public import CFSG.Sporadic.Schreier.LyOuter
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporInputs

public noncomputable section

namespace CFSG.Sporadic.LySchreier

open CFSG.Sporadic.Ly
open CFSG.ComponentClassification.OuterAutomorphisms

theorem bs_restrictC_mem_inner
    (α : autZ) : restrictC α ∈ inner lyC :=
  bs_mem_inner_of_fix lyC_eq_centralizer α (restrictC α) (restrictC_apply α) (mem_autZ.1 α.2)

theorem bs_autZToOuterC_eq_one
    (α : autZ) : autZToOuterC α = 1 := by
  show QuotientGroup.mk' (inner lyC) (restrictC α) = 1
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact bs_restrictC_mem_inner α

theorem bs_inner_J_eq_top :
    inner J = ⊤ := by
  rw [eq_top_iff]
  intro φ _
  obtain ⟨α, hα⟩ := autZToOuterJ_surjective (QuotientGroup.mk' (inner J) φ)
  have h1 : α ∈ autZToOuterC.ker := MonoidHom.mem_ker.2 (bs_autZToOuterC_eq_one α)
  have h2 := ker_autZToOuterC_le h1
  rw [MonoidHom.mem_ker, hα, QuotientGroup.mk'_apply] at h2
  exact (QuotientGroup.eq_one_iff _).1 h2

end CFSG.Sporadic.LySchreier

namespace CFSG.ComponentClassification.RestrictedStd.Spor

open CFSG.Blueprint CFSG.Sporadic.Ly CFSG.Sporadic.LySchreier
open CFSG.ComponentClassification.OuterAutomorphisms

theorem lyOuterTrivialInput :
    LyOuterTrivialInput := by
  have h := inner_map_congr (G := J) (H := NativeSporadic.Ly) (by exact lyEquivJ.symm)
  rw [bs_inner_J_eq_top, Subgroup.map_top_of_surjective _ (MulEquiv.surjective _)] at h
  exact h.symm

end CFSG.ComponentClassification.RestrictedStd.Spor
