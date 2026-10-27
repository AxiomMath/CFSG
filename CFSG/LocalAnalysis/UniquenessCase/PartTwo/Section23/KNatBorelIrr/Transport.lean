module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatBorelIrr.Adjust
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatBorelIrr.Coords
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatBorelIrr.Scalars
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatBorelIrr.Model

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NatBorelIrr

open CFSG.Quasithin Matrix Subgroup CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {W : Type} [CommGroup W] {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem borelIrr_of_hasBorelScalars [Finite W] [Finite K] [CharP K 2] {Γ : Subgroup (GL ι K)}
    {H : Subgroup (MulAut W)} (hreal : (FFModel.nat Γ).Realizes H ⊤ ⊥) {e₀ : ι → K}
    (he0 : e₀ ≠ 0) (hline : KTabC.SylowFixedLine Γ e₀) (hmodel : HasBorelScalars Γ e₀)
    {S P : Subgroup (MulAut W)} (hS : IsSylowIn 2 S H)
    (hNP : H ⊓ normalizer (S : Set (MulAut W)) ≤ P) (hPH : P ≤ H) (hP : ¬ P ≤ stabSub (fixV S))
    {J : Subgroup W} (hJ : J ≤ fixV S)
    (hstab : StableUnder (Hinf P ⊓ normalizer (S : Set (MulAut W))) J) :
    J = ⊥ ∨ J = fixV S := by
  classical
  obtain ⟨U, hU, hscal⟩ := hmodel
  obtain ⟨π, e, he, hπU⟩ := exists_adjusted_natEquiv hreal hS U
  have hcoord : ∀ y : W, y ∈ fixV S ↔ ∃ c : K, Multiplicative.toAdd (e y) = c • e₀ :=
    mem_fixV_iff_coord π e he hS.le U hπU he0 hline hU
  refine eq_bot_or_eq_of_scalar_stable e e₀ (fixV S) J hcoord hJ ?_
  intro c hc y hy
  obtain ⟨t, ht, hte⟩ := hscal (P.comap (toAut π))
    (normalizer_le_comap_toAut π hS.le hπU hNP)
    (not_comap_toAut_le_lineStab π e he hPH hcoord hP) c hc
  obtain ⟨a, ha⟩ := (hcoord y).1 (hJ hy)
  exact ⟨toAut π t y,
    hstab _ (toAut_mem_hinf_inf_normalizer π hS.le hPH hπU ht) y hy, by
      rw [toAut_apply, he t y, ha, Matrix.mulVec_smul, hte]
      exact smul_comm a c e₀⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.NatBorelIrr
