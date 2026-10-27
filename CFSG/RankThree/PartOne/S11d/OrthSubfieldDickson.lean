module

public import CFSG.RankThree.PartOne.S11d.OrthRankBase
public import CFSG.RankThree.PartOne.S11d.OrthDicksonOmega
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldFixed
public import CFSG.RankThree.PartOne.KC.OrthogonalCommutatorBridge

public section

namespace CFSG.RankThree.PartOne.FieldFix

open Module QuadraticMap CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear CFSG.RankThree.OrthogonalInvolutions
open CFSG.RankThree.Classical2 (orthDerived)

variable {K : Type} [Field K] {k : Subfield K} {d : ℕ} {Q₀ : QuadraticForm k (Fin d → k)}
  {Q : QuadraticForm K (Fin d → K)}

theorem subfieldFixedGroup_le_derivedImage [Finite K] [CharP K 2] (hext : IsExtension k Q₀ Q)
    (hnd₀ : (polarBilin Q₀).Nondegenerate)
    (hT₀ : ∃ U : Submodule k (Fin d → k), finrank k U = 3 ∧ ∀ u ∈ U, Q₀ u = 0)
    (hnd : (polarBilin Q).Nondegenerate) :
    subfieldFixedGroup k Q₀ Q ≤ subfieldDerivedImage k hext := by
  have : Finite k := Finite.of_injective (algebraMap k K) (algebraMap k K).injective
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨x, hx, hxy⟩ : ∃ x ∈ matrixIsometries Q₀, glIncl k x = y.val := hy
  have hyD : matrixLinearIso y.val ∈ orthDerived Q := by
    rw [← CFSG.RankThree.PartOne.KCOrthComm.map_matrixDerived Q]
    exact ⟨y.val, y.2, rfl⟩
  have hyΩ := orthDerived_le_omegaGroup hnd hyD
  have heven : Even (finrank K (commSpace (matrixLinearEquiv (glIncl k x)))) := by
    rw [hxy]
    exact (mem_omegaGroup.mp hyΩ).2
  rw [finrank_commSpace_glIncl] at heven
  have hxΩ : matrixLinearIso x ∈ omegaGroup Q₀ hnd₀ := mem_omegaGroup.mpr ⟨hx, heven⟩
  have hxD : x ∈ matrixDerived Q₀ := by
    have h := omegaGroup_le_orthDerived hnd₀ hT₀ hxΩ
    rw [← CFSG.RankThree.PartOne.KCOrthComm.map_matrixDerived Q₀] at h
    obtain ⟨x', hx', hx'x⟩ := h
    have : x' = x := matrixLinearIso.injective hx'x
    exact this ▸ hx'
  refine ⟨matrixProjectiveProjection Q₀ ⟨x, hxD⟩, ?_⟩
  rw [incl_mk]
  congr 1
  exact Subtype.ext hxy

end CFSG.RankThree.PartOne.FieldFix
