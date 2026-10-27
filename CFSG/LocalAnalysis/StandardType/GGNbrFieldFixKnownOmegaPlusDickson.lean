module

public import CFSG.RankThree.PartOne.KC.OrthogonalCommutatorBridge
public import CFSG.RankThree.PartOne.S11d.OrthDicksonOmega
public import CFSG.RankThree.PartOne.S11d.OrthRankBase

public section

namespace CFSG.RankThree.PartOne.FieldFix

open Module QuadraticMap CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear CFSG.RankThree.OrthogonalInvolutions
open CFSG.RankThree.Classical2 (orthDerived)

variable {K : Type} [Field K] {k : Subfield K} {d : ℕ} {Q₀ : QuadraticForm k (Fin d → k)}
  {Q : QuadraticForm K (Fin d → K)}

theorem mem_matrixDerived_of_glIncl [Finite K] [CharP K 2]
    (hnd₀ : (polarBilin Q₀).Nondegenerate)
    (hT₀ : ∃ U : Submodule k (Fin d → k), finrank k U = 3 ∧ ∀ u ∈ U, Q₀ u = 0)
    (hnd : (polarBilin Q).Nondegenerate) {x : GL (Fin d) k} (hx : x ∈ matrixIsometries Q₀)
    (hxD : glIncl k x ∈ matrixDerived Q) : x ∈ matrixDerived Q₀ := by
  haveI : Finite k := Finite.of_injective (algebraMap k K) (algebraMap k K).injective
  have hyD : matrixLinearIso (glIncl k x) ∈ orthDerived Q := by
    rw [← CFSG.RankThree.PartOne.KCOrthComm.map_matrixDerived Q]
    exact ⟨glIncl k x, hxD, rfl⟩
  have hyΩ := orthDerived_le_omegaGroup hnd hyD
  have heven : Even (finrank K (commSpace (matrixLinearEquiv (glIncl k x)))) :=
    (mem_omegaGroup.mp hyΩ).2
  rw [finrank_commSpace_glIncl] at heven
  have hxΩ : matrixLinearIso x ∈ omegaGroup Q₀ hnd₀ := mem_omegaGroup.mpr ⟨hx, heven⟩
  have h := omegaGroup_le_orthDerived hnd₀ hT₀ hxΩ
  rw [← CFSG.RankThree.PartOne.KCOrthComm.map_matrixDerived Q₀] at h
  obtain ⟨x', hx', hx'x⟩ := h
  have : x' = x := matrixLinearIso.injective hx'x
  exact this ▸ hx'

end CFSG.RankThree.PartOne.FieldFix

end
