module

public import CFSG.LocalAnalysis.StandardType.GGPhiTwoLSS92Input

public section

namespace CFSG.StandardType.PhiTwoRootGen

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] noncomputable def phiTwoComp
    {τ : Tag} {K : Type} [Field K]
    (g0 : ModGL τ (AlgebraicClosure K))
    (β : Fin τ.rank → ℤ) : Subgroup (adjointGroup τ K) :=
  ((rootSpan τ (AlgebraicClosure K) {β, -β}).map (MulAut.conj g0).toMonoidHom).comap
    ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp (adjointGroup τ K).subtype)

theorem mem_phiTwoComp_iff
    {τ : Tag} {K : Type} [Field K]
    {g0 : ModGL τ (AlgebraicClosure K)} {β : Fin τ.rank → ℤ}
    {x : adjointGroup τ K} :
    x ∈ phiTwoComp g0 β ↔
      g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) * g0 ∈
        rootSpan τ (AlgebraicClosure K) {β, -β} := by
  rw [phiTwoComp, Subgroup.mem_comap, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  rfl

theorem phiTwoComp_neg
    {τ : Tag} {K : Type} [Field K]
    (g0 : ModGL τ (AlgebraicClosure K)) (β : Fin τ.rank → ℤ) :
    phiTwoComp g0 (-β) = phiTwoComp g0 β := by
  simp only [phiTwoComp, neg_neg, Set.pair_comm]

end CFSG.StandardType.PhiTwoRootGen

end
