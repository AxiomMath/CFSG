module

public import Mathlib.GroupTheory.Transfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.Residual

namespace CFSG
end CFSG
open CFSG

/-!
# Huppert IV.3.3

Book-order entry file for the Grun transfer-kernel step currently used by the
Thompson fixed-point-free development.


The declarations below record the source theorem itself. The source proof uses
IV.1.7, the transfer cycle formula; Mathlib already provides the transfer
homomorphism and the corresponding orbit-product formula in
`Mathlib.GroupTheory.Transfer`, and the focal transfer interface in
`Mathlib.GroupTheory.Focal`.
-/

namespace CFSG.BenderSuzuki
namespace External

open PFchapter1section1 PFAppendixIII
open scoped Pointwise
set_option maxHeartbeats 0

universe u


/-- The subgroup `P ∩ G'`, regarded as a subgroup of the Sylow subgroup `P`. -/
public abbrev huppertIV33SylowDerivedSubgroup
    {Q : Type u} [Group Q] {q : ℕ} (S : Sylow q Q) :
    Subgroup (S : Subgroup Q) :=
  (commutator Q).comap (S : Subgroup Q).subtype

/-- Huppert IV.3.3, sentence 1.

Since `G/G'(q)` is a `q`-group, the image of a Sylow `q`-subgroup `P` in
that quotient is all of `G/G'(q)`, and hence
`G/G'(q) ≃ P/(P ∩ G'(q))`. -/
public theorem huppert_IV_3_3_quotient_equiv_sylow_mod_abelian_residual
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q) :
    letI : (hktAbelianPResidual q Q).Normal :=
      hktAbelianPResidual_normal (Q := Q) (q := q)
    Nonempty ((Q ⧸ hktAbelianPResidual q Q) ≃*
      ((S : Subgroup Q) ⧸ (hktAbelianPResidual q Q).subgroupOf (S : Subgroup Q))) := by
  classical
  let N : Subgroup Q := hktAbelianPResidual q Q
  haveI : N.Normal := hktAbelianPResidual_normal (Q := Q) (q := q)
  have hquot : IsPGroup q (Q ⧸ N) := by
    simpa [N] using hktAbelianPResidual_quotient_isPGroup (Q := Q) (q := q)
  have hmap_top : (S : Subgroup Q).map (QuotientGroup.mk' N) = ⊤ :=
    sylow_map_quotient_eq_top_of_quotient_isPGroup
      (G := Q) (p := q) S N hquot
  let eRange :
      ((S : Subgroup Q) ⧸ N.subgroupOf (S : Subgroup Q)) ≃*
        (S : Subgroup Q).map (QuotientGroup.mk' N) :=
    quotientSubgroupRangeEquiv (S : Subgroup Q) N
  let eTop :
      (S : Subgroup Q).map (QuotientGroup.mk' N) ≃* Q ⧸ N :=
    (MulEquiv.subgroupCongr hmap_top).trans
      (Subgroup.topEquiv : (⊤ : Subgroup (Q ⧸ N)) ≃* Q ⧸ N)
  exact ⟨(eRange.trans eTop).symm⟩

/-- Huppert IV.3.3, sentence 2.

The Sylow part of the abelian `q`-residual is the Sylow part of the ordinary
commutator subgroup: `P ∩ G'(q) = P ∩ G'`. -/
public theorem huppert_IV_3_3_sylow_inf_abelian_residual_eq_sylow_inf_commutator
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q) :
    (S : Subgroup Q) ⊓ hktAbelianPResidual q Q =
      (S : Subgroup Q) ⊓ commutator Q := by
  classical
  let H : Subgroup Q := S
  let V : Q →* H ⧸ H.feitThompsonFocalSubgroupOf := H.feitThompsonTransferFocal
  have htarget_p : IsPGroup q (H ⧸ H.feitThompsonFocalSubgroupOf) := by
    simpa [H] using S.2.to_quotient ((S : Subgroup Q).feitThompsonFocalSubgroupOf)
  have hquot_ker_p : IsPGroup q (Q ⧸ V.ker) := by
    let e : Q ⧸ V.ker ≃* V.range := QuotientGroup.quotientKerEquivRange V
    have hrange_p : IsPGroup q V.range := htarget_p.to_subgroup V.range
    exact hrange_p.of_equiv e.symm
  have hpResidual_le_ker : hktPResidual q Q ≤ V.ker :=
    hktPResidual_le (Q := Q) (q := q) V.ker inferInstance hquot_ker_p
  have hcomm_le_ker : commutator Q ≤ V.ker := by
    open scoped IsMulCommutative in
    exact Abelianization.commutator_subset_ker (f := V)
  have habResidual_le_ker : hktAbelianPResidual q Q ≤ V.ker :=
    hktAbelianPResidual_le (Q := Q) (q := q) (N := V.ker)
      hcomm_le_ker hpResidual_le_ker
  apply le_antisymm
  · intro x hx
    have hxker : x ∈ V.ker ⊓ H := ⟨habResidual_le_ker hx.2, hx.1⟩
    have hxfocal : x ∈ H.feitThompsonFocalSubgroup := by
      rw [← Subgroup.ker_feitThompsonTransferFocal_inf_eq_feitThompsonFocalSubgroup (P := S)]
      simpa [V, H] using hxker
    exact ⟨hx.1, H.feitThompsonFocalSubgroup_le_commutator hxfocal⟩
  · intro x hx
    refine ⟨hx.1, ?_⟩
    exact commutator_le_hktAbelianPResidual (Q := Q) (q := q) hx.2

/-- Huppert IV.3.3. -/
public theorem huppert_IV_3_3_sylow_abelian_residual
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q) :
    let K : Subgroup (S : Subgroup Q) :=
      huppertIV33SylowDerivedSubgroup (Q := Q) (q := q) S
    letI : (hktAbelianPResidual q Q).Normal :=
      hktAbelianPResidual_normal (Q := Q) (q := q)
    letI : K.Normal := inferInstance
    (S : Subgroup Q) ⊓ hktAbelianPResidual q Q =
        (S : Subgroup Q) ⊓ commutator Q ∧
      Nonempty ((Q ⧸ hktAbelianPResidual q Q) ≃*
        ((S : Subgroup Q) ⧸ K)) := by
  classical
  let N : Subgroup Q := hktAbelianPResidual q Q
  have hNnormal : N.Normal := by
    simpa [N] using hktAbelianPResidual_normal (Q := Q) (q := q)
  haveI : (N.subgroupOf (S : Subgroup Q)).Normal :=
    Subgroup.Normal.subgroupOf (H := N) (K := (S : Subgroup Q)) hNnormal
  let K : Subgroup (S : Subgroup Q) :=
    huppertIV33SylowDerivedSubgroup (Q := Q) (q := q) S
  have hSN : (S : Subgroup Q) ⊓ N = (S : Subgroup Q) ⊓ commutator Q := by
    simpa [N] using
      huppert_IV_3_3_sylow_inf_abelian_residual_eq_sylow_inf_commutator
        (Q := Q) (q := q) S
  have hsub : N.subgroupOf (S : Subgroup Q) = K := by
    ext x
    constructor
    · intro hxN
      have hxinf : (x : Q) ∈ (S : Subgroup Q) ⊓ N := ⟨x.2, hxN⟩
      have hxcomm : (x : Q) ∈ (S : Subgroup Q) ⊓ commutator Q := by
        simpa [hSN] using hxinf
      simpa [K, huppertIV33SylowDerivedSubgroup, Subgroup.mem_comap] using
        Subgroup.mem_subgroupOf.mpr hxcomm.2
    · intro hxK
      have hxcomm : (x : Q) ∈ (S : Subgroup Q) ⊓ commutator Q := by
        refine ⟨x.2, ?_⟩
        simpa [K, huppertIV33SylowDerivedSubgroup, Subgroup.mem_comap] using
          Subgroup.mem_subgroupOf.mp hxK
      have hxN : (x : Q) ∈ (S : Subgroup Q) ⊓ N := by
        simpa [hSN] using hxcomm
      exact hxN.2
  have hKnormal : K.Normal := by
    rw [← hsub]
    infer_instance
  haveI : K.Normal := hKnormal
  constructor
  · simpa [N] using hSN
  · rcases huppert_IV_3_3_quotient_equiv_sylow_mod_abelian_residual
        (Q := Q) (q := q) S with ⟨e⟩
    exact ⟨by
      simpa [N, K] using e.trans (QuotientGroup.quotientMulEquivOfEq hsub)⟩


end External
end CFSG.BenderSuzuki
