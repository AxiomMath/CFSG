module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Lemmas
public import Mathlib.GroupTheory.Index
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# A cardinal bound from a disjoint normalized subgroup

This is the small index calculation used in the `S ≤ E` part of the
linear second-case argument.  If an odd subgroup `R` of `U` is disjoint from
`L` and normalizes `L`, then the join `L ⊔ R` sits in `U`; hence the order of
`R` is bounded by the relative index `[U : L]`.
-/

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

/-- A subgroup disjoint from a normalized subgroup has order at most the
relative index of the latter subgroup. -/
public theorem secondCase_linear_card_le_relIndex_of_disjoint_normalizer
    {G : Type u} [Group G] [Finite G]
    (U L R : Subgroup G)
    (hR : R ≤ U)
    (hdisj : Disjoint L R) :
    Nat.card R ≤ L.relIndex U := by
  let L' : Subgroup U := L.subgroupOf U
  let f : R → U ⧸ L' :=
    fun r => QuotientGroup.mk (⟨(r : G), hR r.2⟩ : U)
  have hf : Function.Injective f := by
    intro x y hxy
    have hquot : (⟨(x : G), hR x.2⟩ : U)⁻¹ *
        (⟨(y : G), hR y.2⟩ : U) ∈ L' :=
      (QuotientGroup.eq).mp hxy
    have hamb : (x : G)⁻¹ * (y : G) ∈ L := by
      exact Subgroup.mem_subgroupOf.mp hquot
    have hRmem : (x : G)⁻¹ * (y : G) ∈ R := by
      exact R.mul_mem (R.inv_mem x.2) y.2
    have hmem : (x : G)⁻¹ * (y : G) ∈ L ⊓ R := ⟨hamb, hRmem⟩
    rw [disjoint_iff.mp hdisj] at hmem
    have hone : (x : G)⁻¹ * (y : G) = 1 := Subgroup.mem_bot.mp hmem
    apply Subtype.ext
    exact inv_mul_eq_one.mp hone
  have hcard : Nat.card (U ⧸ L') = L.relIndex U := by
    rw [Subgroup.relIndex, Subgroup.index_eq_card]
  calc
    Nat.card R ≤ Nat.card (U ⧸ L') := Nat.card_le_card_of_injective f hf
    _ = L.relIndex U := hcard

end CFSG.GorensteinWalter
