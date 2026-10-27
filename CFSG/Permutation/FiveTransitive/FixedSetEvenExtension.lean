module

public import CFSG.Permutation.FiveTransitive.SetwiseSylowNormalizer
public import CFSG.Permutation.FiveTransitive.FixedSetNormalizerPerm
public import Mathlib.GroupTheory.GroupAction.Embedding

public section

namespace CFSG

namespace FiveTransitive.FixedSetEvenExtension

open MulAction FixedSetNormalizerPerm SetwiseSylowNormalizer

theorem sign_eq_one
    {G X:Type*} [Group G] [Finite G] [MulAction G X] [Fintype X]
    {p k:ℕ} [Fact p.Prime] (a:Fin k ↪ X) (P:Sylow p (stabilizer G a))
    (heven:let A := (P:Subgroup (stabilizer G a)).map (stabilizer G a).subtype
      ∀n:G,∀hn:n∈Subgroup.normalizer (A:Set G),
      letI := Fintype.ofFinite (fixedPoints A X)
      letI := Classical.decEq (fixedPoints A X)
      (fixedPerm G X A n hn).sign=1)
    (g:G) (e:Equiv.Perm (fixedPoints
      ((P:Subgroup (stabilizer G a)).map (stabilizer G a).subtype) X))
    (he:∀x,(e x).val=g • x.val) :
    letI := Fintype.ofFinite (fixedPoints
      ((P:Subgroup (stabilizer G a)).map (stabilizer G a).subtype) X)
    letI := Classical.decEq (fixedPoints
      ((P:Subgroup (stabilizer G a)).map (stabilizer G a).subtype) X)
    e.sign=1 := by
  classical
  let A := (P:Subgroup (stabilizer G a)).map (stabilizer G a).subtype
  let F := fixedPoints A X
  let H := fixingSubgroup G F
  have ha:∀i,a i∈F := by
    intro i
    rw [mem_fixedPoints]
    intro r
    obtain ⟨q,hq,hqr⟩ := r.property
    change r.val • a i=a i
    rw [←hqr]
    exact DFunLike.congr_fun q.property i
  have hHK:H≤stabilizer G a := by
    intro h hh
    apply Function.Embedding.ext
    intro i
    exact (mem_fixingSubgroup_iff G).mp hh _ (ha i)
  have hAH:A≤H := by
    intro r hr
    rw [mem_fixingSubgroup_iff]
    intro x hx
    exact mem_fixedPoints.mp hx ⟨r,hr⟩
  obtain ⟨S,hS⟩ := exists_sylow_intermediate (stabilizer G a) H hHK P hAH
  have hg:∀x:X,x∈F ↔ g • x∈F := by
    intro x
    constructor
    · intro hx
      rw [←he ⟨x,hx⟩]
      exact (e ⟨x,hx⟩).property
    · intro hx
      let y:F := ⟨g • x,hx⟩
      have hv:g • (e.symm y).val=g • x := by
        rw [←he,e.apply_symm_apply]
      have heq:(e.symm y).val=x := MulAction.injective g hv
      exact heq ▸ (e.symm y).property
  obtain ⟨n,hn,hng⟩ := exists_same_restriction F S g hg
  change n∈Subgroup.normalizer (((S:Subgroup H).map H.subtype):Set G) at hn
  rw [hS] at hn
  have hp:e=fixedPerm G X A n hn := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    exact (he x).trans (hng x.val x.property).symm
  rw [hp]
  exact heven n hn

end FiveTransitive.FixedSetEvenExtension

end CFSG
