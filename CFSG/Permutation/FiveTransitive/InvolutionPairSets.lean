module

public import Mathlib.Data.Finset.Attr
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Order.BourbakiWitt
public import Mathlib.Tactic.Bound.Init

public section

namespace CFSG

namespace FiveTransitive.InvolutionPairSets

open MulAction

theorem pair_invariant
    {G X:Type*} [Group G] [MulAction G X] (a:G) (ha:a^2=1) (x:X) :
    ∀y:X,y∈({x,a • x}:Set X) ↔ a • y∈({x,a • x}:Set X) := by
  have haa (y:X):a • (a • y)=y := by rw [←mul_smul,←pow_two,ha,one_smul]
  have hf:∀y:X,y∈({x,a • x}:Set X) → a • y∈({x,a • x}:Set X) := by
    intro y hy
    rcases Set.mem_insert_iff.mp hy with rfl|hy
    · exact Set.mem_insert_of_mem _ rfl
    · have he:y=a • x := Set.mem_singleton_iff.mp hy
      rw [he,haa]
      exact Set.mem_insert x _
  intro y
  constructor
  · exact hf y
  · intro hy
    simpa only [haa] using hf (a • y) hy

theorem pair_disjoint_fixed
    {G X:Type*} [Group G] [MulAction G X] (a:G) (ha:a^2=1) (x:X) (hx:a • x≠x) :
    Disjoint ({x,a • x}:Set X) (fixedBy X a) := by
  apply Set.disjoint_left.mpr
  intro y hy hfix
  rcases Set.mem_insert_iff.mp hy with rfl|hy
  · exact hx hfix
  · have he:y=a • x := Set.mem_singleton_iff.mp hy
    have haa:a • (a • x)=x := by rw [←mul_smul,←pow_two,ha,one_smul]
    apply hx
    rw [he] at hfix
    exact hfix.symm.trans haa

theorem fixed_subset_invariant
    {G X:Type*} [Group G] [MulAction G X] (a:G) (ha:a^2=1)
    (U:Set X) (hU:U⊆fixedBy X a) : ∀y:X,y∈U ↔ a • y∈U := by
  intro y
  constructor
  · intro hy
    rw [hU hy]
    exact hy
  · intro hy
    have hfix:a • (a • y)=a • y := hU hy
    have haa:a • (a • y)=y := by rw [←mul_smul,←pow_two,ha,one_smul]
    have he:a • y=y := hfix.symm.trans haa
    rwa [he] at hy

end FiveTransitive.InvolutionPairSets

end CFSG
