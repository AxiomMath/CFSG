module

public import CFSG.Permutation.FiveTransitive.Degree24Order96CycleSupports

public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup
open scoped Pointwise

theorem cycleFactor_support_injective
    {Y : Type} [Fintype Y] [DecidableEq Y]
    (g : Equiv.Perm Y) :
    Function.Injective
      (fun c : g.cycleFactorsFinset => c.1.support) := by
  intro c d hsupport
  change c.1.support = d.1.support at hsupport
  apply Subtype.ext
  apply Equiv.ext
  intro y
  by_cases hy : y ∈ c.1.support
  · have hyd : y ∈ d.1.support := by
      rwa [← hsupport]
    exact
      ((Equiv.Perm.mem_cycleFactorsFinset_iff.mp c.2).2
        y hy).trans
        ((Equiv.Perm.mem_cycleFactorsFinset_iff.mp d.2).2
          y hyd).symm
  · have hyd : y ∉ d.1.support := by
      rwa [← hsupport]
    rw [Equiv.Perm.notMem_support.mp hy,
      Equiv.Perm.notMem_support.mp hyd]

theorem subtype_cycleFactor_support_mem_cycleSupportFinset
    {Y : Type} [Fintype Y] [DecidableEq Y]
    (g : Equiv.Perm Y)
    (a :
      (g.subtypePerm
        (fun _ => g.apply_mem_support)).cycleFactorsFinset) :
    a.1.support.map
          (Function.Embedding.subtype
            (fun y : Y => y ∈ g.support)) ∈
      cycleSupportFinset g := by
  classical
  let gSupport : Equiv.Perm g.support :=
    g.subtypePerm (fun _ => g.apply_mem_support)
  obtain ⟨x, hx⟩ :=
    Equiv.Perm.IsCycle.nonempty_support
      (Equiv.Perm.mem_cycleFactorsFinset_iff.mp a.2).1
  let c : Equiv.Perm Y := g.cycleOf x.1
  have hc :
      c ∈ g.cycleFactorsFinset := by
    exact
      Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr
        x.2
  refine Finset.mem_image.mpr ⟨c, hc, ?_⟩
  have haCycle :
      a.1 = gSupport.cycleOf x :=
    Equiv.Perm.cycle_is_cycleOf hx a.2
  ext y
  simp only [Finset.mem_map,
    Function.Embedding.coe_subtype, Subtype.exists,
    exists_and_right, exists_eq_right]
  constructor
  · intro hy
    have hsame :
        g.SameCycle x.1 y :=
      (Equiv.Perm.mem_support_cycleOf_iff.mp hy).1
    have hySupport : y ∈ g.support :=
      Equiv.Perm.mem_cycleFactorsFinset_support_le hc hy
    refine ⟨hySupport, ?_⟩
    rw [haCycle,
      Equiv.Perm.mem_support_cycleOf_iff]
    refine ⟨?_, ?_⟩
    · obtain ⟨i, hi⟩ := hsame
      refine ⟨i, Subtype.ext ?_⟩
      simpa only [gSupport] using
        (Equiv.Perm.subtypePerm_apply_zpow_of_mem
          (fun _ => g.apply_mem_support) x.2).trans hi
    · exact
        Equiv.Perm.mem_cycleFactorsFinset_support_le
          a.2 hx
  · rintro ⟨hySupport, hy⟩
    rw [haCycle,
      Equiv.Perm.mem_support_cycleOf_iff] at hy
    rw [Equiv.Perm.mem_support_cycleOf_iff]
    refine ⟨?_, x.2⟩
    obtain ⟨i, hi⟩ := hy.1
    refine ⟨i, ?_⟩
    have hiVal := congrArg Subtype.val hi
    simpa only [gSupport] using
      (Equiv.Perm.subtypePerm_apply_zpow_of_mem
        (fun _ => g.apply_mem_support) x.2).symm.trans
          hiVal

end FiveTransitive.Degree24

end CFSG
