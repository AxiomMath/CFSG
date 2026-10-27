module

public import CFSG.Sporadic.Th.Max3.AllConjFinal
public import CFSG.Sporadic.ThSchreier.KernelAut

public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3 CFSG.ComponentClassification.OuterAutomorphisms

theorem inner_J : inner J = ⊤ :=
  inner_J_eq_top_kernel th_kernel_facts all_involutions_conjugate

theorem inner_Th : inner Blueprint.NativeSporadic.Th = ⊤ :=
  @inner_eq_top_of_equiv Blueprint.NativeSporadic.Th J Units.instGroup _ thEquivJ inner_J

theorem AT_Th_Schreier : Group.IsSolvable (Outer Blueprint.NativeSporadic.Th) := by
  have := subsingleton_outer_of_inner inner_Th
  infer_instance

end CFSG.Sporadic.ThSchreier
