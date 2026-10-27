module

public import CFSG.Sporadic.Th.Max3.AllConjFinal
public import CFSG.LocalAnalysis.ComponentClassification.SporadicSchreierDispatch
public import CFSG.Sporadic.ThSchreier.KernelAut

public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Blueprint CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.SporadicSchreierDispatch

theorem ctuc_Th_full_automorphism_group :
    inner J = ⊤ ∧ ∀ (K : Type*) [Group K], Nonempty (K ≃* NativeSporadic.Th) →
      inner K = ⊤ ∧ Subsingleton (Outer K) := by
  have hJ : inner J = ⊤ := inner_J_eq_top_kernel th_kernel_facts all_involutions_conjugate
  refine ⟨hJ, fun K instK ⟨e⟩ => ?_⟩
  have hK : inner K = ⊤ := @inner_eq_top_of_equiv K J instK (Subgroup.toGroup J)
    (@MulEquiv.trans K NativeSporadic.Th J _ Units.instMul _ e thEquivJ) hJ
  exact ⟨hK, subsingleton_outer_of_inner hK⟩

theorem outer_Th_isSolvable :
    Group.IsSolvable (Outer NativeSporadic.Th) := by
  have hTh : @inner NativeSporadic.Th Units.instGroup = ⊤ :=
    @inner_eq_top_of_equiv NativeSporadic.Th J Units.instGroup (Subgroup.toGroup J) thEquivJ
      ctuc_Th_full_automorphism_group.{0}.1
  have := @subsingleton_outer_of_inner NativeSporadic.Th Units.instGroup hTh
  infer_instance

theorem sporadicSchreierCase_Th :
    SporadicSchreierCase .Th :=
  sporadicSchreierCase_of_outer outer_Th_isSolvable

end CFSG.Sporadic.ThSchreier
