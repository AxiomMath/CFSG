module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseComponentData

namespace CFSG
end CFSG
open CFSG

/-!
# The coefficient field in the second-case PSL₂ model is nonexceptional

The selected component is perfect, so its central quotient and hence the
identified `PSL₂(K)` are perfect.  This excludes `|K| = 3` structurally.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- A PSL₂ component quotient selected in the second case has coefficient
field cardinality strictly greater than three. -/
public theorem secondCase_psl2_field_card_gt_three
    {G : Type u} [Group G] [Finite G]
    {c : CentralizerSetup G} {w : SecondCaseWitness c}
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (e : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃* PSL2 K)) :
    3 < Nat.card K := by
  let : Group.IsPerfect d.E :=
    (Group.isPerfect_def).2 d.E_component.2.2.2.1
  let : Group.IsPerfect (d.E ⧸ Subgroup.center d.E) := inferInstance
  have hPSLperf : Group.IsPerfect (PSL2 K) :=
    Group.IsPerfect.ofSurjective (f := e.some.toMonoidHom) e.some.surjective
  have htopPerf : Group.IsPerfect (↑(⊤ : Subgroup (PSL2 K))) := by
    let : Group.IsPerfect (PSL2 K) := hPSLperf
    infer_instance
  exact (psl2_perfect_subnormal_eq_top K hK (⊤ : Subgroup (PSL2 K))
    top_ne_bot htopPerf Subgroup.IsSubnormal.top).1

end CFSG.GorensteinWalter
