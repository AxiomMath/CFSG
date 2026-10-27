module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma114Models

namespace CFSG
end CFSG
open CFSG

/-!
# Section 11, Lemma 11.4

This file packages the checked Corollary 8.5 reapplication and proves the
recognized-model transport corresponding to `[II4; 3.2(e), 2.8(a)]`.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1
open scoped Pointwise

universe u

/-- The numbered Lemma 11.4 package.

The first field records the second application of Corollary 8.5 to the
selected subgroup `A₁`.  The second field keeps the Proposition 8.4 residual
`O^{2'}(C_X(V))` separate from the literal Section 11 involution core
`C_X(V)^°`, including the PSL/Suzuki fixed-field alternatives and the small
action data used in Lemma 11.5. -/
public structure Lemma114Conclusion
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t : X}
    (d83 : Lemma83Data M t)
    (d : Lemma101Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t) : Prop where
  corollary85_A1 :
    Nonempty (Corollary85Conclusion M t d83.u
      d.choice.initial.A1 d.choice.P)
  modelTransport :
    Lemma114ModelTransport M
      (peterfalviV (M ⊓ rightConjugate M t) t)
      d.choice.initial.A1 d.choice.P t d83.u

/-- Source Lemma 11.4, assembled from the checked Section 10 packages. -/
public theorem lemma_11_4
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t : X}
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t) (htM : t ∉ M)
    (d83 : Lemma83Data M t)
    (h84 : Proposition84Statement M t d83.u)
    (h84support : Proposition84ModelSupportStatement M t d83.u)
    (d : Lemma101Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t)
    (h102 : Proposition102Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t)) t d) :
    Lemma114Conclusion d83 d := by
  obtain ⟨c85⟩ := lemma114_corollary85_A1
    hM ht htM d83 h84 d
  have _support := lemma114_modelSupport_A1 d83 h84support d
  exact
    { corollary85_A1 := ⟨c85⟩
      modelTransport :=
        lemma114_modelTransport_of_endpoint hM ht htM d83 h84 d
          h84support h102 c85 }

end CFSG.BenderSuzuki
