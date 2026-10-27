module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section9Lemma99

namespace CFSG
end CFSG
open CFSG

/-!
# Section 9, Proposition 9.3

This file packages the two conclusions of source Proposition 9.3.  The
normal-subgroup assertion is Lemma 9.9, while the nontrivial derived
intersection is the first assertion of Lemma 9.8.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1

universe u

/-- The two conclusions of source Proposition 9.3: a nontrivial subgroup
normal in `V` with nontrivial Peterfalvi centralizer, and
`[E, E] \cap V != 1`. -/
public structure Proposition93Conclusion
    {X : Type u} [Group X]
    (D E : Subgroup X) (t : X) : Prop where
  exists_normal_with_nontrivial_centralizer :
    let V : Subgroup X := peterfalviV D t
    ∃ Y : Subgroup X,
      Y ≤ V ∧ Y ≠ ⊥ ∧
        (Y.subgroupOf V).Normal ∧
        HasNontrivialPeterfalviCentralizer D t Y
  derived_inf_fixed_ne_bot :
    (derivedSubgroup E).map E.subtype ⊓ peterfalviV D t ≠ ⊥

/-- Source Proposition 9.3, assembled from Lemmas 9.8 and 9.9. -/
public theorem proposition_9_3
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t : X}
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t) (htM : t ∉ M)
    (d83 : Lemma83Data M t)
    (h84 : Proposition84Statement M t d83.u)
    (hW : IsMinimalNormalSupplement M
      (M ⊓ rightConjugate M t) W)
    (hIne : ∃ x : X,
      x ∈ peterfalviKSet (M ⊓ rightConjugate M t) t ∧ x ≠ 1)
    (h96 : Corollary96Conclusion
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t)) t)
    (h97 : Lemma97Conclusion M t)
    (h98 : Lemma98Conclusion
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t)) t)
    (h43b : II1Lemma43bCyclic (X := X))
    (h911 : IG911iiNilpotentFrobeniusComplementCyclic (X := X)) :
    Proposition93Conclusion
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t)) t := by
  refine ⟨?_, h98.derived_inf_fixed_ne_bot⟩
  exact lemma_9_9 hM ht htM d83 h84 hW hIne h96 h97 h98
    h43b h911

end CFSG.BenderSuzuki
