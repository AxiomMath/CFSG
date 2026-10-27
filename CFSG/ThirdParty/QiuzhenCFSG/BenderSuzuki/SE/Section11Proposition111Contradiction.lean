module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section10Proposition102Final
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma112

namespace CFSG
end CFSG
open CFSG

/-!
# Section 11: the final Proposition 11.1 contradiction

This module isolates the last source-independent step of Sections 9--11.
Once Proposition 11.1 supplies that `N_M(P)` normalizes `F(V)`, Lemma 11.2
applied to `F(V)P` forces `F(V) ≤ P`.  Proposition 10.2 makes these groups
groups for distinct primes, so `F(V)=1`, contradicting the nontrivial
`r`-subgroup already contained in `F(V)`.

No conclusion of Proposition 11.1, Theorem 6, or Theorem SE is built into an
assumption other than the explicit normalization premise being consumed.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1
open scoped Pointwise

universe u

/-- Lemma 11.2 turns Proposition 11.1's normalization conclusion into
`F(V)=1`.  This is the reusable algebraic core of the final contradiction. -/
public theorem proposition111_fitting_eq_bot_of_normalizes
    {X : Type u} [Group X] [Finite X]
    {M W D E : Subgroup X} {t : X}
    (d : Lemma101Conclusion M W D E (peterfalviV D t) t)
    (h102 : Proposition102Conclusion M W D E t d)
    (hmax : ∀ Y : Subgroup X,
      d.choice.P ≤ Y →
      Y ≤ peterfalviV D t →
      normalizerIn M d.choice.P ≤ Subgroup.normalizer (Y : Set X) →
      Y = d.choice.P)
    (hNnormF : normalizerIn M d.choice.P ≤
      Subgroup.normalizer (fittingSubgroupOf (peterfalviV D t) : Set X)) :
    fittingSubgroupOf (peterfalviV D t) = ⊥ := by
  let V : Subgroup X := peterfalviV D t
  let F : Subgroup X := fittingSubgroupOf V
  let P : Subgroup X := d.choice.P
  let N : Subgroup X := normalizerIn M P
  let Y : Subgroup X := F ⊔ P
  have hYV : Y ≤ V := by
    exact sup_le (by simpa [F, V] using fittingSubgroupOf_le V)
      (by simpa [P, V] using d.choice.P_le_V)
  have hPY : P ≤ Y := le_sup_right
  have hNnormY : N ≤ Subgroup.normalizer (Y : Set X) := by
    intro x hx
    apply mem_normalizer_sup_of_mem_normalizers
    · exact hNnormF hx
    · exact hx.2
  have hYeqP : Y = P := by
    exact hmax Y hPY hYV hNnormY
  have hFleP : F ≤ P := by
    intro x hxF
    have hxY : x ∈ F ⊔ P :=
      (show F ≤ F ⊔ P from le_sup_left) hxF
    have hxY' : x ∈ Y := by simpa [Y] using hxY
    rw [hYeqP] at hxY'
    exact hxY'
  have hFp : IsPGroup h102.exponent.r F := by
    have hFeq : F =
        (derivedSubgroup E).map E.subtype ⊓ peterfalviV D t := by
      simpa [F, V] using h102.fitting_eq_derived_inf
    rw [hFeq]
    exact h102.derived_inf_isPGroup
  have hPp : IsPGroup d.choice.p P := by
    obtain ⟨PD, hPD⟩ := d.P_sylow_D
    have hPp0 : IsPGroup d.choice.p d.choice.P := by
      rw [hPD]
      exact PD.isPGroup'.map D.subtype
    simpa [P] using hPp0
  letI : Fact h102.exponent.r.Prime := ⟨h102.exponent.r_prime⟩
  letI : Fact d.choice.p.Prime := ⟨d.choice.p_prime⟩
  have hdisj : Disjoint F P :=
    IsPGroup.disjoint_of_ne h102.exponent.r d.choice.p
      h102.exponent.r_ne_p F P hFp hPp
  apply eq_bot_iff.mpr
  intro x hxF
  exact hdisj.le_bot ⟨hxF, hFleP hxF⟩

/-- The literal Proposition 10.2 package makes the preceding triviality
impossible: its selected nontrivial subgroup `R` lies in `F(V)`. -/
public theorem proposition111_false_of_normalizes_fitting
    {X : Type u} [Group X] [Finite X]
    {M W D E : Subgroup X} {t : X}
    (d : Lemma101Conclusion M W D E (peterfalviV D t) t)
    (h102 : Proposition102Conclusion M W D E t d)
    (hmax : ∀ Y : Subgroup X,
      d.choice.P ≤ Y →
      Y ≤ peterfalviV D t →
      normalizerIn M d.choice.P ≤ Subgroup.normalizer (Y : Set X) →
      Y = d.choice.P)
    (hNnormF : normalizerIn M d.choice.P ≤
      Subgroup.normalizer (fittingSubgroupOf (peterfalviV D t) : Set X)) :
    False := by
  have hFbot := proposition111_fitting_eq_bot_of_normalizes
    d h102 hmax hNnormF
  apply h102.exponent.R_ne_bot
  apply eq_bot_iff.mpr
  intro x hxR
  have hxF : x ∈ fittingSubgroupOf (peterfalviV D t) := by
    rw [h102.fitting_eq_derived_inf]
    exact h102.exponent.R_le_derived_inf_V hxR
  simpa [hFbot] using hxF

/-- Specialization of the final contradiction to the numbered Lemma 11.2
maximality theorem.  The sole Proposition 11.1 input is the displayed
normalization premise. -/
public theorem proposition111_fitting_contradiction
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t : X}
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t) (htM : t ∉ M)
    (d83 : Lemma83Data M t)
    (h84 : Proposition84Statement M t d83.u)
    (d : Lemma101Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t)
    (h102 : Proposition102Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t)) t d)
    (hNnormF : normalizerIn M d.choice.P ≤
      Subgroup.normalizer
        (fittingSubgroupOf
          (peterfalviV (M ⊓ rightConjugate M t) t) : Set X)) :
    False := by
  exact proposition111_false_of_normalizes_fitting d h102
    (lemma_11_2 hM ht htM d83 h84 d) hNnormF

end CFSG.BenderSuzuki
