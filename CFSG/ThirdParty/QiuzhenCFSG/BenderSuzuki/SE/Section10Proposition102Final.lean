module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section10Proposition102FittingEndpoint
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section10Proposition102SupportEquality
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section10Proposition102Hall
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section10Lemma106Final
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section9Proposition93

namespace CFSG
end CFSG
open CFSG

/-!
# Section 10, Proposition 10.2: final assembly

The preceding modules prove the source-independent algebra, Hall/support,
exponent, Sylow, and Fitting-complement endpoints.  This file packages them
without taking any field of Proposition 10.2 as an input.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1
open scoped Pointwise

universe u

public structure Proposition102Conclusion
    {X : Type u} [Group X] [Finite X]
    (M W D E : Subgroup X) (t : X)
    (d : Lemma101Conclusion M W D E (peterfalviV D t) t) where
  part_a : Proposition102PartAConclusion M W D E (peterfalviV D t) t d
  derived_nilpotent : Group.IsNilpotent ((derivedSubgroup E).map E.subtype)
  derived_hall : IsHallSubgroup
      (subgroupPrimeSet ((derivedSubgroup E).map E.subtype))
      ((derivedSubgroup E).map E.subtype)
  support_iff : ∀ q : Nat.Primes,
      q.val ∣ Nat.card ((derivedSubgroup E).map E.subtype) ↔
        q.val ∣ Nat.card {x : X // x ∈ peterfalviKSet D t}
  exponent : Proposition102ExponentConclusion M W D E t d
  derived_normal_D :
      (((derivedSubgroup E).map E.subtype).subgroupOf D).Normal
  kset_subset_derived :
      peterfalviKSet D t ⊆ (derivedSubgroup E).map E.subtype
  derived_inf_eq_exponent_R :
      exponent.R = (derivedSubgroup E).map E.subtype ⊓ peterfalviV D t
  derived_inf_isPGroup :
      IsPGroup exponent.r
        ((derivedSubgroup E).map E.subtype ⊓ peterfalviV D t : Subgroup X)
  derived_inf_normal_V :
      (exponent.R.subgroupOf (peterfalviV D t)).Normal
  derived_inf_isSylow_V :
      theorem4bIsSylowSubgroupOf exponent.r exponent.R (peterfalviV D t)
  fitting_eq_derived_inf :
      fittingSubgroupOf (peterfalviV D t) =
        (derivedSubgroup E).map E.subtype ⊓ peterfalviV D t
  fitting_centralizer_P :
      subgroupCentralizerIn (fittingSubgroupOf (peterfalviV D t))
        d.choice.P = ⊥

private theorem proposition102_mem_normalizer_of_rightConjugate_eq_of_involution
    {X : Type u} [Group X] {E : Subgroup X} {t : X}
    (ht : IsInvolution t) (hEt : rightConjugate E t = E) :
    t ∈ Subgroup.normalizer (E : Set X) := by
  have hforward {x : X} (hx : x ∈ E) :
      rightConjugateElem x t ∈ E := by
    have hx' := rightConjugateElem_mem_rightConjugate (g := t) hx
    simpa [hEt] using hx'
  rw [Subgroup.mem_normalizer_iff'']
  intro x
  constructor
  · exact hforward
  · intro hxt
    have hback := hforward hxt
    change rightConjugateElem (rightConjugateElem x t) t ∈ E at hback
    rw [← rightConjugateElem_involutive_of_isInvolution ht x]
    exact hback

public theorem proposition_10_2
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t : X}
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t) (htM : t ∉ M)
    (d83 : Lemma83Data M t)
    (hW : IsMinimalNormalSupplement M
      (M ⊓ rightConjugate M t) W)
    (h96 : Corollary96Conclusion
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t)) t)
    (h97 : Lemma97Conclusion M t)
    (d : Lemma101Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t)
    (d106 : Lemma106Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t d)
    (h42 : II1Lemma42PrimeTransfer (X := X))
    (h93 : Proposition93Conclusion
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t)) t) :
    let D : Subgroup X := M ⊓ rightConjugate M t
    let E : Subgroup X := W ⊓ D
    let V : Subgroup X := peterfalviV D t
    Nonempty (Proposition102Conclusion M W D E t d) := by
  classical
  let D : Subgroup X := M ⊓ rightConjugate M t
  let E : Subgroup X := W ⊓ D
  let V : Subgroup X := peterfalviV D t
  let H : Subgroup X := (derivedSubgroup E).map E.subtype
  have hDodd : Odd (Nat.card D) := by
    simpa [D] using hM.inf_rightConjugate_card_odd htM
  have hDnorm : t ∈ Subgroup.normalizer (D : Set X) := by
    simpa [D] using inf_rightConjugate_mem_normalizer_of_isInvolution M ht
  have hEnorm : t ∈ Subgroup.normalizer (E : Set X) := by
    apply proposition102_mem_normalizer_of_rightConjugate_eq_of_involution ht
    simpa [D, E] using h96.rightConjugate_eq
  have hED : E ≤ D := inf_le_right
  have hA : Proposition102PartAConclusion M W D E V t d := by
    simpa [D, E, V] using proposition102_part_a
      (D := D) hW (by simpa [D] using (inf_le_left : D ≤ M)) d d106
        ht hDodd hDnorm
  have hLocal : Proposition102HallLocalData D E t := by
    simpa [D, E, V] using proposition102_part_b_hall_D
      (D := D) hW (by simpa [D] using (inf_le_left : D ≤ M)) d d106 hA
  have hHall : IsHallSubgroup (subgroupPrimeSet H) H := by
    simpa [D, E, V, H] using proposition102_part_b_hall_X
      hM ht htM d83 hW d d106 hA h42
  have hHleD : H ≤ D :=
    (Subgroup.map_subtype_le (derivedSubgroup E)).trans hED
  have hKH : peterfalviKSet D t ⊆ H := by
    intro x hx
    have hxK : x ∈ Subgroup.closure (peterfalviKSet D t) :=
      Subgroup.subset_closure hx
    have hxH0 : x ∈ lemma106H d :=
      (show Subgroup.closure (peterfalviKSet D t) ≤ lemma106H d from
        le_sup_left) hxK
    simpa [H, hA.derived_eq_H] using hxH0
  have hHnorm : t ∈ Subgroup.normalizer (H : Set X) := by
    simpa [H] using
      (proposition102_normalizer_le_normalizer_map_subtype_of_characteristic
        E (derivedSubgroup E))
        (proposition102_mem_normalizer_of_rightConjugate_eq_of_involution
          ht (by simpa [E, D] using h96.rightConjugate_eq))
  have hSupport : ∀ q : Nat.Primes,
      q.val ∣ Nat.card H ↔
        q.val ∣ Nat.card {x : X // x ∈ peterfalviKSet D t} := by
    exact proposition102_prime_support_iff_kset_card ht hDodd hDnorm hHleD
      hHnorm hKH h42 hLocal.support_dvd_kernel
  have hExp : Nonempty (Proposition102ExponentConclusion M W D E t d) := by
    exact proposition102_exponent_data d hA ht hDodd hED hDnorm hEnorm
      (by simpa [H, V] using h93.derived_inf_fixed_ne_bot)
      (by simpa [D, V] using h97.peterfalvi_centralizer_eq_bot)
  obtain ⟨e⟩ := hExp
  have hRp : IsPGroup e.r (H ⊓ V : Subgroup X) := by
    simpa [H, V] using proposition102_derived_inf_isPGroup d hA ht hDodd
      hED hDnorm hEnorm (by simpa [D, V] using
        h97.peterfalvi_centralizer_eq_bot) e
  have hReq : e.R = H ⊓ V := by
    simpa [H, V] using proposition102_exponent_R_eq_derived_inf d hA ht hDodd
      hED hDnorm hEnorm (by simpa [D, V] using
        h97.peterfalvi_centralizer_eq_bot) e
  have hRnormal : (e.R.subgroupOf V).Normal := by
    simpa [H, V] using proposition102_exponent_R_normal_in_V d hA ht hDodd
      hED hDnorm hEnorm (by simpa [D, V] using
        h97.peterfalvi_centralizer_eq_bot) e hLocal.derived_normal_D
  have hRsyl : theorem4bIsSylowSubgroupOf e.r e.R V := by
    simpa [H, V] using proposition102_exponent_R_sylow_V_of_hall_D
      d hA ht hDodd hED hDnorm hEnorm
        (by simpa [D, V] using h97.peterfalvi_centralizer_eq_bot) e
        hLocal.derived_normal_D hLocal.derived_hall_D
  obtain ⟨Q, hprodF, hQeq⟩ :=
    proposition102_fitting_internalDirectProduct_of_normal_sylow
      e.r_prime (by rw [hReq]; exact inf_le_right) hRsyl hRnormal
  have hQbot := proposition102_fitting_complement_eq_bot d hA ht hDodd hED
    hDnorm hEnorm (by simpa [D, V] using h97.peterfalvi_centralizer_eq_bot)
    e hLocal.derived_normal_D Q hprodF hQeq
  have hFit : fittingSubgroupOf V = H ⊓ V := by
    calc
      fittingSubgroupOf V = e.R ⊔ Q := internalDirectProduct_eq_sup hprodF
      _ = e.R := by simp [hQbot]
      _ = H ⊓ V := hReq
  have hCent : subgroupCentralizerIn (fittingSubgroupOf V) d.choice.P = ⊥ := by
    rw [hFit]
    apply le_antisymm
    · intro x hx
      have hxH : x ∈ subgroupCentralizerIn H d.choice.P :=
        ⟨hx.1.1, hx.2⟩
      rw [show subgroupCentralizerIn H d.choice.P = ⊥ by
        simpa [H, V] using hA.centralizer_derived_P] at hxH
      exact hxH
    · exact bot_le
  refine ⟨{
    part_a := hA
    derived_nilpotent := by simpa [H] using proposition102_derived_nilpotent hA
    derived_hall := by simpa [H] using hHall
    support_iff := by simpa [H, D, E] using hSupport
    exponent := e
    derived_normal_D := by simpa [H] using hLocal.derived_normal_D
    kset_subset_derived := by simpa [H] using hKH
    derived_inf_eq_exponent_R := by simpa [H, V] using hReq
    derived_inf_isPGroup := by simpa [H, V] using hRp
    derived_inf_normal_V := by simpa [V] using hRnormal
    derived_inf_isSylow_V := by simpa [V] using hRsyl
    fitting_eq_derived_inf := by simpa [H, V] using hFit
    fitting_centralizer_P := by simpa [V] using hCent }⟩

end CFSG.BenderSuzuki
