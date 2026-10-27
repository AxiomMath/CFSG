module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115PartD
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Endpoint

namespace CFSG
end CFSG
open CFSG

/-!
# Section 11, Lemma 11.5

This file packages the numbered source conclusion from the checked fixed-point,
normal-complement, quotient-normalizer, and recognized-torus modules.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1
open scoped Pointwise

universe u

/-- The literal source package for Lemma 11.5.  The subgroup `B` and the
integer `f` are parameters so later Section 11 statements can use the fields
without repeatedly unfolding their source definitions. -/
public structure Lemma115Conclusion
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t : X}
    (d83 : Lemma83Data M t)
    (d : Lemma101Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t)
    (B : Subgroup X) (f : ℕ) : Prop where
  f_eq_three_or_five : f = 3 ∨ f = 5
  f_prime : f.Prime
  normal_complement :
    IsNormalComplementIn
      (Subgroup.centralizer ({t * d83.u} : Set X))
      (peterfalviV (M ⊓ rightConjugate M t) t) B
  B_eq_peterfalviKSet_t :
    (B : Set X) =
      peterfalviKSet (Subgroup.centralizer ({t * d83.u} : Set X)) t
  B_eq_peterfalviKSet_u :
    (B : Set X) =
      peterfalviKSet (Subgroup.centralizer ({t * d83.u} : Set X)) d83.u
  nonidentity_fixedPoints_eq_empty :
    ∀ x : X, x ∈ B → x ≠ 1 →
      fixedPointsOfSubgroup X (conjugateCosetSpace M)
        (Subgroup.zpowers x) = ∅
  B_commutative : IsMulCommutative B
  B_card_odd : Odd (Nat.card B)
  B_coprime_fitting :
    Nat.Coprime (Nat.card B)
      (Nat.card (fittingSubgroupOf
        (peterfalviV (M ⊓ rightConjugate M t) t)))
  normalizerIn_normalizes_B :
    normalizerIn M d.choice.P ≤ Subgroup.normalizer (B : Set X)
  normalizerIn_normalizes_BOne :
    normalizerIn M d.choice.P ≤
      Subgroup.normalizer (lemma115BOne B f : Set X)
  BOne_ne_bot : lemma115BOne B f ≠ ⊥
  BOne_inf_centralizer_eq_bot :
    lemma115BOne B f ⊓
      Subgroup.centralizer (d.choice.P : Set X) = ⊥

/-- Source Lemma 11.5, assembled from the checked numbered parts. -/
public theorem lemma_11_5
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t : X}
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t) (htM : t ∉ M)
    (d83 : Lemma83Data M t)
    (h84 : Proposition84Statement M t d83.u)
    (h42 : II1Lemma42PrimeTransfer (X := X))
    (htwo : MulAction.IsMultiplyPretransitive X
      (conjugateCosetSpace M) 2)
    (d : Lemma101Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t)
    (h102 : Proposition102Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t)) t d)
    (h113 : Lemma113Conclusion d)
    (h114 : Lemma114Conclusion d83 d) :
    let C := Subgroup.centralizer ({t * d83.u} : Set X)
    let B := Subgroup.closure (peterfalviKSet C t)
    let f := orderOf (t * d83.u)
    Lemma115Conclusion d83 d B f := by
  let C : Subgroup X := Subgroup.centralizer ({t * d83.u} : Set X)
  let B : Subgroup X := Subgroup.closure (peterfalviKSet C t)
  let V : Subgroup X := peterfalviV (M ⊓ rightConjugate M t) t
  let f : ℕ := orderOf (t * d83.u)
  obtain ⟨hcomp, hBsetT, hBsetU, hBcomm, hBodd, hBcop⟩ :=
    lemma115_B_normal_complement
      hM ht htM d83 h42 htwo d h102 h114
  have hfix : ∀ x : X, x ∈ B → x ≠ 1 →
      fixedPointsOfSubgroup X (conjugateCosetSpace M)
        (Subgroup.zpowers x) = ∅ := by
    intro x hxB hxne
    apply lemma115_B_nonidentity_fixedPoints_eq_empty
      hM ht htM d83 htwo h42 d h102 h114
    · rw [← hBsetT]
      exact hxB
    · exact hxne
  have hpartD : Lemma115PartDConclusion d B f := by
    simpa [C, B, f] using
      lemma115_partD hM ht htM d83 h84 h42 htwo d h102 h113 h114
  have hBOneNe : lemma115BOne B f ≠ ⊥ := by
    simpa [C, B, f] using
      lemma115_BOne_ne_bot_of_model_endpoint
        hM ht htM d83 h42 htwo d h102 h113 h114
  exact
    { f_eq_three_or_five := by
        simpa [f] using h114.modelTransport.order_tu
      f_prime := hpartD.f_prime
      normal_complement := by simpa [C, B, V] using hcomp
      B_eq_peterfalviKSet_t := by simpa [C, B] using hBsetT
      B_eq_peterfalviKSet_u := by simpa [C, B] using hBsetU
      nonidentity_fixedPoints_eq_empty := by simpa [C, B] using hfix
      B_commutative := by simpa [C, B] using hBcomm
      B_card_odd := by simpa [C, B] using hBodd
      B_coprime_fitting := by simpa [C, B, V] using hBcop
      normalizerIn_normalizes_B := by
        simpa [C, B] using hpartD.normalizerIn_normalizes_B
      normalizerIn_normalizes_BOne := by
        simpa [C, B, f] using hpartD.normalizerIn_normalizes_BOne
      BOne_ne_bot := by simpa [C, B, f] using hBOneNe
      BOne_inf_centralizer_eq_bot := by
        simpa [C, B, f] using hpartD.BOne_inf_centralizer_eq_bot }

end CFSG.BenderSuzuki
