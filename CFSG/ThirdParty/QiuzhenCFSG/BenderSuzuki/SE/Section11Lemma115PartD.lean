module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma113
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Complement
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115PartE

namespace CFSG
end CFSG
open CFSG

/-!
# Section 11, Lemma 11.5: normalization and the `f'`-core centralizer

This module assembles the source-independent quotient/Sylow lift with the
part-(c) anti-fixed subgroup.  It proves part (d), the `f`-group statement for
`C_B(P)`, normalization of `B₁`, and the triviality of `C_{B₁}(P)`.
Only the nontriviality of `B₁` remains for part (e).
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1
open scoped Pointwise

universe u

/-- The checked conclusion of the quotient-normalizer portion of Lemma 11.5.
The final source-model argument is needed only to add `B₁ ≠ 1`. -/
public structure Lemma115PartDConclusion
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t : X}
    (d : Lemma101Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t)
    (B : Subgroup X) (f : ℕ) : Prop where
  f_prime : f.Prime
  NStar_normalizes_B :
    lemma103NStar d.choice.P ≤ Subgroup.normalizer (B : Set X)
  normalizerIn_normalizes_B :
    normalizerIn M d.choice.P ≤ Subgroup.normalizer (B : Set X)
  normalizerIn_normalizes_BOne :
    normalizerIn M d.choice.P ≤
      Subgroup.normalizer (lemma115BOne B f : Set X)
  centralizer_P_isPGroup :
    IsPGroup f (B ⊓ Subgroup.centralizer
      (d.choice.P : Set X) : Subgroup X)
  BOne_inf_centralizer_eq_bot :
    lemma115BOne B f ⊓
      Subgroup.centralizer (d.choice.P : Set X) = ⊥

/-- Assemble part (d) and the checked centralizer half of part (e). -/
public theorem lemma115_partD
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
    Lemma115PartDConclusion d B f := by
  let C : Subgroup X := Subgroup.centralizer ({t * d83.u} : Set X)
  let B : Subgroup X := Subgroup.closure (peterfalviKSet C t)
  let f : ℕ := orderOf (t * d83.u)
  have hfsmall : f = 3 ∨ f = 5 := by
    simpa [f] using h114.modelTransport.order_tu
  have hfprime : f.Prime := by
    rcases hfsmall with hf3 | hf5
    · simpa [hf3] using Nat.prime_three
    · simpa [hf5] using Nat.prime_five
  have hpf : d.choice.p ≠ f := by
    intro h
    rcases hfsmall with hf3 | hf5
    · exact h113.p_ne_three (h.trans hf3)
    · exact h113.p_ne_five (h.trans hf5)
  obtain ⟨d103⟩ := lemma_10_3 d hM ht htM d83 htwo
  obtain ⟨hL⟩ := lemma115_quotient_lift
    hM ht htM d83 h84 d d103
      (by simpa [f] using hpf) (by simpa [f] using hfsmall)
  obtain ⟨_hcomp, _hBsetT, hBsetU, hBcomm, hBodd, _hBcop⟩ :=
    lemma115_B_normal_complement
      hM ht htM d83 h42 htwo d h102 h114
  have hNStar : lemma103NStar d.choice.P ≤
      Subgroup.normalizer (B : Set X) := by
    simpa [B, C] using
      lemma115_lift_normalizes_B d83 d d103 hL B hBsetU hBcomm
  have hNlocal : normalizerIn M d.choice.P ≤
      Subgroup.normalizer (B : Set X) := by
    intro x hx
    exact hNStar hx.2
  have hBOneNorm : normalizerIn M d.choice.P ≤
      Subgroup.normalizer (lemma115BOne B f : Set X) :=
    lemma115_BOne_normalized hNlocal
  have hCBp : IsPGroup f
      (B ⊓ Subgroup.centralizer (d.choice.P : Set X) : Subgroup X) := by
    simpa [f] using
      lemma115_centralizer_P_isPGroup d83 d d103 hL B hBsetU hBodd
  have hBOneCent : lemma115BOne B f ⊓
      Subgroup.centralizer (d.choice.P : Set X) = ⊥ :=
    lemma115_BOne_inf_centralizer_eq_bot hfprime hCBp
  exact
    { f_prime := hfprime
      NStar_normalizes_B := hNStar
      normalizerIn_normalizes_B := hNlocal
      normalizerIn_normalizes_BOne := hBOneNorm
      centralizer_P_isPGroup := hCBp
      BOne_inf_centralizer_eq_bot := hBOneCent }

end CFSG.BenderSuzuki
