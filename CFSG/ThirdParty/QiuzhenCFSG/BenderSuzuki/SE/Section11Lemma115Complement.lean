module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Disjointness
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Normalizer

namespace CFSG
end CFSG
open CFSG

/-!
# Section 11, Lemma 11.5: the normal complement `B`

This module packages part (c) after the checked support/disjointness argument.
It also proves the elementary equality between the anti-fixed descriptions
relative to the two involutions `t` and `u`, which is the input required by
the quotient-lift normalizer route.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1
open scoped Pointwise

universe u

/-- Inside `C_X(tu)`, being inverted by `t` is equivalent to being inverted
by `u`. -/
public theorem lemma115_peterfalviKSet_centralizer_product_swap
    {X : Type u} [Group X]
    {t u0 : X} (ht : IsInvolution t) (hu : IsInvolution u0) :
    peterfalviKSet (Subgroup.centralizer ({t * u0} : Set X)) t =
      peterfalviKSet (Subgroup.centralizer ({t * u0} : Set X)) u0 := by
  ext x
  constructor
  · intro hx
    refine ⟨hx.1, ?_⟩
    let a : X := t * u0
    have hcomm : Commute a x :=
      (show Commute x a from
        Subgroup.mem_centralizer_singleton_iff.mp hx.1).symm
    have haxa : a * x * a⁻¹ = x := by
      calc
        a * x * a⁻¹ = x * (a * a⁻¹) := by rw [hcomm.eq]; group
        _ = x := by simp
    have htinverts : t * x * t = x⁻¹ := by
      simpa [rightConjugateElem, ht.inv_eq_self] using hx.2
    have htt : t * t = 1 := by
      simpa [pow_two] using ht.sq_eq_one
    have huLeft : t * a = u0 := by
      simp [a, ← mul_assoc, htt]
    have huRight : a⁻¹ * t = u0 := by
      simp [a, ht.inv_eq_self, hu.inv_eq_self, mul_assoc, htt]
    have huinverts : u0 * x * u0 = x⁻¹ := by
      calc
        u0 * x * u0 = (t * a) * x * (a⁻¹ * t) := by
          rw [huLeft, huRight]
        _ = t * (a * x * a⁻¹) * t := by group
        _ = t * x * t := by rw [haxa]
        _ = x⁻¹ := htinverts
    simpa [rightConjugateElem, hu.inv_eq_self] using huinverts
  · intro hx
    refine ⟨hx.1, ?_⟩
    let a : X := t * u0
    have hcomm : Commute a x :=
      (show Commute x a from
        Subgroup.mem_centralizer_singleton_iff.mp hx.1).symm
    have haxainv : a⁻¹ * x * a = x := by
      calc
        a⁻¹ * x * a = x * (a⁻¹ * a) := by
          rw [hcomm.inv_left.eq]
          group
        _ = x := by simp
    have huinverts : u0 * x * u0 = x⁻¹ := by
      simpa [rightConjugateElem, hu.inv_eq_self] using hx.2
    have huu : u0 * u0 = 1 := by
      simpa [pow_two] using hu.sq_eq_one
    have htLeft : u0 * a⁻¹ = t := by
      simp [a, ht.inv_eq_self, hu.inv_eq_self, ← mul_assoc, huu]
    have htRight : a * u0 = t := by
      simp [a, mul_assoc, huu]
    have htinverts : t * x * t = x⁻¹ := by
      calc
        t * x * t = (u0 * a⁻¹) * x * (a * u0) := by
          rw [htLeft, htRight]
        _ = u0 * (a⁻¹ * x * a) * u0 := by group
        _ = u0 * x * u0 := by rw [haxainv]
        _ = x⁻¹ := huinverts
    simpa [rightConjugateElem, ht.inv_eq_self] using htinverts

/-- Part (c) in the source-facing normal-complement form.  The same subgroup
`B` is described as the anti-fixed set for both `t` and `u`. -/
public theorem lemma115_B_normal_complement
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t : X}
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t) (htM : t ∉ M)
    (d83 : Lemma83Data M t)
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
    (h114 : Lemma114Conclusion d83 d) :
    let C := Subgroup.centralizer ({t * d83.u} : Set X)
    let B := Subgroup.closure (peterfalviKSet C t)
    let V := peterfalviV (M ⊓ rightConjugate M t) t
    IsNormalComplementIn C V B ∧
      (B : Set X) = peterfalviKSet C t ∧
      (B : Set X) = peterfalviKSet C d83.u ∧
      IsMulCommutative B ∧
      Odd (Nat.card B) ∧
      Nat.Coprime (Nat.card B)
        (Nat.card (fittingSubgroupOf V)) := by
  classical
  let D : Subgroup X := M ⊓ rightConjugate M t
  let C : Subgroup X := Subgroup.centralizer ({t * d83.u} : Set X)
  let B : Subgroup X := Subgroup.closure (peterfalviKSet C t)
  let V : Subgroup X := peterfalviV D t
  obtain ⟨hBsetT, hBcomm, hBodd, hBcop⟩ :=
    lemma115_B_subgroup_properties
      hM ht htM d83 h42 htwo d h102 h114
  have hBsetU : (B : Set X) = peterfalviKSet C d83.u := by
    calc
      (B : Set X) = peterfalviKSet C t := hBsetT
      _ = peterfalviKSet C d83.u := by
        simpa [C] using
          lemma115_peterfalviKSet_centralizer_product_swap
            ht d83.u_involution
  obtain ⟨_hfactor, _hfactor', hBnormal, hBsupFixed⟩ :=
    lemma115_centralizer_tu_decomposition
      hM ht htM d83 htwo h42 d h102 h114
  have hVeq : peterfalviV C t = V := by
    simpa [C, D, V] using
      lemma115_peterfalviV_centralizer_tu_eq hM ht d83
  have hBleC : B ≤ C := by
    rw [Subgroup.closure_le]
    intro x hx
    exact hx.1
  have hBnormal' : (B.subgroupOf C).Normal := by
    simpa [B, C] using hBnormal
  have hBsup : B ⊔ V = C := by
    simpa [B, C, V, hVeq] using hBsupFixed
  have hBdisj : Disjoint B V := by
    simpa [B, C, D, V] using
      lemma115_closure_B_disjoint_V
        hM ht htM d83 h42 htwo d h102 h114
  exact ⟨
    { le_M := hBleC
      normal_in_M := hBnormal'
      sup_eq := hBsup
      disjoint_D := hBdisj },
    hBsetT, hBsetU, hBcomm, hBodd, hBcop⟩

end CFSG.BenderSuzuki
