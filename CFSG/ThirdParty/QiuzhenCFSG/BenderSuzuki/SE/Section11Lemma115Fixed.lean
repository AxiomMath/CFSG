module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma114
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Core

namespace CFSG
end CFSG
open CFSG

/-!
# Section 11, Lemma 11.5: fixed-point transport core

This file isolates the ordered-pair argument used to prove that an odd
prime-order element `x`, inverted by the outside involution `t`, has no fixed
coset once every `t`-fixed coset is excluded.  The only earlier-book input is
the implication-shaped `[II1; 4.2]` prime-transfer contract.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1
open scoped Pointwise

universe u

/-- An inverted prime-order element with no common `t`-fixed point has no
fixed coset.  The ordered-pair transport sends a hypothetical fixed coset and
its `t`-translate to the standard base/`t` pair.  The transported element is
then adjusted by an odd-product cyclic conjugator inside the two-point
stabilizer, producing a prime-order element of the Peterfalvi anti-fixed set;
`[II1; 4.2]` contradicts the supplied nondivisibility. -/
public theorem lemma115_fixedPoint_transport_of_prime
    {X : Type u} [Group X] [Finite X]
    {M : Subgroup X} (hM : IsStronglyEmbedded M)
    {t x : X} (ht : IsInvolution t) (htM : t ∉ M)
    (htwo : MulAction.IsMultiplyPretransitive X
      (conjugateCosetSpace M) 2)
    (h42 : II1Lemma42PrimeTransfer (X := X))
    {f : ℕ} (hf : f.Prime) (hxorder : orderOf x = f)
    (hnotdvd : ¬ f ∣ Nat.card {k : X //
      k ∈ peterfalviKSet (M ⊓ rightConjugate M t) t})
    (hxinv : rightConjugateElem x t = x⁻¹)
    (hnoCommonFix : ∀ omega : conjugateCosetSpace M,
      t • omega = omega → x • omega ≠ omega) :
    fixedPointsOfSubgroup X (conjugateCosetSpace M)
      (Subgroup.zpowers x) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.2
  intro lambda hlambda
  have hxLambda : x • lambda = lambda :=
    mem_fixedPointsOfSubgroup_zpowers_iff.mp hlambda
  have htLambdaNe : t • lambda ≠ lambda := by
    intro htLambda
    exact hnoCommonFix lambda htLambda hxLambda
  have hxx : x * t = t * x⁻¹ := by
    have hconj : t * x * t = x⁻¹ := by
      simpa [rightConjugateElem, ht.inv_eq_self] using hxinv
    have htt : t * t = 1 := by
      simpa [pow_two] using ht.sq_eq_one
    calc
      x * t = t * (t * x * t) := by simp [← mul_assoc, htt]
      _ = t * x⁻¹ := by rw [hconj]
  have hxInvLambda : x⁻¹ • lambda = lambda := by
    calc
      x⁻¹ • lambda = x⁻¹ • (x • lambda) := by rw [hxLambda]
      _ = lambda := inv_smul_smul x lambda
  have hxTLambda : x • (t • lambda) = t • lambda := by
    calc
      x • (t • lambda) = (x * t) • lambda := by rw [mul_smul]
      _ = (t * x⁻¹) • lambda := by rw [hxx]
      _ = t • (x⁻¹ • lambda) := by rw [mul_smul]
      _ = t • lambda := by rw [hxInvLambda]
  let alpha : conjugateCosetSpace M := QuotientGroup.mk 1
  let beta : conjugateCosetSpace M := QuotientGroup.mk t
  have hAlphaBeta : alpha ≠ beta := by
    intro h
    apply htM
    simpa [alpha, beta] using QuotientGroup.eq.mp h
  have htwo' : ∀ {a b c d : conjugateCosetSpace M},
      a ≠ b → c ≠ d → ∃ g : X, g • a = c ∧ g • b = d :=
    MulAction.is_two_pretransitive_iff.mp htwo
  obtain ⟨g, hgLambda, hgTLambda⟩ :=
    htwo' (a := lambda) (b := t • lambda) (c := alpha) (d := beta)
      htLambdaNe.symm hAlphaBeta
  have hgInvAlpha : g⁻¹ • alpha = lambda := by
    calc
      g⁻¹ • alpha = g⁻¹ • (g • lambda) := by rw [hgLambda]
      _ = lambda := inv_smul_smul g lambda
  have hgInvBeta : g⁻¹ • beta = t • lambda := by
    calc
      g⁻¹ • beta = g⁻¹ • (g • (t • lambda)) := by rw [hgTLambda]
      _ = t • lambda := inv_smul_smul g (t • lambda)
  let x0 : X := rightConjugateElem x g⁻¹
  let s : X := rightConjugateElem t g⁻¹
  have hx0Alpha : x0 • alpha = alpha := by
    calc
      x0 • alpha = g • (x • (g⁻¹ • alpha)) := by
        simp [x0, rightConjugateElem, mul_smul]
      _ = g • (x • lambda) := by rw [hgInvAlpha]
      _ = g • lambda := by rw [hxLambda]
      _ = alpha := hgLambda
  have hx0Beta : x0 • beta = beta := by
    calc
      x0 • beta = g • (x • (g⁻¹ • beta)) := by
        simp [x0, rightConjugateElem, mul_smul]
      _ = g • (x • (t • lambda)) := by rw [hgInvBeta]
      _ = g • (t • lambda) := by rw [hxTLambda]
      _ = beta := hgTLambda
  have hsAlpha : s • alpha = beta := by
    calc
      s • alpha = g • (t • (g⁻¹ • alpha)) := by
        simp [s, rightConjugateElem, mul_smul]
      _ = g • (t • lambda) := by rw [hgInvAlpha]
      _ = beta := hgTLambda
  have hsBeta : s • beta = alpha := by
    have htt : t * t = 1 := by
      simpa [pow_two] using ht.sq_eq_one
    calc
      s • beta = g • (t • (g⁻¹ • beta)) := by
        simp [s, rightConjugateElem, mul_smul]
      _ = g • (t • (t • lambda)) := by rw [hgInvBeta]
      _ = g • ((t * t) • lambda) := by rw [mul_smul]
      _ = g • lambda := by rw [htt, one_smul]
      _ = alpha := hgLambda
  have htAlpha : t • alpha = beta := by
    simp [alpha, beta, MulAction.Quotient.smul_mk]
  have htBeta : t • beta = alpha := by
    have htt : t * t = 1 := by
      simpa [pow_two] using ht.sq_eq_one
    simp [alpha, beta, MulAction.Quotient.smul_mk, htt]
  let D : Subgroup X := M ⊓ rightConjugate M t
  have hx0D : x0 ∈ D := by
    constructor
    · have hx0Stab : x0 ∈ MulAction.stabilizer X alpha :=
        MulAction.mem_stabilizer_iff.mpr hx0Alpha
      simpa [D, alpha, baseCoset_stabilizer] using hx0Stab
    · have hx0Stab : x0 ∈ MulAction.stabilizer X beta :=
        MulAction.mem_stabilizer_iff.mpr hx0Beta
      simpa [D, beta, conjugateCoset_stabilizer, ht.inv_eq_self] using hx0Stab
  have hstD : s * t ∈ D := by
    constructor
    · have hstAlpha : (s * t) • alpha = alpha := by
        calc
          (s * t) • alpha = s • (t • alpha) := by rw [mul_smul]
          _ = s • beta := by rw [htAlpha]
          _ = alpha := hsBeta
      have hstStab : s * t ∈ MulAction.stabilizer X alpha :=
        MulAction.mem_stabilizer_iff.mpr hstAlpha
      simpa [D, alpha, baseCoset_stabilizer] using hstStab
    · have hstBeta : (s * t) • beta = beta := by
        calc
          (s * t) • beta = s • (t • beta) := by rw [mul_smul]
          _ = s • alpha := by rw [htBeta]
          _ = beta := hsAlpha
      have hstStab : s * t ∈ MulAction.stabilizer X beta :=
        MulAction.mem_stabilizer_iff.mpr hstBeta
      simpa [D, beta, conjugateCoset_stabilizer, ht.inv_eq_self] using hstStab
  have hs : IsInvolution s := isInvolution_rightConjugateElem ht
  have hDodd : Odd (Nat.card D) := by
    simpa [D] using hM.inf_rightConjugate_card_odd htM
  let stD : D := ⟨s * t, hstD⟩
  have hstOdd : Odd (orderOf (s * t)) := by
    have hsub : Odd (orderOf stD) :=
      Odd.of_dvd_nat hDodd (orderOf_dvd_natCard stD)
    simpa [stD, Subgroup.orderOf_coe] using hsub
  obtain ⟨d, hdz, hsd⟩ :=
    exists_zpowers_conjugator_of_odd_product hs ht hstOdd
  have hdD : d ∈ D := (Subgroup.zpowers_le.mpr hstD) hdz
  have hx0inv : rightConjugateElem x0 s = x0⁻¹ := by
    have h := congrArg (fun y : X => rightConjugateElem y g⁻¹) hxinv
    simpa [x0, s, rightConjugateElem, mul_assoc] using h
  let k : X := rightConjugateElem x0 d
  have hkD : k ∈ D := by
    exact D.mul_mem (D.mul_mem (D.inv_mem hdD) hx0D) hdD
  have hkInv : rightConjugateElem k t = k⁻¹ := by
    rw [← hsd]
    have h := congrArg (fun y : X => rightConjugateElem y d) hx0inv
    simpa [k, rightConjugateElem, mul_assoc] using h
  have hkK : k ∈ peterfalviKSet D t := ⟨hkD, hkInv⟩
  have hx0Order : orderOf x0 = orderOf x := by
    simpa [x0, rightConjugateElem, MulAut.conj_apply] using
      (MulEquiv.orderOf_eq (MulAut.conj g⁻¹).symm x)
  have hkOrder : orderOf k = f := by
    calc
      orderOf k = orderOf x0 := by
        simpa [k, rightConjugateElem, MulAut.conj_symm_apply] using
          (MulEquiv.orderOf_eq (MulAut.conj d).symm x0)
      _ = orderOf x := hx0Order
      _ = f := hxorder
  let K : Subgroup X := Subgroup.closure (peterfalviKSet D t)
  let kK : K := ⟨k, Subgroup.subset_closure hkK⟩
  have hkKOrder : orderOf kK = f := by
    rw [← Subgroup.orderOf_coe]
    exact hkOrder
  have hfdvdK : f ∣ Nat.card K := by
    rw [← hkKOrder]
    exact orderOf_dvd_natCard kK
  have hDnorm : t ∈ Subgroup.normalizer (D : Set X) := by
    simpa [D] using inf_rightConjugate_mem_normalizer_of_isInvolution M ht
  apply hnotdvd
  simpa [D, K] using h42 D t hDodd ht hDnorm f hf hfdvdK

/-- The source element `tu` has no fixed coset.  Lemma 11.4 supplies its
prime order and regular action on `Omega_V`; Proposition 10.2 supplies the
anti-fixed-set cardinality whose nondivisibility is checked arithmetically.
The global double transitivity is the already proved Theorem 4(a) input. -/
public theorem lemma115_tu_fixedPoints_eq_empty
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t : X}
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t) (htM : t ∉ M)
    (d83 : Lemma83Data M t)
    (htwo : MulAction.IsMultiplyPretransitive X
      (conjugateCosetSpace M) 2)
    (h42 : II1Lemma42PrimeTransfer (X := X))
    (d : Lemma101Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t)
    (h102 : Proposition102Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t)) t d)
    (h114 : Lemma114Conclusion d83 d) :
    fixedPointsOfSubgroup X (conjugateCosetSpace M)
      (Subgroup.zpowers (t * d83.u)) = ∅ := by
  let D : Subgroup X := M ⊓ rightConjugate M t
  let V : Subgroup X := peterfalviV D t
  let f : ℕ := orderOf (t * d83.u)
  have hfsmall : f = 3 ∨ f = 5 := by
    simpa [f] using h114.modelTransport.order_tu
  have hfprime : f.Prime := by
    rcases hfsmall with h3 | h5
    · simpa [h3] using Nat.prime_three
    · simpa [h5] using Nat.prime_five
  have hDodd : Odd (Nat.card D) := by
    simpa [D] using hM.inf_rightConjugate_card_odd htM
  have hPD : d.choice.P ≤ D :=
    d.choice.P_le_V.trans inf_le_left
  have hPodd : Odd (Nat.card d.choice.P) :=
    Odd.of_dvd_nat hDodd (Subgroup.card_dvd_of_le hPD)
  have hpodd : Odd d.choice.p := by
    simpa [d.P_card] using hPodd
  have hp2 : d.choice.p ≠ 2 := by
    intro hp
    rw [hp] at hpodd
    exact (by decide : ¬ Odd 2) hpodd
  have hnotdvd : ¬ f ∣ Nat.card {k : X //
      k ∈ peterfalviKSet D t} := by
    have hformula := lemma115_small_prime_not_dvd_exponent_product
      (a := h102.exponent.a)
      d.choice.p_prime hp2 hfsmall h102.exponent.r_prime
        h102.exponent.r_dvd_mersenne
    intro hdiv
    apply hformula
    rw [← h102.exponent.kset_card_eq]
    simpa [D] using hdiv
  have htuinv : rightConjugateElem (t * d83.u) t =
      (t * d83.u)⁻¹ := by
    have htt : t * t = 1 := by
      simpa [pow_two] using ht.sq_eq_one
    simp [rightConjugateElem, ht.inv_eq_self,
      d83.u_involution.inv_eq_self, ← mul_assoc, htt]
  have hVt : V ≤ Subgroup.centralizer ({t} : Set X) :=
    inf_le_right
  have hnoCommonFix : ∀ omega : conjugateCosetSpace M,
      t • omega = omega → (t * d83.u) • omega ≠ omega := by
    intro omega htOmega htuOmega
    obtain ⟨gamma, htGamma, hgammaUnique⟩ :=
      hM.involution_fixed_coset_unique ht
    have homegaV : omega ∈
        fixedPointsOfSubgroup X (conjugateCosetSpace M) V := by
      intro v hv
      have hvcomm : (v : X) * t = t * (v : X) :=
        Subgroup.mem_centralizer_singleton_iff.mp (hVt hv)
      have htVOmega : t • ((v : X) • omega) = (v : X) • omega := by
        calc
          t • ((v : X) • omega) = (t * (v : X)) • omega := by
            rw [mul_smul]
          _ = ((v : X) * t) • omega := by rw [hvcomm.symm]
          _ = (v : X) • (t • omega) := by rw [mul_smul]
          _ = (v : X) • omega := by rw [htOmega]
      exact (hgammaUnique ((v : X) • omega) htVOmega).trans
        (hgammaUnique omega htOmega).symm
    let tuZ : Subgroup.zpowers (t * d83.u) :=
      ⟨t * d83.u, Subgroup.mem_zpowers (t * d83.u)⟩
    obtain ⟨q, hqOmega, hqUnique⟩ :=
      h114.modelTransport.tu_regular homegaV homegaV
    have htuZOmega : (tuZ : X) • omega = omega := by
      simpa [tuZ] using htuOmega
    have honeOmega :
        ((1 : Subgroup.zpowers (t * d83.u)) : X) • omega = omega := by
      simp
    have htuEqOne : tuZ = 1 :=
      (hqUnique tuZ htuZOmega).trans (hqUnique 1 honeOmega).symm
    have htuOne : t * d83.u = 1 := congrArg Subtype.val htuEqOne
    have hfone : f = 1 := by
      simpa [f] using orderOf_eq_one_iff.mpr htuOne
    exact hfprime.ne_one hfone
  exact lemma115_fixedPoint_transport_of_prime
    hM ht htM htwo h42 hfprime (by rfl) hnotdvd htuinv hnoCommonFix

/-- The centralizer of the source element `tu` has odd order.  This is the
source-shaped specialization of the general fixed-point-to-centralizer bridge
to the empty fixed-point set proved above. -/
public theorem lemma115_centralizer_tu_odd
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t : X}
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t) (htM : t ∉ M)
    (d83 : Lemma83Data M t)
    (htwo : MulAction.IsMultiplyPretransitive X
      (conjugateCosetSpace M) 2)
    (h42 : II1Lemma42PrimeTransfer (X := X))
    (d : Lemma101Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t)
    (h102 : Proposition102Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t)) t d)
    (h114 : Lemma114Conclusion d83 d) :
    Odd (Nat.card (Subgroup.centralizer
      ({t * d83.u} : Set X))) := by
  apply lemma115_centralizer_odd_of_fixedPoints_eq_empty hM
  exact lemma115_tu_fixedPoints_eq_empty
    hM ht htM d83 htwo h42 d h102 h114

end CFSG.BenderSuzuki
