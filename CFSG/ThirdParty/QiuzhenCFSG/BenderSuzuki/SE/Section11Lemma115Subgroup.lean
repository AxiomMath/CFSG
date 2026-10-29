module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Centralizer

namespace CFSG
end CFSG
open CFSG

/-!
# Section 11, Lemma 11.5: fixed points of the anti-fixed subgroup

This module proves part (b) of Lemma 11.5.  An arbitrary nonidentity element
inverted by the outside involution has at most two fixed cosets; the prime-
order element \`tu\` then acts on that fixed-point set and forces it to be empty.
No subgroup or complement conclusion from Lemma 11.5 is assumed.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1
open scoped Pointwise

universe u

public theorem lemma115_fixedPoints_card_le_two_of_inverted
    {X : Type u} [Group X] [Finite X]
    {M : Subgroup X} (hM : IsStronglyEmbedded M)
    {t x : X} (ht : IsInvolution t) (htM : t ∉ M)
    (d83 : Lemma83Data M t)
    (htwo : MulAction.IsMultiplyPretransitive X
      (conjugateCosetSpace M) 2)
    (hxinv : rightConjugateElem x t = x⁻¹)
    (hxne : x ≠ 1) :
    Nat.card (theorem4bFixedPoints M (Subgroup.zpowers x)) ≤ 2 := by
  classical
  by_cases hall : ∀ omega : conjugateCosetSpace M,
      x • omega = omega → t • omega = omega
  · let F : theorem4bFixedPoints M (Subgroup.zpowers x) →
        theorem4bFixedPoints M (Subgroup.zpowers t) := fun omega =>
      ⟨omega, mem_fixedPointsOfSubgroup_zpowers_iff.mpr
        (hall omega (mem_fixedPointsOfSubgroup_zpowers_iff.mp omega.property))⟩
    have hFinj : Function.Injective F := by
      intro a b hab
      apply Subtype.ext
      simpa [F] using congrArg Subtype.val hab
    have hle := Nat.card_le_card_of_injective F hFinj
    rw [hM.involution_fixedPoints_card_eq_one ht] at hle
    omega
  · push Not at hall
    obtain ⟨lambda, hxLambda, htLambdaNe⟩ := hall
    have hxInvLambda : x⁻¹ • lambda = lambda := by
      calc
        x⁻¹ • lambda = x⁻¹ • (x • lambda) := by rw [hxLambda]
        _ = lambda := inv_smul_smul x lambda
    have hxx : x * t = t * x⁻¹ := by
      have hconj : t * x * t = x⁻¹ := by
        simpa [rightConjugateElem, ht.inv_eq_self] using hxinv
      have htt : t * t = 1 := by
        simpa [pow_two] using ht.sq_eq_one
      calc
        x * t = t * (t * x * t) := by simp [← mul_assoc, htt]
        _ = t * x⁻¹ := by rw [hconj]
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
    have hkOrder : orderOf k = orderOf x := by
      calc
        orderOf k = orderOf x0 := by
          simpa [k, rightConjugateElem, MulAut.conj_symm_apply] using
            (MulEquiv.orderOf_eq (MulAut.conj d).symm x0)
        _ = orderOf x := hx0Order
    have hkne : k ≠ 1 := by
      intro hkone
      apply hxne
      apply orderOf_eq_one_iff.mp
      calc
        orderOf x = orderOf k := hkOrder.symm
        _ = 1 := by simp [hkone]
    have hkcard : Nat.card
        (theorem4bFixedPoints M (Subgroup.zpowers k)) = 2 := by
      exact d83.fixedPoints_card_eq_two (by simpa [D] using hkK) hkne
    have hx0card : Nat.card
        (theorem4bFixedPoints M (Subgroup.zpowers x0)) =
          Nat.card (theorem4bFixedPoints M (Subgroup.zpowers x)) := by
      have hsub : rightConjugate (Subgroup.zpowers x) g⁻¹ =
          Subgroup.zpowers x0 := by
        rw [rightConjugate, Subgroup.conjBy, MonoidHom.map_zpowers]
        simp [x0, rightConjugateElem]
      rw [← hsub]
      exact Nat.card_congr
        (theorem4bFixedPoints_rightConjugateEquiv M (Subgroup.zpowers x) g⁻¹)
    have hkcard' : Nat.card
        (theorem4bFixedPoints M (Subgroup.zpowers k)) =
          Nat.card (theorem4bFixedPoints M (Subgroup.zpowers x0)) := by
      have hsub : rightConjugate (Subgroup.zpowers x0) d =
          Subgroup.zpowers k := by
        rw [rightConjugate, Subgroup.conjBy, MonoidHom.map_zpowers]
        simp [k, rightConjugateElem]
      rw [← hsub]
      exact Nat.card_congr
        (theorem4bFixedPoints_rightConjugateEquiv M (Subgroup.zpowers x0) d)
    omega

public theorem lemma115_fixedPoints_eq_empty_of_commuting_prime
    {X Omega : Type u} [Group X] [Finite X]
    [MulAction X Omega] [Finite Omega]
    {a x : X} {f : ℕ}
    (hf : f.Prime) (hf3 : 3 ≤ f)
    (haorder : orderOf a = f)
    (hax : Commute a x)
    (hcard : Nat.card {omega : Omega //
      omega ∈ fixedPointsOfSubgroup X Omega (Subgroup.zpowers x)} ≤ 2)
    (hfixa : fixedPointsOfSubgroup X Omega (Subgroup.zpowers a) = ∅) :
    fixedPointsOfSubgroup X Omega (Subgroup.zpowers x) = ∅ := by
  classical
  by_contra hne
  have hnonempty :
      (fixedPointsOfSubgroup X Omega (Subgroup.zpowers x)).Nonempty :=
    Set.nonempty_iff_ne_empty.mpr hne
  let FixedX := {omega : Omega //
    omega ∈ fixedPointsOfSubgroup X Omega (Subgroup.zpowers x)}
  let omega0 : FixedX := ⟨hnonempty.choose, hnonempty.choose_spec⟩
  letI : Nonempty FixedX := ⟨omega0⟩
  let P : Subgroup X := Subgroup.zpowers x
  let N : Subgroup X := Subgroup.normalizer (P : Set X)
  have haCent : a ∈ Subgroup.centralizer (P : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hyP
    rcases Subgroup.mem_zpowers_iff.mp hyP with ⟨n, rfl⟩
    exact (hax.zpow_right n).eq.symm
  have haNorm : a ∈ N := by
    exact centralizer_le_normalizer P haCent
  let aN : N := ⟨a, haNorm⟩
  let A : Subgroup N := Subgroup.zpowers aN
  have haNorder : orderOf aN = f := by
    simpa [aN, Subgroup.orderOf_coe] using haorder
  have hApg : IsPGroup f A := by
    apply IsPGroup.of_card (p := f) (G := A) (n := 1)
    simp [A, Nat.card_zpowers, haNorder]
  letI : Fact (Nat.Prime f) := ⟨hf⟩
  letI : MulAction N FixedX := normalizerFixedPointAction X Omega P
  have hnotdvd : ¬ f ∣ Nat.card FixedX := by
    intro hdiv
    have hpos : 0 < Nat.card FixedX := Nat.card_pos
    have hfle : f ≤ Nat.card FixedX := Nat.le_of_dvd hpos hdiv
    have hle2 : Nat.card FixedX ≤ 2 := by simpa [FixedX] using hcard
    omega
  obtain ⟨omega, homega⟩ :=
    hApg.nonempty_fixed_point_of_prime_not_dvd_card FixedX hnotdvd
  let gen : A := ⟨aN, Subgroup.mem_zpowers aN⟩
  have hgen : gen • omega = omega :=
    MulAction.mem_fixedPoints.mp homega gen
  have haomega : a • (omega : FixedX).1 = (omega : FixedX).1 := by
    have hval := congrArg Subtype.val hgen
    change a • (omega : FixedX).1 = (omega : FixedX).1 at hval
    exact hval
  have hmem : (omega : FixedX).1 ∈
      fixedPointsOfSubgroup X Omega (Subgroup.zpowers a) :=
    mem_fixedPointsOfSubgroup_zpowers_iff.mpr haomega
  rw [hfixa] at hmem
  exact hmem

public theorem lemma115_B_nonidentity_fixedPoints_eq_empty
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
    ∀ {x : X}, x ∈ peterfalviKSet
      (Subgroup.centralizer ({t * d83.u} : Set X)) t → x ≠ 1 →
      fixedPointsOfSubgroup X (conjugateCosetSpace M)
        (Subgroup.zpowers x) = ∅ := by
  intro x hxB hxne
  let f : ℕ := orderOf (t * d83.u)
  have hfsmall : f = 3 ∨ f = 5 := by
    simpa [f] using h114.modelTransport.order_tu
  have hfprime : f.Prime := by
    rcases hfsmall with h3 | h5
    · simpa [h3] using Nat.prime_three
    · simpa [h5] using Nat.prime_five
  have hf3 : 3 ≤ f := by
    rcases hfsmall with h3 | h5 <;> omega
  have hax : Commute (t * d83.u) x := by
    exact (Subgroup.mem_centralizer_singleton_iff.mp hxB.1).symm
  have hcard := lemma115_fixedPoints_card_le_two_of_inverted
    hM ht htM d83 htwo hxB.2 hxne
  apply lemma115_fixedPoints_eq_empty_of_commuting_prime
    hfprime hf3 (by rfl) hax hcard
  exact lemma115_tu_fixedPoints_eq_empty
    hM ht htM d83 htwo h42 d h102 h114

end CFSG.BenderSuzuki
