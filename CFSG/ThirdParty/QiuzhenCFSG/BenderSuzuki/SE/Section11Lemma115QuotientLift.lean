module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Kernel
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115QuotientMembership

namespace CFSG
end CFSG
open CFSG

/-!
# Section 11, Lemma 11.5: the quotient Sylow lift

This module specializes the generic quotient-lift algebra to the faithful
rank-one quotient from Lemma 10.3.  The package stops at the structural facts
used by Lemma 11.5 and does not include any later conclusion about `B` or
`B₁`.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1
open scoped Pointwise

universe u

/-- The image of `tu` in the faithful quotient inverts under `u`. -/
public theorem lemma115_qbar_inverted
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t : X}
    (hM : IsStronglyEmbedded M)
    (d83 : Lemma83Data M t)
    (d : Lemma101Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t)
    (d103 : Lemma103Conclusion M d.choice.P d83.u) :
    ∀ q : lemma103NBar M d.choice.P, q ∈ d103.Qbar →
      rightConjugateElem q d103.uBar = q⁻¹ := by
  classical
  let P : Subgroup X := d.choice.P
  let Nstar : Subgroup X := lemma103NStar P
  let core : Subgroup Nstar := lemma103NZeroStar M P
  let Nbar := Nstar ⧸ core
  let Omega : Type u := lemma103OmegaP M P
  letI : Finite Omega := by
    dsimp [Omega, lemma103OmegaP]
    infer_instance
  letI : MulAction Nstar Omega := lemma103NormalizerAction M P
  let hcoreNormal : (pointStabilizerCore Nstar Omega).Normal :=
    pointStabilizerCore_normal
  letI : (pointStabilizerCore Nstar Omega).Normal := hcoreNormal
  letI : core.Normal := by
    dsimp [core, Nstar, P]
    infer_instance
  letI : MulAction Nbar Omega := lemma103QuotientAction M P
  letI : FaithfulSMul Nbar Omega := lemma103QuotientAction_faithful M P
  let alpha : Omega :=
    ⟨QuotientGroup.mk 1,
      theorem4b_baseCoset_mem_fixedPoints
        (d.choice.P_le_V.trans (inf_le_left.trans inf_le_left))⟩
  have huBaseAmbient : d83.u •
      (QuotientGroup.mk 1 : conjugateCosetSpace M) =
        QuotientGroup.mk 1 := by
    apply MulAction.mem_stabilizer_iff.mp
    simpa [baseCoset_stabilizer] using d83.u_mem_M
  have huAlpha : d103.uBar • alpha = alpha := by
    have hrepresentative : d103.uBar • alpha = d103.uStar • alpha := by
      rw [d103.uBar_eq]
      have hmk := @pointStabilizerCoreQuotientAction_mk_smul
        Nstar Omega _ (lemma103NormalizerAction M P) hcoreNormal
        d103.uStar alpha
      change @SMul.smul Nbar Omega
          (@pointStabilizerCoreQuotientAction Nstar Omega _
            (lemma103NormalizerAction M P) hcoreNormal).toSMul
          (QuotientGroup.mk d103.uStar) alpha = d103.uStar • alpha
      exact hmk
    rw [hrepresentative]
    apply Subtype.ext
    change (d103.uStar : X) • alpha.val = alpha.val
    rw [d103.uStar_eq]
    simpa [alpha] using huBaseAmbient
  obtain ⟨gamma, hgamma, hgammaUnique⟩ :=
    hM.involution_fixed_coset_unique d83.u_involution
  have huBaseUnique : ∀ omega : conjugateCosetSpace M,
      d83.u • omega = omega → omega = QuotientGroup.mk 1 := by
    intro omega homega
    exact (hgammaUnique omega homega).trans
      (hgammaUnique (QuotientGroup.mk 1) huBaseAmbient).symm
  have huUnique : ∀ omega : Omega,
      d103.uBar • omega = omega → omega = alpha := by
    intro omega homega
    have hrepresentative : d103.uBar • omega = d103.uStar • omega := by
      rw [d103.uBar_eq]
      have hmk := @pointStabilizerCoreQuotientAction_mk_smul
        Nstar Omega _ (lemma103NormalizerAction M P) hcoreNormal
        d103.uStar omega
      change @SMul.smul Nbar Omega
          (@pointStabilizerCoreQuotientAction Nstar Omega _
            (lemma103NormalizerAction M P) hcoreNormal).toSMul
          (QuotientGroup.mk d103.uStar) omega = d103.uStar • omega
      exact hmk
    have homegaStar : d103.uStar • omega = omega :=
      hrepresentative.symm.trans homega
    have hval := congrArg Subtype.val homegaStar
    change (d103.uStar : X) • omega.val = omega.val at hval
    rw [d103.uStar_eq] at hval
    apply Subtype.ext
    exact huBaseUnique omega.val hval
  letI : Fact d103.q.Prime := ⟨d103.q_prime⟩
  letI : IsElementaryAbelian d103.q d103.Qbar :=
    d103.Qbar_elementaryAbelian
  have hQcomm : IsMulCommutative d103.Qbar := inferInstance
  exact lemma115_regular_normal_inverted_by_unique_fixed_involution
    d103.Qbar d103.Qbar_normal hQcomm d103.Qbar_regular
      d103.uBar_involution alpha huAlpha huUnique

/-- The structural conclusions of the quotient/Sylow part of Lemma 11.5. -/
public structure Lemma115QuotientLiftConclusion
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t : X}
    (d83 : Lemma83Data M t)
    (d : Lemma101Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t)
    (d103 : Lemma103Conclusion M d.choice.P d83.u)
    (f : ℕ) where
  Q : Subgroup (lemma103NStar d.choice.P)
  Q_normal : Q.Normal
  Q_factorization :
    Q ⊔ Subgroup.centralizer
      ({d103.uStar} : Set (lemma103NStar d.choice.P)) = ⊤
  Q_sylow : theorem4bIsSylowSubgroupOf f Q
    (d103.Qbar.comap
      (QuotientGroup.mk' (lemma103NZeroStar M d.choice.P)))
  Q_map : Q.map (QuotientGroup.mk' (lemma103NZeroStar M d.choice.P)) = d103.Qbar
  Q_isPGroup : IsPGroup f Q
  Q_odd : Odd (Nat.card Q)
  Q_disjoint_core : Disjoint Q (lemma103NZeroStar M d.choice.P)
  Q_inverted : ∀ q : Q, rightConjugateElem (q : lemma103NStar d.choice.P)
      d103.uStar = (q : lemma103NStar d.choice.P)⁻¹
  tuStar : lemma103NStar d.choice.P
  tuStar_eq : (tuStar : X) = t * d83.u
  tuStar_mem_Q : tuStar ∈ Q
  commutator_eq :
    ⁅(lemma103NZeroStar M d.choice.P) ⊔ Q,
      Subgroup.zpowers d103.uStar⁆ = Q

/-- The quotient Sylow lift package used in Lemma 11.5. -/
public theorem lemma115_quotient_lift
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
    (d103 : Lemma103Conclusion M d.choice.P d83.u)
    (hpf : d.choice.p ≠ orderOf (t * d83.u))
    (hfsmall : orderOf (t * d83.u) = 3 ∨
      orderOf (t * d83.u) = 5) :
    Nonempty (Lemma115QuotientLiftConclusion d83 d d103
      (orderOf (t * d83.u))) := by
  classical
  let P : Subgroup X := d.choice.P
  let Nstar : Subgroup X := lemma103NStar P
  let core : Subgroup Nstar := lemma103NZeroStar M P
  let Nbar := Nstar ⧸ core
  let a : X := t * d83.u
  let f : ℕ := orderOf a
  have hfprime : f.Prime := by
    rcases hfsmall with hf3 | hf5
    · simpa [f, a, hf3] using (by decide : Nat.Prime 3)
    · simpa [f, a, hf5] using (by decide : Nat.Prime 5)
  have hfodd : Odd f := by
    rcases hfsmall with hf3 | hf5
    · simpa [f, a, hf3] using (by decide : Odd 3)
    · simpa [f, a, hf5] using (by decide : Odd 5)
  have hPcentt : P ≤ Subgroup.centralizer ({t} : Set X) := by
    intro x hx
    exact (d.choice.P_le_V hx).2
  have hPcentu : P ≤ Subgroup.centralizer ({d83.u} : Set X) := by
    intro x hx
    have hxV := d.choice.P_le_V hx
    change x ∈ (M ⊓ rightConjugate M t) ⊓
      Subgroup.centralizer ({t} : Set X) at hxV
    rw [d83.centralizer_eq] at hxV
    exact hxV.2
  have haCentP : a ∈ Subgroup.centralizer (P : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxt : x * t = t * x :=
      Subgroup.mem_centralizer_singleton_iff.mp (hPcentt hx)
    have hxu : x * d83.u = d83.u * x :=
      Subgroup.mem_centralizer_singleton_iff.mp (hPcentu hx)
    dsimp [a]
    calc
      x * (t * d83.u) = (x * t) * d83.u := by group
      _ = (t * x) * d83.u := by rw [hxt]
      _ = t * (x * d83.u) := by group
      _ = t * (d83.u * x) := by rw [hxu]
      _ = (t * d83.u) * x := by group
  have haNstar : a ∈ Nstar := centralizer_le_normalizer P haCentP
  let aStar : Nstar := ⟨a, haNstar⟩
  have haStarOrder : orderOf aStar = f := by
    calc
      orderOf aStar = orderOf (aStar : X) :=
        (Subgroup.orderOf_coe aStar).symm
      _ = f := rfl
  have hkernelEq : core.map Nstar.subtype = P := by
    simpa [core, Nstar, P] using
      lemma115_actionKernel_image_eq_P hM ht htM d83 h84 d
  have haStarNotCore : aStar ∉ core := by
    intro haCore
    have haP : a ∈ P := by
      rw [← hkernelEq]
      exact Subgroup.mem_map.mpr ⟨aStar, haCore, rfl⟩
    have hfdvdP : orderOf a ∣ Nat.card P :=
      Subgroup.orderOf_dvd_natCard P haP
    have hfdvdp : f ∣ d.choice.p := by
      rw [show Nat.card P = d.choice.p by simpa [P] using d.P_card] at hfdvdP
      simpa [f, a] using hfdvdP
    have hfeq : f = d.choice.p :=
      (Nat.prime_dvd_prime_iff_eq hfprime d.choice.p_prime).mp hfdvdp
    exact hpf (by simpa [f, a] using hfeq.symm)
  let aBar : Nbar := QuotientGroup.mk' core aStar
  have haBarOrder : orderOf aBar = f := by
    exact lemma115_orderOf_quotient_eq_prime_of_not_mem
      core hfprime haStarOrder haStarNotCore
  have haStarInv : rightConjugateElem aStar d103.uStar = aStar⁻¹ := by
    apply Subtype.ext
    change (d103.uStar : X)⁻¹ * a * (d103.uStar : X) = a⁻¹
    rw [d103.uStar_eq]
    dsimp [a]
    rw [d83.u_involution.inv_eq_self]
    have huu : d83.u * d83.u = 1 := by
      simpa [pow_two] using d83.u_involution.sq_eq_one
    calc
      d83.u * (t * d83.u) * d83.u =
          d83.u * t * (d83.u * d83.u) := by group
      _ = d83.u * t := by rw [huu, mul_one]
      _ = (t * d83.u)⁻¹ := by
        simp [mul_inv_rev, ht.inv_eq_self, d83.u_involution.inv_eq_self]
  have haBarInv : rightConjugateElem aBar d103.uBar = aBar⁻¹ := by
    rw [d103.uBar_eq]
    simpa [aBar, rightConjugateElem] using
      congrArg (QuotientGroup.mk' core) haStarInv
  have haBarOdd : Odd (orderOf aBar) := by
    rw [haBarOrder]
    exact hfodd
  letI : d103.Qbar.Normal := d103.Qbar_normal
  have haBarQ : aBar ∈ d103.Qbar :=
    lemma115_inverted_odd_order_mem_normal_factor d103.Qbar
      d103.factorization haBarOdd haBarInv
  have haBarNe : aBar ≠ 1 := by
    intro h
    have horderOne : orderOf aBar = 1 := orderOf_eq_one_iff.mpr h
    rw [haBarOrder] at horderOne
    exact hfprime.ne_one horderOne
  letI : Fact d103.q.Prime := ⟨d103.q_prime⟩
  letI : IsElementaryAbelian d103.q d103.Qbar :=
    d103.Qbar_elementaryAbelian
  have haBarPow : aBar ^ d103.q = 1 :=
    elemPow_eq_one_of_isElementaryAbelian aBar haBarQ
  have haBarOrderQ : orderOf aBar = d103.q :=
    orderOf_eq_prime haBarPow haBarNe
  have hqf : d103.q = f := by
    rw [haBarOrder] at haBarOrderQ
    exact haBarOrderQ.symm
  have hQbarf : IsPGroup f d103.Qbar := by
    rw [← hqf]
    exact IsElementaryAbelian.isPGroup d103.q d103.Qbar
  have hcoreOdd : Odd (Nat.card core) := by
    simpa [core, Nstar, P] using d.actionKernel_odd hM ht htM
  have hcoreCard : Nat.card core = d.choice.p := by
    calc
      Nat.card core = Nat.card (core.map Nstar.subtype) := by
        symm
        exact Subgroup.card_map_of_injective Nstar.subtype_injective
      _ = Nat.card P := by rw [hkernelEq]
      _ = d.choice.p := d.P_card
  have hcorep : IsPGroup d.choice.p core := by
    apply IsPGroup.of_card (n := 1)
    simp [hcoreCard]
  have hcoreCentU : core ≤
      Subgroup.centralizer ({d103.uStar} : Set Nstar) := by
    intro z hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    change (z : X) * (d103.uStar : X) =
      (d103.uStar : X) * (z : X)
    rw [d103.uStar_eq]
    have hzP : (z : X) ∈ P := by
      rw [← hkernelEq]
      exact Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mp (hPcentu hzP)
  have huStarMem : d83.u ∈ Nstar :=
    centralizer_le_normalizer P (by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact Subgroup.mem_centralizer_singleton_iff.mp (hPcentu hx))
  have huStar : IsInvolution d103.uStar := by
    let uStar' : Nstar := ⟨d83.u, huStarMem⟩
    have huStar' : IsInvolution uStar' :=
      IsInvolution.subtype d83.u_involution huStarMem
    have heq : uStar' = d103.uStar := by
      apply Subtype.ext
      exact d103.uStar_eq.symm
    rw [← heq]
    exact huStar'
  letI : core.Normal := by
    dsimp [core, Nstar, P]
    infer_instance
  obtain ⟨Q, hQsyl, hQmap, _huNormQ, hdisj, hQinv⟩ :=
    lemma115_exists_invariant_inverted_sylow_lift core hcoreOdd
      d.choice.p_prime hfprime (by simpa [f, a] using hpf)
      hcorep huStar d103.Qbar d103.Qbar_normal
      d103.Qbar_card_odd hQbarf (by
        simpa [Nbar, core, Nstar, P, d103.uBar_eq] using
          lemma115_qbar_inverted hM d83 d d103)
  let H : Subgroup Nstar :=
    d103.Qbar.comap (QuotientGroup.mk' core)
  have hQH : Q ≤ H := by
    rcases hQsyl with ⟨S, rfl⟩
    exact Subgroup.map_subtype_le (S : Subgroup H)
  have hHodd : Odd (Nat.card H) := by
    rw [show Nat.card H = Nat.card core * Nat.card d103.Qbar by
      simpa [H] using lemma115_card_quotient_subgroup_comap core d103.Qbar]
    exact hcoreOdd.mul d103.Qbar_card_odd
  have hQodd : Odd (Nat.card Q) :=
    hHodd.of_dvd_nat (Subgroup.card_dvd_of_le hQH)
  have hQf : IsPGroup f Q := by
    rcases hQsyl with ⟨S, rfl⟩
    exact S.isPGroup'.map H.subtype
  obtain ⟨hQnormal, hQfactor, hanti⟩ :=
    lemma115_odd_lift_normal_factorization core Q hcoreOdd
      d103.Qbar d103.Qbar_normal huStar hcoreCentU hQmap hQodd hQinv
      (by simpa [Nbar, core, Nstar, P, d103.uBar_eq] using
        d103.factorization)
  have haStarH : aStar ∈ H := by
    change QuotientGroup.mk' core aStar ∈ d103.Qbar
    simpa [aBar] using haBarQ
  have haStarQ : aStar ∈ Q :=
    (hanti aStar haStarH).mp haStarInv
  have hcomm : ⁅core ⊔ Q, Subgroup.zpowers d103.uStar⁆ = Q := by
    letI : Q.Normal := hQnormal
    exact lemma115_commutator_odd_lift_eq core Q hQodd huStar hcoreCentU hQinv
  let tuStar : Nstar := aStar
  refine ⟨{
    Q := Q
    Q_normal := hQnormal
    Q_factorization := hQfactor
    Q_sylow := hQsyl
    Q_map := hQmap
    Q_isPGroup := hQf
    Q_odd := hQodd
    Q_disjoint_core := hdisj
    Q_inverted := by
      intro q
      exact hQinv (q : Nstar) q.property
    tuStar := tuStar
    tuStar_eq := rfl
    tuStar_mem_Q := haStarQ
    commutator_eq := hcomm }⟩

end CFSG.BenderSuzuki
