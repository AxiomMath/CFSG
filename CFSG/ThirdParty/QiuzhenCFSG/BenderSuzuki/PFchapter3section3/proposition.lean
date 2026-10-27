module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter3section3.Basic
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.LinearAlgebra.Dimension.Finite
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.lemma_2
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.lemma_1
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.theorem
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Conjugacy
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section2.corollary
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section2.proposition_2
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section2.AppendixIInput
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.lemma_5
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.RingTheory.AdjoinRoot

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter3section3

open PFchapter1section1 PFAppendixIII
open PFchapter1section3
open PFchapter3section1

/-!
# Peterfalvi, Part II, Chapter III, Section 3 Proposition
-/

public theorem typeB_not_isMulCommutative
    {G : Type*} [Group G] (S : Subgroup G)
    (hB : IsSuzukiTwoTypeB S) : ¬ IsMulCommutative S := by
  classical
  rcases hB with
    ⟨n, _hn, theta, epsilon, tripleLift, cocycle, hepsilon,
      _hperiod, _hnonzero, haddLeft, haddRight, hdiag, hmem, _hone,
      _hsurj, hinj, hmul⟩
  intro hcomm
  let x : S := ⟨tripleLift 0 1 0, hmem 0 1 0⟩
  let y : S := ⟨tripleLift 0 0 1, hmem 0 0 1⟩
  have hcommEq : tripleLift 0 1 0 * tripleLift 0 0 1 =
      tripleLift 0 0 1 * tripleLift 0 1 0 := by
    exact congrArg (fun z : S => (z : G))
      ((@IsMulCommutative.is_comm S _ hcomm).comm x y)
  rw [hmul, hmul] at hcommEq
  have hcross : cocycle 1 0 0 1 = cocycle 0 1 1 0 := by
    simpa only [zero_add, add_zero] using
      (hinj _ _ _ _ _ _ hcommEq).1
  have hsplitLeft :
      cocycle 1 1 1 1 = cocycle 1 0 1 1 + cocycle 0 1 1 1 := by
    simpa using haddLeft 1 0 0 1 1 1
  have hsplitFirst :
      cocycle 1 0 1 1 = cocycle 1 0 1 0 + cocycle 1 0 0 1 := by
    simpa using haddRight 1 0 1 0 0 1
  have hsplitSecond :
      cocycle 0 1 1 1 = cocycle 0 1 1 0 + cocycle 0 1 0 1 := by
    simpa using haddRight 0 1 1 0 0 1
  have hepsilonZero : epsilon = 0 := by
    calc
      epsilon = 1 * theta 1 + epsilon * 1 * theta 1 + 1 * theta 1 := by
        simp only [map_one, mul_one]
        rw [show (1 : BinaryGaloisField n) + epsilon + 1 =
            epsilon + (1 + 1) by ring,
          CharTwo.add_self_eq_zero, add_zero]
      _ = cocycle 1 1 1 1 := (hdiag 1 1).symm
      _ = cocycle 1 0 1 1 + cocycle 0 1 1 1 := hsplitLeft
      _ = (cocycle 1 0 1 0 + cocycle 1 0 0 1) +
            (cocycle 0 1 1 0 + cocycle 0 1 0 1) := by
        rw [hsplitFirst, hsplitSecond]
      _ = (1 + cocycle 1 0 0 1) +
            (cocycle 0 1 1 0 + 1) := by
        rw [hdiag, hdiag]
        simp only [map_one, map_zero, mul_one, mul_zero,
          add_zero, zero_add]
      _ = cocycle 1 0 0 1 + cocycle 0 1 1 0 := by
        rw [show (1 + cocycle 1 0 0 1) +
            (cocycle 0 1 1 0 + 1) =
              (1 + 1) +
                (cocycle 1 0 0 1 + cocycle 0 1 1 0) by abel,
          CharTwo.add_self_eq_zero, zero_add]
      _ = 0 := by rw [hcross, CharTwo.add_self_eq_zero]
  exact hepsilon hepsilonZero

private theorem typeB_card_is_two_power
    {G : Type*} [Group G] {S : Subgroup G}
    (hB : IsSuzukiTwoTypeB S) :
    ∃ m : ℕ, Nat.card (⊤ : Subgroup S) = 2 ^ m := by
  classical
  rcases hB with
    ⟨n, hn, _theta, _epsilon, tripleLift, _cocycle, _hepsilon,
      _hperiod, _hnonzero, _haddLeft, _haddRight, _hdiag, hmem, _hone,
      hsurj, hinj, _hmul⟩
  let F := BinaryGaloisField n
  let tripleFun : F × F × F → S := fun cab =>
    ⟨tripleLift cab.1 cab.2.1 cab.2.2,
      hmem cab.1 cab.2.1 cab.2.2⟩
  have htripleBijective : Function.Bijective tripleFun := by
    constructor
    · intro cab dbf hEq
      have hval := congrArg (fun z : S => (z : G)) hEq
      rcases hinj cab.1 cab.2.1 cab.2.2
          dbf.1 dbf.2.1 dbf.2.2 hval with ⟨h1, h2, h3⟩
      exact Prod.ext h1 (Prod.ext h2 h3)
    · intro x
      rcases hsurj x x.property with ⟨c, a, b, hx⟩
      exact ⟨(c, a, b), Subtype.ext hx.symm⟩
  let tripleEquiv : F × F × F ≃ S :=
    Equiv.ofBijective tripleFun htripleBijective
  have hFcard : Nat.card F = 2 ^ n := by
    simpa [F, BinaryGaloisField] using GaloisField.card 2 n hn
  have hSCard : Nat.card S = (2 ^ n) ^ 3 := by
    calc
      Nat.card S = Nat.card (F × F × F) :=
        (Nat.card_congr tripleEquiv).symm
      _ = Nat.card F * (Nat.card F * Nat.card F) := by
        rw [Nat.card_prod, Nat.card_prod]
      _ = (2 ^ n) ^ 3 := by rw [hFcard]; ring
  refine ⟨n * 3, ?_⟩
  simpa [pow_mul] using hSCard


private theorem q0_card_eq_center_card
    {G : Type*} [Group G] [Finite G]
    (H Q Q0 S : Subgroup G)
    (hQleH : Q ≤ H) (hQ0leQ : Q0 ≤ Q)
    (hQ0def : ∀ x : G, x ∈ Q0 ↔
      x = 1 ∨ (x ∈ H ∧ IsInvolution x))
    (hSQ : S = Q) (hS : IsSuzukiTwoGroup S) :
    Nat.card Q0 = Nat.card (Subgroup.center S) := by
  classical
  have hinvolutions := (higmanTheorem_involutions_center hS).1
  let toCenter : Q0 → Subgroup.center S := fun x =>
    ⟨⟨x, by rw [hSQ]; exact hQ0leQ x.property⟩, by
      rcases (hQ0def (x : G)).mp x.property with hxOne | hxInv
      · have hxOneS : (⟨x, by rw [hSQ]; exact hQ0leQ x.property⟩ : S) = 1 :=
          Subtype.ext hxOne
        rw [hxOneS]
        exact (Subgroup.center S).one_mem
      · have hxInvS : IsInvolution
            (⟨x, by rw [hSQ]; exact hQ0leQ x.property⟩ : S) :=
          ⟨fun hx => hxInv.2.ne_one (congrArg (fun z : S => (z : G)) hx),
            Subtype.ext hxInv.2.sq_eq_one⟩
        have hxMem :
            (⟨x, by rw [hSQ]; exact hQ0leQ x.property⟩ : S) ∈
              involutions S := hxInvS
        rw [hinvolutions] at hxMem
        exact hxMem.1⟩
  have htoCenterInjective : Function.Injective toCenter := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : Subgroup.center S => ((z : S) : G)) hxy
  have htoCenterSurjective : Function.Surjective toCenter := by
    intro z
    by_cases hzOne : (z : S) = 1
    · refine ⟨1, ?_⟩
      apply Subtype.ext
      exact hzOne.symm
    · have hzInv : IsInvolution (z : S) := by
        have hzMem : (z : S) ∈
            {x : S | x ∈ Subgroup.center S ∧ x ≠ 1} := ⟨z.property, hzOne⟩
        rw [← hinvolutions] at hzMem
        exact hzMem
      have hzQ0 : ((z : S) : G) ∈ Q0 := by
        apply (hQ0def ((z : S) : G)).mpr
        refine Or.inr ⟨?_, ?_⟩
        · exact hQleH (by rw [← hSQ]; exact (z : S).property)
        · exact ⟨fun hz => hzInv.ne_one (Subtype.ext hz),
            congrArg (fun x : S => (x : G)) hzInv.sq_eq_one⟩
      refine ⟨⟨((z : S) : G), hzQ0⟩, ?_⟩
      apply Subtype.ext
      rfl
  exact Nat.card_congr
    (Equiv.ofBijective toCenter ⟨htoCenterInjective, htoCenterSurjective⟩)

private theorem q0_mem_iff_center
    {G : Type*} [Group G]
    (H Q Q0 S : Subgroup G)
    (hQleH : Q ≤ H) (_hQ0leQ : Q0 ≤ Q)
    (hQ0def : ∀ x : G, x ∈ Q0 ↔
      x = 1 ∨ (x ∈ H ∧ IsInvolution x))
    (hSQ : S = Q) (hS : IsSuzukiTwoGroup S) (x : S) :
    (x : G) ∈ Q0 ↔ x ∈ Subgroup.center S := by
  have hinvolutions := (higmanTheorem_involutions_center hS).1
  constructor
  · intro hxQ0
    rcases (hQ0def (x : G)).mp hxQ0 with hxOne | hxInv
    · have hxOneS : x = 1 := Subtype.ext hxOne
      rw [hxOneS]
      exact (Subgroup.center S).one_mem
    · have hxInvS : IsInvolution x :=
        ⟨fun hx => hxInv.2.ne_one (congrArg (fun z : S => (z : G)) hx),
          Subtype.ext hxInv.2.sq_eq_one⟩
      have hxMem : x ∈ involutions S := hxInvS
      rw [hinvolutions] at hxMem
      exact hxMem.1
  · intro hxCenter
    by_cases hxOne : x = 1
    · apply (hQ0def (x : G)).mpr
      exact Or.inl (congrArg (fun z : S => (z : G)) hxOne)
    · have hxMem : x ∈
          {z : S | z ∈ Subgroup.center S ∧ z ≠ 1} := ⟨hxCenter, hxOne⟩
      rw [← hinvolutions] at hxMem
      apply (hQ0def (x : G)).mpr
      refine Or.inr ⟨?_, ?_⟩
      · exact hQleH (by rw [← hSQ]; exact x.property)
      · exact ⟨fun hx => hxMem.ne_one (Subtype.ext hx),
          congrArg (fun z : S => (z : G)) hxMem.sq_eq_one⟩

private theorem K_inf_W_eq_bot
    {G : Type*} [Group G] [Finite G]
    (D K V W : Subgroup G) (t : G)
    (hDodd : Odd (Nat.card D)) (htInv : IsInvolution t)
    (hKleD : K ≤ D)
    (hKdef : ∀ x : G, x ∈ K ↔
      x ∈ D ∧ rightConjugateElem x t = x⁻¹)
    (hVeq : V = peterfalviV D t) (hWleV : W ≤ V) :
    K ⊓ W = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hxV : x ∈ peterfalviV D t := by
    rw [← hVeq]
    exact hWleV hx.2
  have hxt : x * t = t * x :=
    Subgroup.mem_centralizer_singleton_iff.mp hxV.2
  have hfix : rightConjugateElem x t = x := by
    calc
      rightConjugateElem x t = t⁻¹ * x * t := rfl
      _ = t * x * t := by rw [htInv.inv_eq_self]
      _ = x * (t * t) := by rw [← hxt, mul_assoc]
      _ = x := by simpa [pow_two] using congrArg (fun z : G => x * z) htInv.sq_eq_one
  have hinv : rightConjugateElem x t = x⁻¹ := (hKdef x).mp hx.1 |>.2
  have hxsq : x ^ 2 = 1 := by
    have hxx : x = x⁻¹ := hfix.symm.trans hinv
    calc
      x ^ 2 = x * x := pow_two x
      _ = x⁻¹ * x := congrArg (fun z : G => z * x) hxx
      _ = 1 := by simp
  let xD : D := ⟨x, hKleD hx.1⟩
  have hxDsq : xD ^ 2 = 1 := Subtype.ext hxsq
  have horderTwo : orderOf xD ∣ 2 :=
    (orderOf_dvd_iff_pow_eq_one).2 hxDsq
  have horderCard : orderOf xD ∣ Nat.card D := orderOf_dvd_natCard xD
  have horderOdd : Odd (orderOf xD) := hDodd.of_dvd_nat horderCard
  have horderOne : orderOf xD = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp horderTwo with h | h
    · exact h
    · exfalso
      rw [h] at horderOdd
      rcases horderOdd with ⟨m, hm⟩
      omega
  have hxDone : xD = 1 := orderOf_eq_one_iff.mp horderOne
  exact congrArg (fun z : D => (z : G)) hxDone

private noncomputable def centerQuotientAction
    (P : Type*) [Group P] :
    MulAut P →* MulAut (P ⧸ Subgroup.center P) := by
  classical
  have hpreserve (alpha : MulAut P) :
      Subgroup.center P ≤ (Subgroup.center P).comap alpha.toMonoidHom := by
    intro z hz
    rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
    intro x
    have hzComm := Subgroup.mem_center_iff.mp hz (alpha.symm x)
    have h := congrArg alpha hzComm
    simpa using h
  let descend (alpha : MulAut P) :
      (P ⧸ Subgroup.center P) →* (P ⧸ Subgroup.center P) :=
    QuotientGroup.map (N := Subgroup.center P) (Subgroup.center P)
      alpha.toMonoidHom (hpreserve alpha)
  have hdescend_mk (alpha : MulAut P) (x : P) :
      descend alpha (QuotientGroup.mk' (Subgroup.center P) x) =
        QuotientGroup.mk' (Subgroup.center P) (alpha x) := by
    rfl
  have hdescend_inv_left (alpha : MulAut P) :
      Function.LeftInverse (descend alpha.symm) (descend alpha) := by
    intro q
    refine QuotientGroup.induction_on q ?_
    intro x
    change QuotientGroup.mk' (Subgroup.center P) (alpha.symm (alpha x)) =
      QuotientGroup.mk' (Subgroup.center P) x
    rw [alpha.symm_apply_apply]
  have hdescend_inv_right (alpha : MulAut P) :
      Function.RightInverse (descend alpha.symm) (descend alpha) :=
    hdescend_inv_left alpha.symm
  let descendAut (alpha : MulAut P) : MulAut (P ⧸ Subgroup.center P) :=
    { toFun := descend alpha
      invFun := descend alpha.symm
      left_inv := hdescend_inv_left alpha
      right_inv := hdescend_inv_right alpha
      map_mul' := (descend alpha).map_mul }
  refine
    { toFun := descendAut
      map_one' := ?_
      map_mul' := ?_ }
  · apply DFunLike.ext _ _
    intro q
    refine QuotientGroup.induction_on q ?_
    intro x
    rfl
  · intro alpha beta
    apply DFunLike.ext _ _
    intro q
    refine QuotientGroup.induction_on q ?_
    intro x
    rfl

set_option maxHeartbeats 400000 in
private theorem actualK_action_on_S
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K S : Subgroup G) (t s : G)
    (hA : HypothesisA G Ω H D Q t)
    (hKleD : K ≤ D)
    (hKdef : ∀ x : G, x ∈ K ↔
      x ∈ D ∧ rightConjugateElem x t = x⁻¹)
    (hsH : s ∈ H) (hsInv : IsInvolution s)
    (hsStruct : ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r)
    (hSQ : S = Q) :
    ∃ hKnormS : K ≤ Subgroup.normalizer (S : Set G),
      letI : Subgroup.Normalizes K S := ⟨hKnormS⟩
      FaithfulSMul K S ∧ ActionRegularOn K S (involutions S) := by
  classical
  have hD_faithful_on_S :
      D ⊓ Subgroup.centralizer (S : Set G) = ⊥ := by
    have hcore := (PFchapter1section1.proposition_4_c H D Q t s
      hA.A1 hsH hsInv hsStruct).1
    rw [← hSQ] at hcore
    rw [← hcore, eq_bot_iff]
    intro x hxCore
    have hfix : ∀ omega : Ω, x • omega = omega := by
      have hxAll : ∀ point : Ω, x ∈ MulAction.stabilizer G point := by
        simpa [pointStabilizerCore] using hxCore
      intro omega
      exact MulAction.mem_stabilizer_iff.mp (hxAll omega)
    have hxOne : x = 1 := (faithfulSMul_iff.mp hA.A2) x hfix
    simp [hxOne]
  letI : (Q.subgroupOf H).Normal := hA.A1.Q_normal_in_H
  have hHnormQ : H ≤ Subgroup.normalizer (Q : Set G) :=
    Subgroup.le_normalizer_of_normal_subgroupOf hA.A1.Q_le_H
  have hDnormS : D ≤ Subgroup.normalizer (S : Set G) := by
    rw [hSQ]
    exact hA.A1.D_le_H.trans hHnormQ
  have hKnormS : K ≤ Subgroup.normalizer (S : Set G) := hKleD.trans hDnormS
  letI : Subgroup.Normalizes K S := ⟨hKnormS⟩
  have hKfaithful : FaithfulSMul K S := by
    rw [faithfulSMul_iff]
    intro k hkfix
    have hkCentralizer : (k : G) ∈ Subgroup.centralizer (S : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hxS
      let xS : S := ⟨x, hxS⟩
      have hfix := hkfix xS
      have hconj : (k : G) * x * (k : G)⁻¹ = x := by
        simpa [xS,
          Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
            congrArg (fun z : S => (z : G)) hfix
      have hmul := congrArg (fun z : G => z * (k : G)) hconj
      simpa [mul_assoc] using hmul.symm
    have hkBot : (k : G) ∈ (⊥ : Subgroup G) := by
      rw [← hD_faithful_on_S]
      exact ⟨hKleD k.property, hkCentralizer⟩
    apply Subtype.ext
    simpa using hkBot
  have hrightConjugateInjective :
      ∀ (x : S) (hx : IsInvolution x),
        Function.Injective
          (fun k : {a : G // a ∈ peterfalviKSet D t} =>
            (⟨rightConjugateElem (x : G) (k : G),
              ((PFchapter1section1.proposition_3 H D Q t hA.A1).2
                (x : G) (hA.A1.Q_le_H (by rw [← hSQ]; exact x.property))
                ⟨(by intro hxOne; exact hx.ne_one (Subtype.ext hxOne)),
                  congrArg (fun z : S => (z : G)) hx.sq_eq_one⟩
                (rightConjugateElem (x : G) (k : G))).2
                  ⟨k, k.property, rfl⟩⟩ :
              {y : G // y ∈ H ∧ IsInvolution y})) := by
    intro x hx
    let KSet : Type _ := {a : G // a ∈ peterfalviKSet D t}
    let HInv : Type _ := {y : G // y ∈ H ∧ IsInvolution y}
    have hxG : IsInvolution (x : G) :=
      ⟨fun hxOne => hx.ne_one (Subtype.ext hxOne),
        congrArg (fun z : S => (z : G)) hx.sq_eq_one⟩
    have hxH : (x : G) ∈ H :=
      hA.A1.Q_le_H (by rw [← hSQ]; exact x.property)
    let psi : KSet → HInv := fun k =>
      ⟨rightConjugateElem (x : G) (k : G),
        ((PFchapter1section1.proposition_3 H D Q t hA.A1).2
          (x : G) hxH hxG (rightConjugateElem (x : G) (k : G))).2
            ⟨k, k.property, rfl⟩⟩
    have hpsiSurjective : Function.Surjective psi := by
      rintro ⟨y, hy⟩
      rcases ((PFchapter1section1.proposition_3 H D Q t hA.A1).2
          (x : G) hxH hxG y).1 hy with ⟨k, hk, hkEq⟩
      refine ⟨⟨k, hk⟩, ?_⟩
      apply Subtype.ext
      exact hkEq
    have hpsiInjective : Function.Injective psi :=
      (hpsiSurjective.bijective_of_nat_card_le
        (by simpa [KSet, HInv] using
          le_of_eq (PFchapter1section1.proposition_3 H D Q t hA.A1).1)).1
    simpa [psi, KSet, HInv, hxG, hxH] using hpsiInjective
  have hKregular : ActionRegularOn K S (involutions S) := by
    constructor
    · intro x hx k
      have hxG : IsInvolution (x : G) :=
        ⟨fun hxOne => hx.ne_one (Subtype.ext hxOne),
          congrArg (fun z : S => (z : G)) hx.sq_eq_one⟩
      have hconj := isInvolution_rightConjugateElem
        (g := ((k⁻¹ : K) : G)) hxG
      constructor
      · intro hOne
        apply hconj.ne_one
        simpa [rightConjugateElem,
          Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
            congrArg (fun z : S => (z : G)) hOne
      · apply Subtype.ext
        simpa [rightConjugateElem,
          Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
            hconj.sq_eq_one
    · intro x hx y hy
      have hxG : IsInvolution (x : G) :=
        ⟨fun hxOne => hx.ne_one (Subtype.ext hxOne),
          congrArg (fun z : S => (z : G)) hx.sq_eq_one⟩
      have hyG : IsInvolution (y : G) :=
        ⟨fun hyOne => hy.ne_one (Subtype.ext hyOne),
          congrArg (fun z : S => (z : G)) hy.sq_eq_one⟩
      have hxH : (x : G) ∈ H := hA.A1.Q_le_H (by rw [← hSQ]; exact x.property)
      have hyH : (y : G) ∈ H := hA.A1.Q_le_H (by rw [← hSQ]; exact y.property)
      rcases ((PFchapter1section1.proposition_3 H D Q t hA.A1).2
          (x : G) hxH hxG (y : G)).1 ⟨hyH, hyG⟩ with ⟨a, haSet, haEq⟩
      have haK : a ∈ K := (hKdef a).mpr haSet
      let k : K := ⟨a⁻¹, K.inv_mem haK⟩
      refine ⟨k, ?_, ?_⟩
      · apply Subtype.ext
        simpa [k, rightConjugateElem,
          Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using haEq.symm
      · intro b hb
        let aSet : {z : G // z ∈ peterfalviKSet D t} := ⟨a, haSet⟩
        let bSet : {z : G // z ∈ peterfalviKSet D t} :=
          ⟨((b⁻¹ : K) : G), (hKdef ((b⁻¹ : K) : G)).mp (b⁻¹ : K).property⟩
        have hbRight : rightConjugateElem (x : G) (bSet : G) = (y : G) := by
          have hbVal := congrArg (fun z : S => (z : G)) hb
          simpa [bSet, rightConjugateElem,
            Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using hbVal.symm
        have hba : bSet = aSet :=
          hrightConjugateInjective x hx
            (by apply Subtype.ext; exact hbRight.trans haEq.symm)
        apply Subtype.ext
        change (b : G) = a⁻¹
        have hval : ((b⁻¹ : K) : G) = a := congrArg Subtype.val hba
        simpa using congrArg Inv.inv hval
  exact ⟨hKnormS, hKfaithful, hKregular⟩

private theorem linearMap_eq_mulLeft_of_commutes_fin_two
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (alpha : E) (b : Module.Basis (Fin 2) F E)
    (hbZero : b 0 = alpha) (hbOne : b 1 = 1)
    (T : E →ₗ[F] E) (hTalpha : T alpha = alpha * T 1) :
    ∀ x : E, T x = T 1 * x := by
  have hmaps : T = LinearMap.mulLeft F (T 1) := by
    apply Module.Basis.ext b
    intro i
    by_cases hi : i = 0
    · subst i
      rw [hbZero]
      change T alpha = T 1 * alpha
      simpa [mul_comm] using hTalpha
    · have hiOne : i = 1 := Fin.eq_one_of_ne_zero i hi
      subst i
      rw [hbOne]
      change T 1 = T 1 * 1
      rw [mul_one]
  exact fun x => LinearMap.congr_fun hmaps x

private theorem quadraticMap_of_multiplicative_polar
    {V W : Type*}
    [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    (q : Multiplicative V → Multiplicative W)
    (hqOne : q 1 = 1)
    (hpolarLeft : ∀ x₁ x₂ y : Multiplicative V,
      q ((x₁ * x₂) * y) * (q (x₁ * x₂))⁻¹ * (q y)⁻¹ =
        (q (x₁ * y) * (q x₁)⁻¹ * (q y)⁻¹) *
          (q (x₂ * y) * (q x₂)⁻¹ * (q y)⁻¹)) :
    ∃ Q : QuadraticMap (ZMod 2) V W,
      ∀ x : V, Q x = (q (Multiplicative.ofAdd x)).toAdd := by
  let f : V → W := fun x => (q (Multiplicative.ofAdd x)).toAdd
  have hfZero : f 0 = 0 := by
    change (q (Multiplicative.ofAdd 0)).toAdd = 0
    simpa using congrArg Multiplicative.toAdd hqOne
  have hfSmul (a : ZMod 2) (x : V) :
      f (a • x) = (a * a) • f x := by
    have ha : a = 0 ∨ a = 1 := by
      fin_cases a
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases ha with rfl | rfl
    · simp [hfZero]
    · simp
  have hpolarAdd (x x' y : V) :
      QuadraticMap.polar f (x + x') y =
        QuadraticMap.polar f x y + QuadraticMap.polar f x' y := by
    have h := congrArg Multiplicative.toAdd
      (hpolarLeft (Multiplicative.ofAdd x)
        (Multiplicative.ofAdd x') (Multiplicative.ofAdd y))
    simpa [f, QuadraticMap.polar, sub_eq_add_neg, mul_assoc, add_assoc] using h
  have hpolarSmul (a : ZMod 2) (x y : V) :
      QuadraticMap.polar f (a • x) y =
        a • QuadraticMap.polar f x y := by
    have ha : a = 0 ∨ a = 1 := by
      fin_cases a
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases ha with rfl | rfl
    · simp [QuadraticMap.polar, hfZero]
    · simp
  let Q : QuadraticMap (ZMod 2) V W :=
    QuadraticMap.ofPolar f hfSmul hpolarAdd hpolarSmul
  exact ⟨Q, fun x => rfl⟩

set_option maxHeartbeats 800000 in
private theorem cyclic_irreducible_plane_field_model
    {F W : Type*} [Field F] [Finite F] [CharP F 2] [Group W]
    (rho : W →* LinearMap.GeneralLinearGroup F (F × F))
    (w0 : W) (hcomm : ∀ a : W, a * w0 = w0 * a)
    (hnoEigen : ∀ v : F × F, v ≠ 0 → ∀ a : F, (rho w0).1 v ≠ a • v)
    (hrho : Function.Injective rho) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E) (_ : Algebra F E)
        (H : E ≃ₗ[F] F × F) (u : W →* Eˣ),
      Module.finrank F E = 2 ∧ Function.Injective u ∧
        ∀ w : W, ∀ x : E, H ((u w : E) * x) = (rho w).1 (H x) := by
  classical
  let pairFin : (Fin 2 → F) ≃ₗ[F] F × F := LinearEquiv.finTwoArrow F F
  let rhoFin : W →* LinearMap.GeneralLinearGroup F (Fin 2 → F) :=
    (LinearMap.GeneralLinearGroup.congrLinearEquiv pairFin.symm).toMonoidHom.comp rho
  let M : Matrix (Fin 2) (Fin 2) F :=
    LinearMap.toMatrix' (rhoFin w0).1
  have hM_apply (x : Fin 2 → F) : M.mulVec x = (rhoFin w0).1 x := by
    simp [M, LinearMap.toMatrix'_mulVec]
  let chi : Polynomial F := M.charpoly
  have hchiDeg : chi.natDegree = 2 := by
    simp [chi, M, Matrix.charpoly_natDegree_eq_dim]
  have hchiNe : chi ≠ 0 := (Matrix.charpoly_monic M).ne_zero
  have hnoRoot (mu : F) : ¬ chi.IsRoot mu := by
    intro hroot
    have hdetZero : (Matrix.scalar (Fin 2) mu - M).det = 0 := by
      rw [← Matrix.eval_charpoly]
      exact hroot
    obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdetZero
    have hscalar : (Matrix.scalar (Fin 2) mu).mulVec v = mu • v := by
      ext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct]
    rw [Matrix.sub_mulVec, hscalar, sub_eq_zero] at hMv
    let vPair : F × F := pairFin v
    have hvPair : vPair ≠ 0 := by
      intro hv0
      apply hv
      apply pairFin.injective
      simpa [vPair] using hv0
    apply hnoEigen vPair hvPair mu
    change (rho w0).1 (pairFin v) = mu • pairFin v
    have hfin : (rhoFin w0).1 v = mu • v := by
      rw [← hM_apply]
      exact hMv.symm
    simpa [rhoFin, pairFin] using congrArg pairFin hfin
  have hchiRoots : chi.roots = 0 := by
    apply Multiset.eq_zero_of_forall_notMem
    intro mu hmu
    exact hnoRoot mu ((Polynomial.mem_roots hchiNe).mp hmu)
  have hchiIrreducible : Irreducible chi := by
    apply ((Matrix.charpoly_monic M).irreducible_iff_roots_eq_zero_of_degree_le_three
      (by rw [hchiDeg]) (by rw [hchiDeg]; norm_num)).mpr
    exact hchiRoots
  haveI : Fact (Irreducible chi) := ⟨hchiIrreducible⟩
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : NeZero 2 := ⟨by norm_num⟩
  letI : Algebra F (AdjoinRoot chi) := AdjoinRoot.instAlgebra chi
  letI : Module F (AdjoinRoot chi) := Algebra.toModule
  have hfinrankRoot : Module.finrank F (AdjoinRoot chi) = 2 := by
    calc
      Module.finrank F (AdjoinRoot chi) =
          (AdjoinRoot.powerBasis hchiNe).dim :=
        (AdjoinRoot.powerBasis hchiNe).finrank
      _ = chi.natDegree := AdjoinRoot.powerBasis_dim hchiNe
      _ = 2 := hchiDeg
  let E := FiniteField.Extension F 2 2
  let eRoot : AdjoinRoot chi ≃ₐ[F] E :=
    FiniteField.algEquivExtension F 2 2 (AdjoinRoot chi) hfinrankRoot
  let alpha : E := eRoot (AdjoinRoot.root chi)
  have halphaRoot : (chi.map (algebraMap F E)).IsRoot alpha := by
    have hroot := AdjoinRoot.isRoot_root chi
    have hrootE :
        ((chi.map (AdjoinRoot.of chi)).map eRoot.toRingEquiv.toRingHom).IsRoot
          (eRoot (AdjoinRoot.root chi)) := hroot.map
    rw [Polynomial.map_map] at hrootE
    convert hrootE using 1
    congr 1
    ext r
    simp [eRoot]
  have halphaNotScalar (r : F) : algebraMap F E r ≠ alpha := by
    intro hr
    apply hnoRoot r
    apply (Polynomial.isRoot_map_iff (algebraMap F E).injective).mp
    rw [hr]
    exact halphaRoot
  have halphaPoly :
      alpha ^ 2 - algebraMap F E (Matrix.trace M) * alpha +
          algebraMap F E M.det = 0 := by
    have h := halphaRoot
    simpa [Polynomial.IsRoot, chi, Matrix.charpoly_fin_two] using h
  have halphaSq :
      alpha * alpha = algebraMap F E (Matrix.trace M) * alpha -
        algebraMap F E M.det := by
    rw [pow_two] at halphaPoly
    linear_combination halphaPoly
  let alphaFamily : Fin 2 → E := ![alpha, 1]
  have halphaLI : LinearIndependent F alphaFamily := by
    rw [linearIndependent_fin2]
    refine ⟨one_ne_zero, ?_⟩
    intro r hr
    exact halphaNotScalar r (by
      simpa [alphaFamily, Algebra.smul_def] using hr)
  have hfinrankE : Module.finrank F E = 2 := by
    simpa [E] using FiniteField.finrank_extension F 2 2
  let bAlpha : Module.Basis (Fin 2) F E :=
    basisOfLinearIndependentOfCardEqFinrank halphaLI (by simp [hfinrankE])
  let v : Fin 2 → F := ![1, 0]
  let wv : Fin 2 → F := M.mulVec v
  have hv : v ≠ 0 := by
    intro hv0
    have := congrFun hv0 0
    simp [v] at this
  let actionFamily : Fin 2 → (Fin 2 → F) := ![wv, v]
  have hactionLI : LinearIndependent F actionFamily := by
    rw [linearIndependent_fin2]
    refine ⟨hv, ?_⟩
    intro mu hmu
    let vPair : F × F := pairFin v
    have hvPair : vPair ≠ 0 := by
      intro hv0
      apply hv
      apply pairFin.injective
      simpa [vPair] using hv0
    apply hnoEigen vPair hvPair mu
    change (rho w0).1 (pairFin v) = mu • pairFin v
    have hfin : (rhoFin w0).1 v = mu • v := by
      rw [← hM_apply]
      simpa [actionFamily, wv] using hmu.symm
    simpa [rhoFin, pairFin] using congrArg pairFin hfin
  let bAction : Module.Basis (Fin 2) F (Fin 2 → F) :=
    basisOfLinearIndependentOfCardEqFinrank hactionLI (by simp)
  have hbAlphaZero : bAlpha 0 = alpha := by simp [bAlpha, alphaFamily]
  have hbAlphaOne : bAlpha 1 = 1 := by simp [bAlpha, alphaFamily]
  have hbActionZero : bAction 0 = wv := by simp [bAction, actionFamily]
  have hbActionOne : bAction 1 = v := by simp [bAction, actionFamily]
  let Hfin : E ≃ₗ[F] (Fin 2 → F) :=
    bAlpha.equiv bAction (Equiv.refl (Fin 2))
  have hHfinBasis (i : Fin 2) : Hfin (bAlpha i) = bAction i := by simp [Hfin]
  have hHfinAlpha : Hfin alpha = wv := by
    rw [← hbAlphaZero, hHfinBasis, hbActionZero]
  have hHfinOne : Hfin 1 = v := by
    rw [← hbAlphaOne, hHfinBasis, hbActionOne]
  have hdetCoord : M 0 0 * M 1 1 - M 0 1 * M 1 0 = M.det := by
    simp [Matrix.det_fin_two]
  have hMwv :
      M.mulVec wv = Matrix.trace M • wv - M.det • v := by
    ext i
    fin_cases i
    · simp [wv, v, Matrix.mulVec, dotProduct, Matrix.trace_fin_two]
      linear_combination -hdetCoord
    · simp [wv, v, Matrix.mulVec, dotProduct, Matrix.trace_fin_two]
      ring
  have hHfinIntertwines :
      Hfin.toLinearMap.comp (Algebra.lmul F E alpha) =
        M.mulVecLin.comp Hfin.toLinearMap := by
    apply Module.Basis.ext bAlpha
    intro i
    fin_cases i
    · change Hfin (alpha * bAlpha 0) = M.mulVec (Hfin (bAlpha 0))
      rw [hbAlphaZero, hHfinAlpha]
      calc
        Hfin (alpha * alpha) = Hfin
            (algebraMap F E (Matrix.trace M) * alpha - algebraMap F E M.det) :=
          congrArg Hfin halphaSq
        _ = Matrix.trace M • Hfin alpha - M.det • Hfin 1 := by
          rw [show algebraMap F E (Matrix.trace M) * alpha =
              Matrix.trace M • alpha by rfl,
            show algebraMap F E M.det = M.det • (1 : E) by
              simp [Algebra.smul_def],
            map_sub, map_smul, map_smul]
        _ = Matrix.trace M • wv - M.det • v := by
          rw [hHfinAlpha, hHfinOne]
        _ = M.mulVec wv := hMwv.symm
    · change Hfin (alpha * bAlpha 1) = M.mulVec (Hfin (bAlpha 1))
      rw [hbAlphaOne, mul_one, hHfinAlpha, hHfinOne]
  let H : E ≃ₗ[F] F × F := Hfin.trans pairFin
  have hHAlpha (x : E) : H (alpha * x) = (rho w0).1 (H x) := by
    change pairFin (Hfin (alpha * x)) = (rho w0).1 (pairFin (Hfin x))
    have hlin := LinearMap.congr_fun hHfinIntertwines x
    change Hfin (alpha * x) = M.mulVec (Hfin x) at hlin
    rw [hM_apply] at hlin
    simpa [rhoFin, pairFin] using congrArg pairFin hlin
  let tau : W →* LinearMap.GeneralLinearGroup F E :=
    (LinearMap.GeneralLinearGroup.congrLinearEquiv H).symm.toMonoidHom.comp rho
  have htauApply (a : W) (x : E) : H ((tau a).1 x) = (rho a).1 (H x) := by
    change H (H.symm ((rho a).1 (H x))) = (rho a).1 (H x)
    simp
  have htauW0 (x : E) : (tau w0).1 x = alpha * x := by
    apply H.injective
    rw [htauApply, hHAlpha]
  have htauComm (a : W) : tau a * tau w0 = tau w0 * tau a := by
    rw [← map_mul, ← map_mul, hcomm]
  have htauScalar (a : W) (x : E) : (tau a).1 x = (tau a).1 1 * x := by
    have hcommMaps := congrArg
      (fun g : LinearMap.GeneralLinearGroup F E => g.1) (htauComm a)
    have hcommOne := LinearMap.congr_fun hcommMaps 1
    change (tau a).1 ((tau w0).1 1) =
      (tau w0).1 ((tau a).1 1) at hcommOne
    rw [htauW0, htauW0, mul_one] at hcommOne
    exact linearMap_eq_mulLeft_of_commutes_fin_two alpha bAlpha
      hbAlphaZero hbAlphaOne (tau a).1 hcommOne x
  let scalarHom : W →* E :=
    { toFun := fun a => (tau a).1 1
      map_one' := by simp [tau]
      map_mul' := by
        intro a b
        change (tau (a * b)).1 1 = (tau a).1 1 * (tau b).1 1
        rw [map_mul]
        change (tau a).1 ((tau b).1 1) = (tau a).1 1 * (tau b).1 1
        exact htauScalar a ((tau b).1 1) }
  let u : W →* Eˣ := MonoidHom.toHomUnits (G := W) (M := E) scalarHom
  have hcompat (a : W) (x : E) : H ((u a : E) * x) = (rho a).1 (H x) := by
    have hu : (u a : E) = (tau a).1 1 := rfl
    rw [hu, ← htauScalar a x, htauApply]
  have huInjective : Function.Injective u := by
    intro a b hab
    apply hrho
    apply Units.ext
    apply LinearMap.ext
    intro y
    let x : E := H.symm y
    have hval : (u a : E) = (u b : E) := congrArg Units.val hab
    calc
      (rho a).1 y = H ((u a : E) * x) := by
        rw [hcompat]
        simp [x]
      _ = H ((u b : E) * x) := by rw [hval]
      _ = (rho b).1 y := by
        rw [hcompat]
        simp [x]
  exact ⟨E, inferInstance, inferInstance, inferInstance, H, u,
    hfinrankE, huInjective, hcompat⟩

private theorem typeB_group_model :
    ∀ (E : Type) [Field E] [Finite E] [CharP E 2]
      (F : Subfield E) (theta : F ≃+* F) (sigma : E ≃+* E)
      (phi : E → E → E) (K1 W1 : Subgroup Eˣ),
      (theta = 1 → Function.Involutive sigma) →
      (theta = 1 → ∀ x y : E, phi x y = x * sigma y) →
      (∀ x y z : E, phi (x + y) z = phi x z + phi y z) →
      (∀ x y z : E, phi x (y + z) = phi x y + phi x z) →
      (theta ≠ 1 → ∀ x y : E, phi x y ∈ F) →
      (∀ a : (K1 ⊔ W1 : Subgroup Eˣ), theta ≠ 1 →
        ((a : Eˣ) : E) * sigma ((a : Eˣ) : E) ∈ F) →
      (∀ a : (K1 ⊔ W1 : Subgroup Eˣ), ∀ x y : E,
        phi (((a : Eˣ) : E) * x) (((a : Eˣ) : E) * y) =
          ((a : Eˣ) : E) * sigma ((a : Eˣ) : E) * phi x y) →
      ∃ (S1 : Type) (_ : Group S1)
        (coord : S1 ≃
          {p : E × E //
            (theta = 1 ∧ p.2 + sigma p.2 = p.1 * sigma p.1) ∨
              (theta ≠ 1 ∧ p.2 ∈ F)})
        (rho1 : (K1 ⊔ W1 : Subgroup Eˣ) →* MulAut S1),
        (∀ x y : S1,
          ((coord (x * y)).1 : E × E) =
            ((coord x).1.1 + (coord y).1.1,
              (coord x).1.2 + (coord y).1.2 +
                phi (coord x).1.1 (coord y).1.1)) ∧
        (∀ a : (K1 ⊔ W1 : Subgroup Eˣ), ∀ x : S1,
          ((coord (rho1 a⁻¹ x)).1 : E × E) =
            (((a : Eˣ) : E) * (coord x).1.1,
              ((a : Eˣ) : E) * sigma ((a : Eˣ) : E) *
                (coord x).1.2)) := by
  intro E _ _ _ F theta sigma phi K1 W1 hsigmaInv hphiOne
    hphiAddLeft hphiAddRight hphiMem hnormMem hphiScale
  classical
  let Carrier :=
    {p : E × E //
      (theta = 1 ∧ p.2 + sigma p.2 = p.1 * sigma p.1) ∨
        (theta ≠ 1 ∧ p.2 ∈ F)}
  have hphiZeroLeft (z : E) : phi 0 z = 0 := by
    have h := hphiAddLeft 0 0 z
    have h' := congrArg (fun u : E => u - phi 0 z) h
    simpa using h'.symm
  have hphiZeroRight (z : E) : phi z 0 = 0 := by
    have h := hphiAddRight z 0 0
    have h' := congrArg (fun u : E => u - phi z 0) h
    simpa using h'.symm
  have hmul_mem (p q : Carrier) :
      ((p.1.1 + q.1.1,
        p.1.2 + q.1.2 + phi p.1.1 q.1.1) : E × E) ∈
        {r : E × E |
          (theta = 1 ∧ r.2 + sigma r.2 = r.1 * sigma r.1) ∨
            (theta ≠ 1 ∧ r.2 ∈ F)} := by
    by_cases htheta : theta = 1
    · refine Or.inl ⟨htheta, ?_⟩
      have hp := p.property.resolve_right (fun hp => hp.1 htheta)
      have hq := q.property.resolve_right (fun hq => hq.1 htheta)
      have hphi := hphiOne htheta p.1.1 q.1.1
      have hsigmaPhi :
          sigma (phi p.1.1 q.1.1) = sigma p.1.1 * q.1.1 := by
        rw [hphi, map_mul, hsigmaInv htheta q.1.1]
      change
        (p.1.2 + q.1.2 + phi p.1.1 q.1.1) +
            sigma (p.1.2 + q.1.2 + phi p.1.1 q.1.1) =
          (p.1.1 + q.1.1) * sigma (p.1.1 + q.1.1)
      rw [map_add, map_add, hsigmaPhi, hphi, map_add]
      linear_combination hp.2 + hq.2
    · refine Or.inr ⟨htheta, ?_⟩
      have hp := p.property.resolve_left (fun hp => htheta hp.1)
      have hq := q.property.resolve_left (fun hq => htheta hq.1)
      exact F.add_mem (F.add_mem hp.2 hq.2)
        (hphiMem htheta p.1.1 q.1.1)
  let mulCarrier : Carrier → Carrier → Carrier := fun p q =>
    ⟨(p.1.1 + q.1.1,
      p.1.2 + q.1.2 + phi p.1.1 q.1.1), hmul_mem p q⟩
  have hone_mem :
      ((0, 0) : E × E) ∈
        {r : E × E |
          (theta = 1 ∧ r.2 + sigma r.2 = r.1 * sigma r.1) ∨
            (theta ≠ 1 ∧ r.2 ∈ F)} := by
    by_cases htheta : theta = 1
    · exact Or.inl ⟨htheta, by simp⟩
    · exact Or.inr ⟨htheta, F.zero_mem⟩
  let oneCarrier : Carrier := ⟨(0, 0), hone_mem⟩
  letI : Mul Carrier := ⟨mulCarrier⟩
  letI : One Carrier := ⟨oneCarrier⟩
  have hmul_assoc (a b c : Carrier) : a * b * c = a * (b * c) := by
    apply Subtype.ext
    apply Prod.ext
    · change (a.1.1 + b.1.1) + c.1.1 = a.1.1 + (b.1.1 + c.1.1)
      ring
    · change
        (a.1.2 + b.1.2 + phi a.1.1 b.1.1) + c.1.2 +
            phi (a.1.1 + b.1.1) c.1.1 =
          a.1.2 + (b.1.2 + c.1.2 + phi b.1.1 c.1.1) +
            phi a.1.1 (b.1.1 + c.1.1)
      rw [hphiAddLeft, hphiAddRight]
      ring
  have hone_mul (a : Carrier) : 1 * a = a := by
    apply Subtype.ext
    apply Prod.ext
    · change 0 + a.1.1 = a.1.1
      simp
    · change 0 + a.1.2 + phi 0 a.1.1 = a.1.2
      simp [hphiZeroLeft]
  have hmul_one (a : Carrier) : a * 1 = a := by
    apply Subtype.ext
    apply Prod.ext
    · change a.1.1 + 0 = a.1.1
      simp
    · change a.1.2 + 0 + phi a.1.1 0 = a.1.2
      simp [hphiZeroRight]
  have hmul_left_cancel (a b c : Carrier) (h : a * b = a * c) : b = c := by
    have hv := congrArg (fun z : Carrier => (z.1 : E × E)) h
    have hfirst : b.1.1 = c.1.1 :=
      (IsLeftCancelAdd.add_left_cancel (a.1.1)) (by
        have h := congrArg Prod.fst hv
        dsimp [Mul.mul, mulCarrier] at h
        exact h)
    apply Subtype.ext
    apply Prod.ext
    · exact hfirst
    · have hsecond := congrArg Prod.snd hv
      change a.1.2 + b.1.2 + phi a.1.1 b.1.1 =
        a.1.2 + c.1.2 + phi a.1.1 c.1.1 at hsecond
      rw [hfirst] at hsecond
      linear_combination hsecond
  letI : LeftCancelMonoid Carrier :=
    { mul_assoc := hmul_assoc
      one_mul := hone_mul
      mul_one := hmul_one
      mul_left_cancel := hmul_left_cancel }
  let groupCarrier : Group Carrier := LeftCancelMonoid.groupOfFinite
  letI : Group Carrier := groupCarrier
  let coord : Carrier ≃ Carrier := Equiv.refl Carrier
  let Actor := (K1 ⊔ W1 : Subgroup Eˣ)
  have hscale_mem (a : Actor) (p : Carrier) :
      ((((a : Eˣ) : E) * p.1.1,
        ((a : Eˣ) : E) * sigma ((a : Eˣ) : E) * p.1.2) : E × E) ∈
        {r : E × E |
          (theta = 1 ∧ r.2 + sigma r.2 = r.1 * sigma r.1) ∨
            (theta ≠ 1 ∧ r.2 ∈ F)} := by
    by_cases htheta : theta = 1
    · refine Or.inl ⟨htheta, ?_⟩
      have hp := p.property.resolve_right (fun hp => hp.1 htheta)
      have hsigmaNorm :
          sigma (((a : Eˣ) : E) * sigma ((a : Eˣ) : E)) =
            ((a : Eˣ) : E) * sigma ((a : Eˣ) : E) := by
        rw [map_mul, hsigmaInv htheta]
        exact mul_comm _ _
      change
        (((a : Eˣ) : E) * sigma ((a : Eˣ) : E) * p.1.2) +
            sigma (((a : Eˣ) : E) * sigma ((a : Eˣ) : E) * p.1.2) =
          (((a : Eˣ) : E) * p.1.1) *
            sigma (((a : Eˣ) : E) * p.1.1)
      rw [map_mul, hsigmaNorm, map_mul]
      linear_combination
        (((a : Eˣ) : E) * sigma ((a : Eˣ) : E)) * hp.2
    · refine Or.inr ⟨htheta, ?_⟩
      have hp := p.property.resolve_left (fun hp => htheta hp.1)
      exact F.mul_mem (hnormMem a htheta) hp.2
  let scale (a : Actor) (p : Carrier) : Carrier :=
    ⟨(((a : Eˣ) : E) * p.1.1,
      ((a : Eˣ) : E) * sigma ((a : Eˣ) : E) * p.1.2),
      hscale_mem a p⟩
  have hscale_one (a : Actor) : scale a 1 = 1 := by
    apply Subtype.ext
    apply Prod.ext
    · change ((a : Eˣ) : E) * 0 = 0
      simp
    · change ((a : Eˣ) : E) * sigma ((a : Eˣ) : E) * 0 = 0
      simp
  have hscale_mul (a : Actor) (x y : Carrier) :
      scale a (x * y) = scale a x * scale a y := by
    apply Subtype.ext
    apply Prod.ext
    · change ((a : Eˣ) : E) * (x.1.1 + y.1.1) =
        ((a : Eˣ) : E) * x.1.1 + ((a : Eˣ) : E) * y.1.1
      ring
    · change
        ((a : Eˣ) : E) * sigma ((a : Eˣ) : E) *
            (x.1.2 + y.1.2 + phi x.1.1 y.1.1) =
          (((a : Eˣ) : E) * sigma ((a : Eˣ) : E) * x.1.2 +
              ((a : Eˣ) : E) * sigma ((a : Eˣ) : E) * y.1.2) +
            phi (((a : Eˣ) : E) * x.1.1)
              (((a : Eˣ) : E) * y.1.1)
      rw [hphiScale]
      ring
  let scaleHom (a : Actor) : Carrier →* Carrier :=
    { toFun := scale a
      map_one' := hscale_one a
      map_mul' := hscale_mul a }
  have hscale_inv_left (a : Actor) (x : Carrier) :
      scale a⁻¹ (scale a x) = x := by
    apply Subtype.ext
    apply Prod.ext
    · change (((a⁻¹ : Actor) : Eˣ) : E) * (((a : Eˣ) : E) * x.1.1) = x.1.1
      simp
    · change
        (((a⁻¹ : Actor) : Eˣ) : E) * sigma (((a⁻¹ : Actor) : Eˣ) : E) *
            (((a : Eˣ) : E) * sigma ((a : Eˣ) : E) * x.1.2) = x.1.2
      rw [Subgroup.coe_inv, Units.val_inv_eq_inv_val, map_inv₀]
      field_simp
  have hscale_inv_right (a : Actor) (x : Carrier) :
      scale a (scale a⁻¹ x) = x := by
    simpa using hscale_inv_left a⁻¹ x
  let scaleAut (a : Actor) : MulAut Carrier :=
    { toFun := scale a
      invFun := scale a⁻¹
      left_inv := hscale_inv_left a
      right_inv := hscale_inv_right a
      map_mul' := hscale_mul a }
  have hscaleAut_mul (a b : Actor) :
      scaleAut (a * b) = scaleAut a * scaleAut b := by
    apply DFunLike.ext _ _
    intro x
    apply Subtype.ext
    apply Prod.ext
    · change ((((a * b : Actor) : Eˣ) : E) * x.1.1) =
        ((a : Eˣ) : E) * (((b : Eˣ) : E) * x.1.1)
      simp [mul_assoc]
    · change
        ((((a * b : Actor) : Eˣ) : E) *
            sigma (((a * b : Actor) : Eˣ) : E) * x.1.2) =
          ((a : Eˣ) : E) * sigma ((a : Eˣ) : E) *
            (((b : Eˣ) : E) * sigma ((b : Eˣ) : E) * x.1.2)
      simp only [Subgroup.coe_mul, Units.val_mul, map_mul]
      ring
  have hscaleAut_one : scaleAut (1 : Actor) = 1 := by
    apply DFunLike.ext _ _
    intro x
    apply Subtype.ext
    apply Prod.ext
    · change (1 : E) * x.1.1 = x.1.1
      simp
    · change (1 : E) * sigma (1 : E) * x.1.2 = x.1.2
      simp
  let rho1 : Actor →* MulAut Carrier :=
    { toFun := fun a => scaleAut a⁻¹
      map_one' := by simpa using hscaleAut_one
      map_mul' := by
        intro a b
        rw [mul_inv_rev]
        calc
          scaleAut (b⁻¹ * a⁻¹) = scaleAut (a⁻¹ * b⁻¹) := by rw [mul_comm]
          _ = scaleAut a⁻¹ * scaleAut b⁻¹ := hscaleAut_mul a⁻¹ b⁻¹ }
  refine ⟨Carrier, groupCarrier, coord, rho1, ?_, ?_⟩
  · intro x y
    rfl
  · intro a x
    change ((rho1 a⁻¹ x).1 : E × E) = _
    simp only [rho1, MonoidHom.coe_mk, OneHom.coe_mk, inv_inv]
    rfl

private theorem align_odd_actions_on_binary_central_extension
    {A V W P : Type*}
    [Group A] [Finite A]
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    [Group P]
    (iota : Multiplicative W →* P)
    (pi : P →* Multiplicative V)
    (hiota : Function.Injective iota)
    (hpi : Function.Surjective pi)
    (hexact : iota.range = pi.ker)
    (hcentral : iota.range ≤ Subgroup.center P)
    (rhoT rhoM : A →* MulAut P)
    (hAodd : Odd (Nat.card A))
    (hdelta_pi : ∀ a x,
      pi ((rhoT a * (rhoM a)⁻¹) x) = pi x)
    (hdelta_iota : ∀ a z,
      (rhoT a * (rhoM a)⁻¹) (iota z) = iota z)
    (hkernel_conj : ∀ a alpha,
      (∀ x, pi (alpha x) = pi x) →
      (∀ z, alpha (iota z) = iota z) →
      (∀ x, pi ((rhoM a * alpha * (rhoM a)⁻¹) x) = pi x) ∧
        ∀ z, (rhoM a * alpha * (rhoM a)⁻¹) (iota z) = iota z) :
    ∃ u : MulAut P, ∀ a, u⁻¹ * rhoT a * u = rhoM a := by
  classical
  obtain ⟨encode, hencode_injective, hencode_zero, hencode_add,
      hencode_pi, hencode_iota, hencode_unique⟩ :=
    lemma1d_extension_kernel_automorphisms
      iota pi hiota hpi hexact hcentral
  let KernelParam := V →ₗ[ZMod 2] W
  letI : Finite KernelParam :=
    Finite.of_injective (fun f : KernelParam => (f : V → W)) (by
      intro f g h
      ext x
      exact congrFun h x)
  let encodeHom : Multiplicative KernelParam →* MulAut P :=
    { toFun := fun f => encode f.toAdd
      map_one' := hencode_zero
      map_mul' := by
        intro f g
        exact hencode_add f.toAdd g.toAdd }
  have hencodeHom_injective : Function.Injective encodeHom := by
    intro f g hfg
    apply Multiplicative.toAdd.injective
    exact hencode_injective hfg
  let U : Subgroup (MulAut P) := encodeHom.range
  let delta (a : A) : MulAut P := rhoT a * (rhoM a)⁻¹
  have hdelta_mem (a : A) : delta a ∈ U := by
    obtain ⟨f, hf, _⟩ :=
      hencode_unique (delta a) (hdelta_pi a) (hdelta_iota a)
    exact ⟨Multiplicative.ofAdd f, hf⟩
  have hU_fixes (u : U) :
      (∀ x, pi (u.1 x) = pi x) ∧
        ∀ z, u.1 (iota z) = iota z := by
    rcases u.2 with ⟨f, hf⟩
    constructor
    · intro x
      rw [← hf]
      exact hencode_pi f.toAdd x
    · intro z
      rw [← hf]
      exact hencode_iota f.toAdd z
  have hconjModel_mem (a : A) (u : U) :
      rhoM a * u.1 * (rhoM a)⁻¹ ∈ U := by
    obtain ⟨hfixPi, hfixIota⟩ := hU_fixes u
    obtain ⟨hconjPi, hconjIota⟩ :=
      hkernel_conj a u.1 hfixPi hfixIota
    obtain ⟨f, hf, _⟩ :=
      hencode_unique (rhoM a * u.1 * (rhoM a)⁻¹)
        hconjPi hconjIota
    exact ⟨Multiplicative.ofAdd f, hf⟩
  have hrhoM_normalizes :
      rhoM.range ≤ Subgroup.normalizer (U : Set (MulAut P)) := by
    rintro g ⟨a, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · intro hu
      exact hconjModel_mem a ⟨u, hu⟩
    · intro hu
      have hback := hconjModel_mem a⁻¹
        ⟨rhoM a * u * (rhoM a)⁻¹, hu⟩
      convert hback using 1; simp only [map_inv]; group
  letI : MulDistribMulAction rhoM.range U :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer
      rhoM.range U hrhoM_normalizes
  letI : MulDistribMulAction A U :=
    MulDistribMulAction.compHom U rhoM.rangeRestrict
  let cocycle : A → U := fun a => ⟨delta a, hdelta_mem a⟩
  have hcocycle (a b : A) :
      cocycle (a * b) = cocycle a * (a • cocycle b) := by
    apply Subtype.ext
    change delta (a * b) = delta a *
      (rhoM a * delta b * (rhoM a)⁻¹)
    simp only [delta, map_mul]
    group
  have hUcommutative : IsMulCommutative U := by
    refine IsMulCommutative.mk ⟨?_⟩
    intro u v
    rcases u with ⟨u, ⟨f, rfl⟩⟩
    rcases v with ⟨v, ⟨g, rfl⟩⟩
    apply Subtype.ext
    change encodeHom f * encodeHom g = encodeHom g * encodeHom f
    rw [← map_mul, ← map_mul]
    congr 1
    exact mul_comm f g
  letI : IsMulCommutative U := hUcommutative
  haveI : CommGroup U :=
    { mul_comm := by
        intro a b
        have h := (isMulCommutative_iff.mp hUcommutative) a b
        exact h }
  let kernelIso : Multiplicative KernelParam ≃* U :=
    (MonoidHom.ofInjective hencodeHom_injective).trans
      (MulEquiv.subgroupCongr rfl)
  have hUsolvable : Group.IsSolvable U := by
    have : Group.IsSolvable (Multiplicative KernelParam) := by
      -- Multiplicative KernelParam is an abelian group (it's a ZMod 2-vector space)
      infer_instance
    let : Group.IsSolvable (Multiplicative KernelParam) := this
    refine Group.isSolvable_of_surjective (f := kernelIso.toMonoidHom) ?_
    -- kernelIso is an isomorphism, so it's surjective
    intro x
    refine ⟨kernelIso.symm x, ?_⟩
    simp
  haveI : Finite U :=
    Finite.of_injective (fun u : U => kernelIso.symm u) (kernelIso.symm.injective)
  have hcardU : Nat.card U =
      2 ^ Module.finrank (ZMod 2) KernelParam := by
    calc
      Nat.card U = Nat.card (Multiplicative KernelParam) :=
        (Nat.card_congr kernelIso.toEquiv).symm
      _ = Nat.card KernelParam := rfl
      _ = Nat.card (ZMod 2) ^ Module.finrank (ZMod 2) KernelParam :=
        Module.natCard_eq_pow_finrank
      _ = 2 ^ Module.finrank (ZMod 2) KernelParam := by norm_num
  have hAU_coprime : Nat.Coprime (Nat.card A) (Nat.card U) := by
    rw [hcardU]
    exact Nat.prime_two.coprime_pow_of_not_dvd hAodd.not_two_dvd_nat
  obtain ⟨uCorrect, huCorrect⟩ :=
    exists_principal_cocycle_of_solvable_coprime
      (A := A) hUsolvable hAU_coprime cocycle hcocycle
  refine ⟨uCorrect.1, ?_⟩
  intro a
  have hdelta_correct :
      delta a = (uCorrect.1 : MulAut P) *
        (rhoM a * (uCorrect.1 : MulAut P) * (rhoM a)⁻¹)⁻¹ := by
    exact congrArg (fun z : U => (z : MulAut P)) (huCorrect a)
  have htransport :
      rhoT a = (uCorrect.1 : MulAut P) * rhoM a *
        (uCorrect.1 : MulAut P)⁻¹ := by
    calc
      rhoT a = (rhoT a * (rhoM a)⁻¹) * rhoM a := by group
      _ = (uCorrect.1 : MulAut P) *
          (rhoM a * (uCorrect.1 : MulAut P) * (rhoM a)⁻¹)⁻¹ *
            rhoM a := by
        exact congrArg (fun z : MulAut P => z * rhoM a) hdelta_correct
      _ = (uCorrect.1 : MulAut P) * rhoM a *
          (uCorrect.1 : MulAut P)⁻¹ := by group
  rw [htransport]
  group

private theorem nat_square_sub_one_factor (q : ℕ) (hq : 1 < q) :
    q ^ 2 - 1 = (q + 1) * (q - 1) := by
  have hsub : q - 1 + 1 = q := Nat.sub_add_cancel hq.le
  apply (Nat.sub_eq_iff_eq_add (by nlinarith : 1 ≤ q ^ 2)).2
  nlinarith

private theorem card_quotient_units_eq_add_one
    {E : Type*} [Field E] [Finite E] (K : Subgroup Eˣ) (q : ℕ)
    (hq : 1 < q) (hcardE : Nat.card E = q ^ 2)
    (hcardK : Nat.card K = q - 1) :
    Nat.card (Eˣ ⧸ K) = q + 1 := by
  have hcardFormula :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup K
  rw [Nat.card_units, hcardE, hcardK,
    nat_square_sub_one_factor q hq] at hcardFormula
  apply Nat.mul_right_cancel (Nat.sub_pos_of_lt hq)
  exact hcardFormula.symm

private theorem transport_multiplicative_polar_identity
    {X Q Z : Type*} [Group X] [Group Q] [Group Z]
    (e : X ≃* Q) (f : Z →* X) (q : Q → Z)
    (hpolar : ∀ x₁ x₂ y : Q,
      q ((x₁ * x₂) * y) * (q (x₁ * x₂))⁻¹ * (q y)⁻¹ =
        (q (x₁ * y) * (q x₁)⁻¹ * (q y)⁻¹) *
          (q (x₂ * y) * (q x₂)⁻¹ * (q y)⁻¹))
    (x₁ x₂ y : X) :
    f (q (e ((x₁ * x₂) * y))) *
          (f (q (e (x₁ * x₂))))⁻¹ * (f (q (e y)))⁻¹ =
      (f (q (e (x₁ * y))) * (f (q (e x₁)))⁻¹ *
          (f (q (e y)))⁻¹) *
        (f (q (e (x₂ * y))) * (f (q (e x₂)))⁻¹ *
          (f (q (e y)))⁻¹) := by
  simpa using congrArg f (hpolar (e x₁) (e x₂) (e y))

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
private theorem typeB_model_central_extension_data
    {E S1 : Type*} [Field E] [Finite E] [CharP E 2]
    [Module (ZMod 2) E] [Group S1]
    (F : Subfield E) (theta : F ≃+* F) (sigma bar : E ≃+* E)
    (phi : E → E → E) (qNorm : QuadraticMap (ZMod 2) E E)
    (qF : QuadraticMap (ZMod 2) E F)
    (coord : S1 ≃
      {p : E × E //
        (theta = 1 ∧ p.2 + sigma p.2 = p.1 * sigma p.1) ∨
          (theta ≠ 1 ∧ p.2 ∈ F)})
    (hcoordMul : ∀ x y : S1,
      ((coord (x * y)).1 : E × E) =
        ((coord x).1.1 + (coord y).1.1,
          (coord x).1.2 + (coord y).1.2 +
            phi (coord x).1.1 (coord y).1.1))
    (piModel : S1 →* Multiplicative E)
    (iotaModel : Multiplicative F →* S1)
    (hpiModel_coord : ∀ x : S1,
      (piModel x).toAdd = (coord x).1.1)
    (hiotaModel_coord : ∀ z : Multiplicative F,
      ((coord (iotaModel z)).1 : E × E) = (0, (z.toAdd : E)))
    (htrace_formula : ∀ x : E,
      (Algebra.trace F E x : E) = x + bar x)
    (hmemF_of_bar_fixed : ∀ x : E, bar x = x → x ∈ F)
    (hsigma_eq_bar : theta = 1 → sigma = bar)
    (hqNorm_norm : theta = 1 → ∀ x : E, qNorm x = x * bar x)
    (hphi_zero_left : ∀ z : E, phi 0 z = 0)
    (hphi_zero_right : ∀ z : E, phi z 0 = 0)
    (hphi_diag : ∀ x : E, phi x x = qNorm x)
    (hqF_apply : ∀ x : E, (qF x : E) = qNorm x) :
    Function.Injective iotaModel ∧
      Function.Surjective piModel ∧
      iotaModel.range = piModel.ker ∧
      iotaModel.range ≤ Subgroup.center S1 ∧
      ∀ x : S1,
        iotaModel (Multiplicative.ofAdd (qF (piModel x).toAdd)) = x ^ 2 := by
  classical
  have hiotaModel_injective : Function.Injective iotaModel := by
    intro z w h
    have hc := congrArg (fun x : S1 => ((coord x).1 : E × E)) h
    change ((coord (iotaModel z)).1 : E × E) =
      ((coord (iotaModel w)).1 : E × E) at hc
    rw [hiotaModel_coord, hiotaModel_coord] at hc
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact congrArg Prod.snd hc
  have hpiModel_surjective : Function.Surjective piModel := by
    intro u
    let x : E := u.toAdd
    by_cases htheta : theta = 1
    · have hnormMem : x * bar x ∈ F := by
        have hqMem : qNorm x ∈ F := by
          rw [← hqF_apply]
          exact (qF x).property
        rw [hqNorm_norm htheta] at hqMem
        exact hqMem
      let normF : F := ⟨x * bar x, hnormMem⟩
      obtain ⟨y, hy⟩ := (Algebra.trace_surjective F E) normF
      have hyTrace : y + sigma y = x * sigma x := by
        rw [hsigma_eq_bar htheta]
        calc
          y + bar y = (Algebra.trace F E y : E) :=
            (htrace_formula y).symm
          _ = (normF : E) := by rw [hy]
          _ = x * bar x := rfl
      let p :
          {r : E × E //
            (theta = 1 ∧ r.2 + sigma r.2 = r.1 * sigma r.1) ∨
              (theta ≠ 1 ∧ r.2 ∈ F)} :=
        ⟨(x, y), Or.inl ⟨htheta, hyTrace⟩⟩
      refine ⟨coord.symm p, ?_⟩
      apply Multiplicative.toAdd.injective
      rw [hpiModel_coord, coord.apply_symm_apply]
    · let p :
          {r : E × E //
            (theta = 1 ∧ r.2 + sigma r.2 = r.1 * sigma r.1) ∨
              (theta ≠ 1 ∧ r.2 ∈ F)} :=
        ⟨(x, 0), Or.inr ⟨htheta, F.zero_mem⟩⟩
      refine ⟨coord.symm p, ?_⟩
      apply Multiplicative.toAdd.injective
      rw [hpiModel_coord, coord.apply_symm_apply]
  have hexactModel : iotaModel.range = piModel.ker := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      apply MonoidHom.mem_ker.mpr
      apply Multiplicative.toAdd.injective
      rw [hpiModel_coord, hiotaModel_coord]
      rfl
    · intro hx
      have hxpi := MonoidHom.mem_ker.mp hx
      have hxFirst : (coord x).1.1 = 0 := by
        have h := congrArg Multiplicative.toAdd hxpi
        rw [hpiModel_coord] at h
        simpa using h
      have hxSecond : (coord x).1.2 ∈ F := by
        rcases (coord x).property with hcase | hcase
        · have htheta := hcase.1
          have hsum := hcase.2
          rw [hxFirst, zero_mul] at hsum
          have hsigmaValue : sigma (coord x).1.2 =
              bar (coord x).1.2 := by
            exact DFunLike.congr_fun (hsigma_eq_bar htheta) (coord x).1.2
          rw [hsigmaValue] at hsum
          have hfixed : bar (coord x).1.2 = (coord x).1.2 := by
            have hneg : bar (coord x).1.2 = -(coord x).1.2 :=
              eq_neg_of_add_eq_zero_right hsum
            simpa only [ZModModule.neg_eq_self] using hneg
          exact hmemF_of_bar_fixed _ hfixed
        · exact hcase.2
      let z : F := ⟨(coord x).1.2, hxSecond⟩
      refine ⟨Multiplicative.ofAdd z, ?_⟩
      apply coord.injective
      apply Subtype.ext
      rw [hiotaModel_coord]
      exact Prod.ext hxFirst.symm rfl
  have hcentralModel : iotaModel.range ≤ Subgroup.center S1 := by
    rintro z ⟨a, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro x
    apply coord.injective
    apply Subtype.ext
    rw [hcoordMul, hcoordMul, hiotaModel_coord]
    change ((coord x).1.1 + 0,
        (coord x).1.2 + (a.toAdd : E) + phi (coord x).1.1 0) =
      (0 + (coord x).1.1,
        (a.toAdd : E) + (coord x).1.2 + phi 0 (coord x).1.1)
    rw [hphi_zero_left, hphi_zero_right]
    apply Prod.ext
    · simp
    · simp only [add_comm]
  have hsquareModel (x : S1) :
      iotaModel (Multiplicative.ofAdd (qF (piModel x).toAdd)) = x ^ 2 := by
    apply coord.injective
    apply Subtype.ext
    rw [hiotaModel_coord, pow_two, hcoordMul, hpiModel_coord]
    change (0, (qF (coord x).1.1 : E)) =
      ((coord x).1.1 + (coord x).1.1,
        (coord x).1.2 + (coord x).1.2 +
          phi (coord x).1.1 (coord x).1.1)
    rw [hqF_apply, hphi_diag, CharTwo.add_self_eq_zero,
      CharTwo.add_self_eq_zero]
    simp
  exact ⟨hiotaModel_injective, hpiModel_surjective, hexactModel,
    hcentralModel, hsquareModel⟩

universe u v

set_option maxHeartbeats 800000 in
private theorem central_extensions_equivalent_same_quadratic_lift_right
    {V W P' : Type} {P : Type u}
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    [Group P] [Group P']
    (iota : Multiplicative W →* P) (pi : P →* Multiplicative V)
    (iota' : Multiplicative W →* P') (pi' : P' →* Multiplicative V)
    (q : QuadraticMap (ZMod 2) V W)
    (hiota : Function.Injective iota) (hpi : Function.Surjective pi)
    (hexact : iota.range = pi.ker)
    (hcentral : iota.range ≤ Subgroup.center P)
    (hiota' : Function.Injective iota') (hpi' : Function.Surjective pi')
    (hexact' : iota'.range = pi'.ker)
    (hcentral' : iota'.range ≤ Subgroup.center P')
    (hsquare : ∀ x : P,
      iota (Multiplicative.ofAdd (q (pi x).toAdd)) = x ^ 2)
    (hsquare' : ∀ x : P',
      iota' (Multiplicative.ofAdd (q (pi' x).toAdd)) = x ^ 2) :
    ∃ e : P ≃* P',
      (∀ x : P, (pi' (e x)).toAdd = (pi x).toAdd) ∧
        ∀ z : Multiplicative W, e (iota z) = iota' z := by
  let eU : ULift.{u} P' ≃* P' := MulEquiv.ulift
  let iotaU : Multiplicative W →* ULift.{u} P' :=
    eU.symm.toMonoidHom.comp iota'
  let piU : ULift.{u} P' →* Multiplicative V :=
    pi'.comp eU.toMonoidHom
  have hiotaU : Function.Injective iotaU :=
    eU.symm.injective.comp hiota'
  have hpiU : Function.Surjective piU := by
    intro x
    obtain ⟨y, rfl⟩ := hpi' x
    exact ⟨eU.symm y, by simp [piU]⟩
  have hexactU : iotaU.range = piU.ker := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      apply MonoidHom.mem_ker.mpr
      have hz : iota' z ∈ pi'.ker := by
        rw [← hexact']
        exact ⟨z, rfl⟩
      simpa [iotaU, piU] using MonoidHom.mem_ker.mp hz
    · intro hx
      have hx' : eU x ∈ pi'.ker := by
        apply MonoidHom.mem_ker.mpr
        simpa [piU] using MonoidHom.mem_ker.mp hx
      rw [← hexact'] at hx'
      rcases hx' with ⟨z, hz⟩
      refine ⟨z, ?_⟩
      apply eU.injective
      simpa [iotaU] using hz
  have hcentralU : iotaU.range ≤ Subgroup.center (ULift.{u} P') := by
    rintro x ⟨z, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    apply eU.injective
    simpa [iotaU] using
      (Subgroup.mem_center_iff.mp (hcentral' ⟨z, rfl⟩) (eU y))
  have hsquareU (x : ULift.{u} P') :
      iotaU (Multiplicative.ofAdd (q (piU x).toAdd)) = x ^ 2 := by
    apply eU.injective
    simpa [iotaU, piU] using hsquare' (eU x)
  obtain ⟨eLift, heLiftPi, heLiftIota⟩ :=
    (lemma1c_central_extensions_equivalent_iff
      iota pi iotaU piU q q hiota hpi hexact hcentral
      hiotaU hpiU hexactU hcentralU hsquare hsquareU
      (LinearEquiv.refl (ZMod 2) V)
      (LinearEquiv.refl (ZMod 2) W)).2 (fun _ => rfl)
  refine ⟨eLift.trans eU, ?_, ?_⟩
  · intro x
    simpa [piU] using heLiftPi x
  · intro z
    simpa [iotaU] using congrArg eU (heLiftIota z)

set_option maxHeartbeats 800000 in
private theorem phi_twisted_additive_core
    {E : Type*} [Field E] [Module (ZMod 2) E]
    (qNorm : QuadraticMap (ZMod 2) E E) (c t d : E) :
    let phiTwisted : E → E → E := fun x y =>
      d * (qNorm.polarBilin (c * x) y + t * qNorm.polarBilin x y)
    (∀ x y z, phiTwisted (x + y) z =
      phiTwisted x z + phiTwisted y z) ∧
    ∀ x y z, phiTwisted x (y + z) =
      phiTwisted x y + phiTwisted x z := by
  dsimp
  constructor
  · intro x y z
    simp [mul_add]
    ring
  · intro x y z
    simp [mul_add]
    ring

set_option maxHeartbeats 800000 in
private theorem phi_twisted_polar_decomp_core
    {E : Type*} [Field E] [CharP E 2] [Module (ZMod 2) E]
    (F : Subfield E) (theta : F ≃+* F)
    (qNorm : QuadraticMap (ZMod 2) E E)
    (cTheta dTheta : F) (hdTheta : dTheta = cTheta + theta cTheta)
    (hdThetaE : (dTheta : E) ≠ 0)
    (hpolarScaleSum : ∀ (a : F) (x y : E),
      qNorm.polarBilin ((a : E) * x) y +
          qNorm.polarBilin x ((a : E) * y) =
        ((a : E) + (theta a : E)) * qNorm.polarBilin x y)
    (hpolarCross : ∀ (a b : F) (x y : E),
      qNorm.polarBilin ((a : E) * x) ((b : E) * y) +
          qNorm.polarBilin ((a : E) * y) ((b : E) * x) =
        ((a : E) * (theta b : E) +
          (b : E) * (theta a : E)) * qNorm.polarBilin x y)
    (a : F) (x y : E) :
    qNorm.polarBilin ((a : E) * x) y =
      (a : E) * ((dTheta⁻¹ : E) *
        (qNorm.polarBilin ((cTheta : E) * x) y +
          (theta cTheta : E) * qNorm.polarBilin x y)) +
      (theta a : E) * ((dTheta⁻¹ : E) *
        (qNorm.polarBilin ((cTheta : E) * y) x +
          (theta cTheta : E) * qNorm.polarBilin y x)) := by
  have h1 := hpolarScaleSum cTheta ((a : E) * x) y
  have h2 := hpolarScaleSum a ((cTheta : E) * x) y
  have h3 := hpolarCross a cTheta x y
  have h4 := hpolarScaleSum cTheta x y
  rw [show qNorm.polarBilin (((a : E) * y))
      ((cTheta : E) * x) =
    qNorm.polarBilin ((cTheta : E) * x) ((a : E) * y) from
      QuadraticMap.polar_comm qNorm ((a : E) * y)
        ((cTheta : E) * x)] at h3
  let U : E := qNorm.polarBilin ((a : E) * x) y
  let V : E := qNorm.polarBilin x y
  let P : E :=
    qNorm.polarBilin ((cTheta : E) * ((a : E) * x)) y
  let Q : E :=
    qNorm.polarBilin ((a : E) * x) ((cTheta : E) * y)
  let R : E :=
    qNorm.polarBilin ((cTheta : E) * x) ((a : E) * y)
  let T : E :=
    qNorm.polarBilin ((cTheta : E) * y) x
  let S0 : E := qNorm.polarBilin ((cTheta : E) * x) y
  have h1p : P + Q = (dTheta : E) * U := by
    dsimp [P, Q, U]
    rw [hdTheta]
    exact h1
  have h2p : P + R =
      ((a : E) + (theta a : E)) * S0 := by
    dsimp [P, R, S0]
    rw [show (cTheta : E) * ((a : E) * x) =
      (a : E) * ((cTheta : E) * x) by ring]
    exact h2
  have h3p : Q + R =
      ((a : E) * (theta cTheta : E) +
        (cTheta : E) * (theta a : E)) * V := by
    dsimp [Q, R, V]
    exact h3
  have h4p : S0 + T = (dTheta : E) * V := by
    dsimp [S0, T, V]
    simp [QuadraticMap.polar_comm qNorm ((cTheta : E) * y) x, hdTheta, QuadraticMap.polarBilin_apply_apply]
    exact h4
  have hT : T = S0 + (dTheta : E) * V := by
    calc
      T = T + 0 := by simp
      _ = T + (S0 + S0) := by rw [CharTwo.add_self_eq_zero]
      _ = (S0 + T) + S0 := by abel
      _ = (dTheta : E) * V + S0 := by rw [h4p]
      _ = S0 + (dTheta : E) * V := add_comm _ _
  have hmain :
      (dTheta : E) * U =
        (a : E) * S0 +
          (a : E) * (theta cTheta : E) * V +
        (theta a : E) * T +
          (theta a : E) * (theta cTheta : E) * V := by
    calc
      (dTheta : E) * U = P + Q := h1p.symm
      _ = (P + R) + (Q + R) := by
        calc
          P + Q = P + Q + 0 := by simp
          _ = P + Q + (R + R) := by
            rw [CharTwo.add_self_eq_zero]
          _ = (P + R) + (Q + R) := by abel
      _ = ((a : E) + (theta a : E)) * S0 +
          ((a : E) * (theta cTheta : E) +
            (cTheta : E) * (theta a : E)) * V := by
        rw [h2p, h3p]
      _ = (a : E) * S0 +
          (a : E) * (theta cTheta : E) * V +
        (theta a : E) * T +
          (theta a : E) * (theta cTheta : E) * V := by
        rw [hT, hdTheta]
        push_cast
        ring_nf
        have htwo : (2 : E) = 0 := by
          simpa only [one_add_one_eq_two] using
            (CharTwo.add_self_eq_zero (1 : E))
        simp only [htwo, mul_zero, add_zero]
  change U =
    (a : E) * ((dTheta⁻¹ : E) *
      (S0 + (theta cTheta : E) * V)) +
    (theta a : E) * ((dTheta⁻¹ : E) *
      (T + (theta cTheta : E) * qNorm.polarBilin y x))
  rw [show qNorm.polarBilin y x = V by
    exact QuadraticMap.polar_comm qNorm y x]
  apply mul_left_cancel₀ hdThetaE
  rw [hmain]
  field_simp [hdThetaE]
  ring

set_option maxHeartbeats 800000 in
private theorem phi_twisted_smul_left_core
    {E : Type*} [Field E] [CharP E 2] [Module (ZMod 2) E]
    (F : Subfield E) (theta : F ≃+* F)
    (qNorm : QuadraticMap (ZMod 2) E E)
    (cTheta dTheta : F) (hdTheta : dTheta = cTheta + theta cTheta)
    (hdThetaE : (dTheta : E) ≠ 0)
    (hpolarScaleSum : ∀ (a : F) (x y : E),
      qNorm.polarBilin ((a : E) * x) y +
          qNorm.polarBilin x ((a : E) * y) =
        ((a : E) + (theta a : E)) * qNorm.polarBilin x y)
    (hpolarCross : ∀ (a b : F) (x y : E),
      qNorm.polarBilin ((a : E) * x) ((b : E) * y) +
          qNorm.polarBilin ((a : E) * y) ((b : E) * x) =
        ((a : E) * (theta b : E) +
          (b : E) * (theta a : E)) * qNorm.polarBilin x y)
    (a : F) (x y : E) :
    (dTheta⁻¹ : E) *
        (qNorm.polarBilin ((cTheta : E) * ((a : E) * x)) y +
          (theta cTheta : E) * qNorm.polarBilin ((a : E) * x) y) =
      (a : E) * ((dTheta⁻¹ : E) *
        (qNorm.polarBilin ((cTheta : E) * x) y +
          (theta cTheta : E) * qNorm.polarBilin x y)) := by
  let phiTwisted (x y : E) : E :=
    (dTheta⁻¹ : E) *
      (qNorm.polarBilin ((cTheta : E) * x) y +
        (theta cTheta : E) * qNorm.polarBilin x y)
  have hpolar (b : F) (u v : E) :
      qNorm.polarBilin ((b : E) * u) v =
        (b : E) * phiTwisted u v +
          (theta b : E) * phiTwisted v u := by
    dsimp [phiTwisted]
    exact phi_twisted_polar_decomp_core F theta qNorm cTheta dTheta
      hdTheta hdThetaE hpolarScaleSum hpolarCross b u v
  rw [show (cTheta : E) * ((a : E) * x) =
    ((cTheta * a : F) : E) * x by push_cast; ring]
  change (dTheta⁻¹ : E) *
      (qNorm.polarBilin (((cTheta * a : F) : E) * x) y +
        (theta cTheta : E) * qNorm.polarBilin ((a : E) * x) y) =
    (a : E) * ((dTheta⁻¹ : E) *
      (qNorm.polarBilin ((cTheta : E) * x) y +
        (theta cTheta : E) * qNorm.polarBilin x y))
  rw [hpolar (cTheta * a) x y, hpolar a x y, map_mul]
  field_simp [hdThetaE]
  push_cast
  have hpolarOne := hpolar (1 : F) x y
  have hpolarOneEq : qNorm.polarBilin x y =
      phiTwisted x y + phiTwisted y x := by
    simpa using hpolarOne
  rw [hpolar cTheta x y, hpolarOneEq]
  ring_nf
  have htwo : (2 : E) = 0 := by
    simpa only [one_add_one_eq_two] using
      (CharTwo.add_self_eq_zero (1 : E))
  simp only [htwo, mul_zero, add_zero]

set_option maxHeartbeats 800000 in
private theorem typeB_model_target_involution
    {E S1 : Type*} [Field E] [CharP E 2] [Group S1]
    (F : Subfield E) (theta : F ≃+* F) (sigma : E ≃+* E)
    (phi : E → E → E)
    (coord : S1 ≃
      {p : E × E //
        (theta = 1 ∧ p.2 + sigma p.2 = p.1 * sigma p.1) ∨
          (theta ≠ 1 ∧ p.2 ∈ F)})
    (hcoordMul : ∀ x y : S1,
      ((coord (x * y)).1 : E × E) =
        ((coord x).1.1 + (coord y).1.1,
          (coord x).1.2 + (coord y).1.2 +
            phi (coord x).1.1 (coord y).1.1))
    (hcoordOne : ((coord (1 : S1)).1 : E × E) = (0, 0))
    (hphiZeroLeft : ∀ z : E, phi 0 z = 0) :
    ∃ target : S1, IsInvolution target ∧
      ((coord target).1 : E × E) = (0, 1) := by
  let targetPoint :
      {p : E × E //
        (theta = 1 ∧ p.2 + sigma p.2 = p.1 * sigma p.1) ∨
          (theta ≠ 1 ∧ p.2 ∈ F)} :=
    ⟨(0, 1), by
      by_cases htheta : theta = 1
      · left
        refine ⟨htheta, ?_⟩
        rw [map_one, map_zero, zero_mul]
        exact CharTwo.add_self_eq_zero (1 : E)
      · exact Or.inr ⟨htheta, F.one_mem⟩⟩
  let target : S1 := coord.symm targetPoint
  have hcoordTarget : ((coord target).1 : E × E) = (0, 1) := by
    rw [coord.apply_symm_apply]
  have htargetNeOne : target ≠ 1 := by
    intro h
    have hcoordEq : ((coord target).1 : E × E) =
        ((coord (1 : S1)).1 : E × E) :=
      congrArg (fun z : S1 => ((coord z).1 : E × E)) h
    have hc : (1 : E) = 0 := by
      calc
        (1 : E) = ((coord target).1 : E × E).2 := by rw [hcoordTarget]
        _ = ((coord (1 : S1)).1 : E × E).2 := congrArg Prod.snd hcoordEq
        _ = 0 := by rw [hcoordOne]
    exact one_ne_zero hc
  have htargetSq : target ^ 2 = 1 := by
    apply coord.injective
    apply Subtype.ext
    rw [pow_two, hcoordMul, hcoordTarget, hcoordOne]
    simpa [hphiZeroLeft] using (CharTwo.add_self_eq_zero (1 : E))
  exact ⟨target, ⟨htargetNeOne, htargetSq⟩, hcoordTarget⟩

set_option maxHeartbeats 800000 in
private theorem actor_scale_decomp_core
    {B E : Type*} [Field B] [Field E] [Algebra B E]
    (F : Subfield E) (baseEquiv : F ≃+* B)
    (theta : F ≃+* F) (thetaB : B ≃+* B) (sigma : E ≃+* E)
    (hbaseCoe : ∀ a : F,
      (a : E) = algebraMap B E (baseEquiv a))
    (htheta : ∀ a : F,
      baseEquiv (theta a) = thetaB (baseEquiv a))
    (c b : F) (w : Eˣ)
    (hc : (c : E) =
      ((b : E) * (w : E)) *
        (sigma (b : E) * sigma (w : E)))
    (hsigmaB : sigma (b : E) = (theta b : E))
    (hsigmaW : sigma (w : E) = (w : E)⁻¹) :
    baseEquiv c = baseEquiv b * thetaB (baseEquiv b) := by
  apply (algebraMap B E).injective
  rw [map_mul, ← hbaseCoe c]
  calc
    (c : E) = ((b : E) * (w : E)) *
        (sigma (b : E) * sigma (w : E)) := hc
    _ = ((b : E) * (w : E)) *
        ((theta b : E) * (w : E)⁻¹) := by
      rw [hsigmaB, hsigmaW]
    _ = (b : E) * (theta b : E) *
        ((w : E) * (w : E)⁻¹) := by ring
    _ = (b : E) * (theta b : E) := by
      rw [mul_inv_cancel₀ (Units.ne_zero w), mul_one]
    _ = algebraMap B E (baseEquiv b) *
        algebraMap B E (thetaB (baseEquiv b)) := by
      rw [hbaseCoe b, hbaseCoe (theta b), htheta]

set_option maxHeartbeats 800000 in
private theorem actor_scale_decomp_of_decomposition
    {B E A K W : Type*}
    [Field B] [Field E] [Algebra B E]
    [Group A] [Group K] [Group W]
    (F : Subfield E) (baseEquiv : F ≃+* B)
    (theta : F ≃+* F) (thetaB : B ≃+* B) (sigma : E ≃+* E)
    (kwUnits : A →* Eˣ) (kIncl : K →* A) (wIncl : W →* A)
    (eK : K →* Bˣ) (actorScale : A → F)
    (hactorScale : ∀ a : A,
      (actorScale a : E) =
        (kwUnits a : E) * sigma (kwUnits a : E))
    (hbaseCoe : ∀ a : F,
      (a : E) = algebraMap B E (baseEquiv a))
    (htheta : ∀ a : F,
      baseEquiv (theta a) = thetaB (baseEquiv a))
    (hkwK : ∀ k : K,
      (kwUnits (kIncl k) : E) =
        algebraMap B E (eK k : B))
    (hsigmaBase : ∀ b : F, sigma (b : E) = (theta b : E))
    (hsigmaW : ∀ w : W,
      sigma (kwUnits (wIncl w) : E) =
        (kwUnits (wIncl w) : E)⁻¹)
    (a : A) (k : K) (w : W) (ha : a = kIncl k * wIncl w) :
    baseEquiv (actorScale a) =
      (eK k : B) * thetaB (eK k : B) := by
  let b : F := baseEquiv.symm (eK k : B)
  have hbBase : baseEquiv b = (eK k : B) := by
    simp [b]
  have hbK : (b : E) = (kwUnits (kIncl k) : E) := by
    rw [hkwK, ← hbBase, ← hbaseCoe]
  have hkwUnitsMul :
      (kwUnits a : E) =
        (kwUnits (kIncl k) : E) * (kwUnits (wIncl w) : E) := by
    have hUnits : kwUnits a =
        kwUnits (kIncl k) * kwUnits (wIncl w) := by
      calc
        kwUnits a = kwUnits (kIncl k * wIncl w) := congrArg kwUnits ha
        _ = kwUnits (kIncl k) * kwUnits (wIncl w) := map_mul kwUnits _ _
    exact congrArg (fun u : Eˣ => (u : E)) hUnits
  have hsigmaMul :
      sigma (kwUnits a : E) =
        sigma (kwUnits (kIncl k) : E) *
          sigma (kwUnits (wIncl w) : E) := by
    calc
      sigma (kwUnits a : E) =
          sigma ((kwUnits (kIncl k) : E) *
            (kwUnits (wIncl w) : E)) := congrArg sigma hkwUnitsMul
      _ = sigma (kwUnits (kIncl k) : E) *
          sigma (kwUnits (wIncl w) : E) := map_mul sigma _ _
  have hc : (actorScale a : E) =
      ((b : E) * (kwUnits (wIncl w) : E)) *
        (sigma (b : E) * sigma (kwUnits (wIncl w) : E)) := by
    calc
      (actorScale a : E) =
          (kwUnits a : E) * sigma (kwUnits a : E) := hactorScale a
      _ = ((kwUnits (kIncl k) : E) *
              (kwUnits (wIncl w) : E)) *
            (sigma (kwUnits (kIncl k) : E) *
              sigma (kwUnits (wIncl w) : E)) :=
        congrArg₂ (fun x y : E => x * y) hkwUnitsMul hsigmaMul
      _ = ((b : E) * (kwUnits (wIncl w) : E)) *
            (sigma (b : E) * sigma (kwUnits (wIncl w) : E)) := by
        rw [hbK]
  have hcore := actor_scale_decomp_core F baseEquiv theta thetaB sigma
    hbaseCoe htheta (actorScale a) b (kwUnits (wIncl w))
    hc (hsigmaBase b) (hsigmaW w)
  simpa only [hbBase] using hcore

set_option maxHeartbeats 800000 in
private theorem align_odd_actions_from_matching_boundary
    {A V W P : Type*}
    [Group A] [Finite A]
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    [Group P]
    (iota : Multiplicative W →* P)
    (pi : P →* Multiplicative V)
    (hiota : Function.Injective iota)
    (hpi : Function.Surjective pi)
    (hexact : iota.range = pi.ker)
    (hcentral : iota.range ≤ Subgroup.center P)
    (rhoT rhoM : A →* MulAut P)
    (centerInv : A → Multiplicative W → Multiplicative W)
    (hAodd : Odd (Nat.card A))
    (hboundaryPi : ∀ a x, pi (rhoT a x) = pi (rhoM a x))
    (hboundaryIota : ∀ a z, rhoT a (iota z) = rhoM a (iota z))
    (hrhoM_pi_congr : ∀ a x y, pi x = pi y →
      pi (rhoM a x) = pi (rhoM a y))
    (hrhoM_inv_iota : ∀ a z,
      (rhoM a)⁻¹ (iota z) = iota (centerInv a z)) :
    ∃ u : MulAut P, ∀ a, u⁻¹ * rhoT a * u = rhoM a := by
  have hdelta_pi (a : A) (x : P) :
      pi ((rhoT a * (rhoM a)⁻¹) x) = pi x := by
    change pi (rhoT a ((rhoM a)⁻¹ x)) = pi x
    calc
      pi (rhoT a ((rhoM a)⁻¹ x)) =
          pi (rhoM a ((rhoM a)⁻¹ x)) :=
        hboundaryPi a ((rhoM a)⁻¹ x)
      _ = pi x := congrArg pi ((rhoM a).apply_symm_apply x)
  have hdelta_iota (a : A) (z : Multiplicative W) :
      (rhoT a * (rhoM a)⁻¹) (iota z) = iota z := by
    change rhoT a ((rhoM a)⁻¹ (iota z)) = iota z
    rw [hrhoM_inv_iota]
    calc
      rhoT a (iota (centerInv a z)) =
          rhoM a (iota (centerInv a z)) :=
        hboundaryIota a (centerInv a z)
      _ = iota z := by
        rw [← hrhoM_inv_iota a z]
        exact (rhoM a).apply_symm_apply (iota z)
  have hkernel_conj (a : A) (alpha : MulAut P)
      (hfixPi : ∀ x, pi (alpha x) = pi x)
      (hfixIota : ∀ z, alpha (iota z) = iota z) :
      (∀ x, pi ((rhoM a * alpha * (rhoM a)⁻¹) x) = pi x) ∧
        ∀ z, (rhoM a * alpha * (rhoM a)⁻¹) (iota z) = iota z := by
    constructor
    · intro x
      change pi (rhoM a (alpha ((rhoM a)⁻¹ x))) = pi x
      calc
        pi (rhoM a (alpha ((rhoM a)⁻¹ x))) =
            pi (rhoM a ((rhoM a)⁻¹ x)) :=
          hrhoM_pi_congr a _ _ (hfixPi ((rhoM a)⁻¹ x))
        _ = pi x := congrArg pi ((rhoM a).apply_symm_apply x)
    · intro z
      change rhoM a (alpha ((rhoM a)⁻¹ (iota z))) = iota z
      rw [hrhoM_inv_iota, hfixIota]
      rw [← hrhoM_inv_iota a z]
      exact (rhoM a).apply_symm_apply (iota z)
  exact align_odd_actions_on_binary_central_extension
    iota pi hiota hpi hexact hcentral rhoT rhoM hAodd
    hdelta_pi hdelta_iota hkernel_conj

private theorem typeB_natCard_eq_cube
    {G : Type*} [Group G] [Finite G]
    (H Q Q0 S : Subgroup G)
    (hB : IsSuzukiTwoTypeB S) (hSleQ : S ≤ Q) (hQleH : Q ≤ H)
    (hQ0leQ : Q0 ≤ Q)
    (hQ0def : ∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ IsInvolution x))
    (hSQ : S = Q) :
    Nat.card Q = Nat.card Q0 ^ 3 := by
  classical
  rcases hB with ⟨r, hr, theta, epsilon, tripleLift, cocycle, hepsilon,
    hperiod, hnonzero, haddLeft, haddRight, hdiag, hmem, hone,
    hsurj, hinj, hmul⟩
  let R := BinaryGaloisField r
  let liftS : R × R × R → S := fun p =>
    ⟨tripleLift p.1 p.2.1 p.2.2, hmem p.1 p.2.1 p.2.2⟩
  have hliftS_bijective : Function.Bijective liftS := by
    constructor
    · intro p q hpq
      have hval := congrArg (fun z : S => (z : G)) hpq
      have hcoords := hinj p.1 p.2.1 p.2.2 q.1 q.2.1 q.2.2 hval
      exact Prod.ext hcoords.1 (Prod.ext hcoords.2.1 hcoords.2.2)
    · intro x
      obtain ⟨c, a, b, hx⟩ := hsurj (x : G) x.property
      exact ⟨(c, a, b), Subtype.ext hx.symm⟩
  let eS : R × R × R ≃ S := Equiv.ofBijective liftS hliftS_bijective
  have hcardS : Nat.card S = Nat.card R ^ 3 := by
    calc
      Nat.card S = Nat.card (R × R × R) := (Nat.card_congr eS).symm
      _ = Nat.card R ^ 3 := by
        rw [Nat.card_prod, Nat.card_prod]
        ring
  have hcocycle_zero : cocycle 0 0 0 0 = 0 := by
    simpa using hdiag 0 0
  have hcentral_mem_Q0 : ∀ c : R, tripleLift c 0 0 ∈ Q0 := by
    intro c
    have hsq : tripleLift c 0 0 ^ 2 = 1 := by
      rw [pow_two, hmul, hcocycle_zero]
      simp only [CharTwo.add_self_eq_zero]
      exact hone
    by_cases hone' : tripleLift c 0 0 = 1
    · exact hone' ▸ Q0.one_mem
    · exact (hQ0def _).2 (Or.inr
        ⟨hQleH (hSleQ (hmem c 0 0)), hone', hsq⟩)
  let liftQ0 : R → Q0 := fun c => ⟨tripleLift c 0 0, hcentral_mem_Q0 c⟩
  have hliftQ0_bijective : Function.Bijective liftQ0 := by
    constructor
    · intro c d hcd
      have hval := congrArg (fun z : Q0 => (z : G)) hcd
      exact (hinj c 0 0 d 0 0 hval).1
    · intro q
      have hqS : (q : G) ∈ S := by
        rw [hSQ]
        exact hQ0leQ q.property
      obtain ⟨c, a, b, hq⟩ := hsurj (q : G) hqS
      have hab : a = 0 ∧ b = 0 := by
        rcases (hQ0def (q : G)).1 q.property with hq_one | ⟨_hqH, hqI⟩
        · exact (hinj c a b 0 0 0 (by rw [← hq, hq_one, hone])).2
        · have hsquare :
              tripleLift c a b * tripleLift c a b = tripleLift 0 0 0 := by
            rw [← pow_two, ← hq, hqI.sq_eq_one, hone]
          have hcoords := hinj _ _ _ 0 0 0 (by
            rw [← hmul]
            simpa only [CharTwo.add_self_eq_zero, zero_add] using hsquare)
          have hquad :
              a * theta a + epsilon * a * theta b + b * theta b = 0 := by
            rw [← hdiag]
            simpa only [CharTwo.add_self_eq_zero, zero_add] using hcoords.1
          by_cases ha : a = 0
          · subst a
            simp only [map_zero, zero_mul, mul_zero, add_zero, zero_add] at hquad
            rcases mul_eq_zero.mp hquad with hb | hb
            · exact ⟨rfl, hb⟩
            · exact ⟨rfl, theta.injective (by simpa using hb)⟩
          · by_cases hb : b = 0
            · subst b
              simp only [map_zero, mul_zero, add_zero] at hquad
              rcases mul_eq_zero.mp hquad with ha' | ha'
              · exact ⟨ha', rfl⟩
              · exact ⟨theta.injective (by simpa using ha'), rfl⟩
            · exact False.elim (hnonzero a b ha hb hquad)
      refine ⟨c, Subtype.ext ?_⟩
      simpa [liftQ0, hab.1, hab.2] using hq.symm
  let eQ0 : R ≃ Q0 := Equiv.ofBijective liftQ0 hliftQ0_bijective
  have hcardQ0 : Nat.card Q0 = Nat.card R := (Nat.card_congr eQ0).symm
  rw [← hSQ, hcardS, hcardQ0]

private theorem typeB_square_mem_Q0
    {G : Type*} [Group G] (H Q Q0 S : Subgroup G)
    (hB : IsSuzukiTwoTypeB S) (hSleQ : S ≤ Q) (hQleH : Q ≤ H)
    (hQ0def : ∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ IsInvolution x)) :
    ∀ x : G, x ∈ S → x ^ 2 ∈ Q0 := by
  rcases hB with ⟨n, hn, theta, epsilon, tripleLift, cocycle, hepsilon,
    hperiod, hnonzero, haddLeft, haddRight, hdiag, hmem, hone,
    hsurj, hinj, hmul⟩
  intro x hxS
  rcases hsurj x hxS with ⟨c, a, b, rfl⟩
  have hsquare :
      tripleLift c a b ^ 2 = tripleLift (cocycle a b a b) 0 0 := by
    rw [pow_two, hmul]
    simp only [CharTwo.add_self_eq_zero, zero_add]
  rw [hsquare]
  by_cases hsq_one : tripleLift (cocycle a b a b) 0 0 = 1
  · rw [hsq_one]
    exact Q0.one_mem
  · apply (hQ0def _).2
    refine Or.inr ⟨hQleH (hSleQ (hmem _ _ _)), hsq_one, ?_⟩
    have hcocycle_zero : cocycle 0 0 0 0 = 0 := by
      simpa using hdiag 0 0
    calc
      tripleLift (cocycle a b a b) 0 0 ^ 2 = tripleLift 0 0 0 := by
        rw [pow_two, hmul, hcocycle_zero]
        simp only [CharTwo.add_self_eq_zero]
      _ = 1 := hone

private theorem fixedPointFree_quotient_core
    {G : Type*} [Group G] [Finite G]
    (D A Q K W Q0 S : Subgroup G)
    (hDodd : Odd (Nat.card D)) (hWleD : W ≤ D)
    (hdecomp : ∀ d : G, d ∈ A →
      ∃ w k : G, w ∈ W ∧ k ∈ K ∧ d = w * k)
    (hSQ : S = Q)
    (hQ0sq : ∀ z : G, z ∈ Q0 → z ^ 2 = 1)
    (hsq_mem_Q0 : ∀ x : G, x ∈ Q → x ^ 2 = 1 → x ∈ Q0)
    (hsquare : ∀ x : G, x ∈ Q → x ^ 2 ∈ Q0)
    (hQ0commQ : ∀ z : G, z ∈ Q0 → ∀ x : G, x ∈ Q → z * x = x * z)
    (hWcommQ0 : ∀ w : G, w ∈ W → ∀ z : G, z ∈ Q0 → z * w = w * z)
    (hregular : ConjugationRegularOn K {z : G | z ∈ S ∧ IsInvolution z})
    (hcentralizer : ∀ w : G, w ∈ W → w ≠ 1 →
      Subgroup.centralizer (Subgroup.zpowers w : Set G) ⊓ Q = Q0) :
    ∀ d : G, d ∈ A → d ≠ 1 → ∀ x : G, x ∈ Q → x ∉ Q0 →
      rightConjugateElem x d * x⁻¹ ∉ Q0 := by
  intro d hdA hdne x hxQ hxQ0 hdeltaQ0
  obtain ⟨w, k, hwW, hkK, hd⟩ := hdecomp d hdA
  let delta : G := rightConjugateElem x d * x⁻¹
  have hdelta_sq : delta ^ 2 = 1 := hQ0sq delta hdeltaQ0
  have hx_sq_Q0 : x ^ 2 ∈ Q0 := hsquare x hxQ
  have hx_sq_ne : x ^ 2 ≠ 1 := fun hx2 => hxQ0 (hsq_mem_Q0 x hxQ hx2)
  have hx_sq_involution : IsInvolution (x ^ 2) :=
    ⟨hx_sq_ne, hQ0sq (x ^ 2) hx_sq_Q0⟩
  have hdelta_comm_x : delta * x = x * delta :=
    hQ0commQ delta hdeltaQ0 x hxQ
  have hxd : rightConjugateElem x d = delta * x := by
    simp [delta, mul_assoc]
  have hconj_xsq_d : rightConjugateElem (x ^ 2) d = x ^ 2 := by
    calc
      rightConjugateElem (x ^ 2) d = (rightConjugateElem x d) ^ 2 := by
        simp [rightConjugateElem, pow_two, mul_assoc]
      _ = (delta * x) ^ 2 := by rw [hxd]
      _ = delta ^ 2 * x ^ 2 := by
        simp only [pow_two]
        calc
          (delta * x) * (delta * x) = delta * (x * delta) * x := by
            simp [mul_assoc]
          _ = delta * (delta * x) * x := by rw [← hdelta_comm_x]
          _ = (delta * delta) * (x * x) := by simp [mul_assoc]
      _ = x ^ 2 := by rw [hdelta_sq]; simp
  have hconj_xsq_w : rightConjugateElem (x ^ 2) w = x ^ 2 := by
    have hwcomm : (x ^ 2) * w = w * (x ^ 2) :=
      hWcommQ0 w hwW (x ^ 2) hx_sq_Q0
    simp [rightConjugateElem, hwcomm, mul_assoc]
  have hconj_xsq_k : rightConjugateElem (x ^ 2) k = x ^ 2 := by
    calc
      rightConjugateElem (x ^ 2) k =
          rightConjugateElem (rightConjugateElem (x ^ 2) w) k := by
        rw [hconj_xsq_w]
      _ = rightConjugateElem (x ^ 2) (w * k) := by
        simp [rightConjugateElem, mul_assoc]
      _ = x ^ 2 := by simpa [hd] using hconj_xsq_d
  have hk_one : k = 1 := by
    have hxset : x ^ 2 ∈ {z : G | z ∈ S ∧ IsInvolution z} := by
      exact ⟨by simpa [hSQ] using Q.pow_mem hxQ 2, hx_sq_involution⟩
    obtain ⟨a, ha, hunique⟩ := hregular.2 (x ^ 2) hxset (x ^ 2) hxset
    exact (hunique k ⟨hkK, hconj_xsq_k.symm⟩).trans
      (hunique 1 ⟨K.one_mem, by simp [rightConjugateElem]⟩).symm
  have hdw : d = w := by simpa [hk_one] using hd
  have hwD : w ∈ D := hWleD hwW
  have hwne : w ≠ 1 := by simpa [hdw] using hdne
  have hdelta_comm_w : delta * w = w * delta :=
    hWcommQ0 w hwW delta hdeltaQ0
  have hconj_delta_w : rightConjugateElem delta w = delta := by
    simp [rightConjugateElem, hdelta_comm_w, mul_assoc]
  have hxdw : rightConjugateElem x w = delta * x := by simpa [hdw] using hxd
  have hconj_x_wsq : rightConjugateElem x (w ^ 2) = x := by
    calc
      rightConjugateElem x (w ^ 2) =
          rightConjugateElem (rightConjugateElem x w) w := by
        simp [rightConjugateElem, pow_two, mul_assoc]
      _ = rightConjugateElem (delta * x) w := by rw [hxdw]
      _ = rightConjugateElem delta w * rightConjugateElem x w := by
        simp [rightConjugateElem, mul_assoc]
      _ = delta * (delta * x) := by rw [hconj_delta_w, hxdw]
      _ = x := by
        rw [← mul_assoc, ← pow_two, hdelta_sq]
        simp
  let C : Subgroup G := Subgroup.centralizer ({x} : Set G)
  have hwsqC : w ^ 2 ∈ C := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyx : y = x := by simpa using hy
    subst y
    calc
      x * w ^ 2 = w ^ 2 * rightConjugateElem x (w ^ 2) := by
        simp [rightConjugateElem, mul_assoc]
      _ = w ^ 2 * x := by rw [hconj_x_wsq]
  have hwodd : Odd (orderOf w) :=
    hDodd.of_dvd_nat (D.orderOf_dvd_natCard hwD)
  obtain ⟨m, hm⟩ := hwodd
  have hw_zpowers : w ∈ Subgroup.zpowers (w ^ 2) := by
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨Int.ofNat (m + 1), ?_⟩
    calc
      (w ^ 2) ^ (↑m + 1 : ℤ) = (w ^ 2) ^ ((m + 1 : ℕ) : ℤ) := by
        norm_num
      _ = (w ^ 2) ^ (m + 1) := by rw [zpow_natCast]
      _ = w ^ (2 * (m + 1)) := by rw [pow_mul]
      _ = w ^ (2 * m + 2) := by ring_nf
      _ = w ^ (orderOf w + 1) := by rw [hm]
      _ = w := by rw [pow_add, pow_orderOf_eq_one, one_mul, pow_one]
  have hwC : w ∈ C := (Subgroup.zpowers_le.mpr hwsqC) hw_zpowers
  have hxw : Commute x w := by
    rw [Subgroup.mem_centralizer_iff] at hwC
    exact hwC x (by simp)
  have hxcentral : x ∈ Subgroup.centralizer (Subgroup.zpowers w : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rcases Subgroup.mem_zpowers_iff.mp hz with ⟨n, rfl⟩
    exact (hxw.zpow_right n).eq.symm
  have hxinf : x ∈ Subgroup.centralizer (Subgroup.zpowers w : Set G) ⊓ Q :=
    ⟨hxcentral, hxQ⟩
  rw [hcentralizer w hwW hwne] at hxinf
  exact hxQ0 hxinf

private theorem subfield_coe_ne_zero_of_ne_zero
    {E : Type*} [Field E] (F : Subfield E) (a : F) (ha : a ≠ 0) :
    (a : E) ≠ 0 := by
  intro h
  apply ha
  apply Subtype.ext
  exact h

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
/--
Peterfalvi, Part II, Chapter III, Section 3, Proposition.

In the type-B case, the internal semidirect product `S ⋊ KW` has the
finite-field model `S₁ ⋊ K₁W₁` described in the source.  The statement keeps
the two actions explicit so that the displayed isomorphism is an isomorphism
of the actual semidirect products, not only a bijection of coordinate sets.
-/
public theorem proposition_of_KW_fixed_point_free
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t s : G)
    (hsection3 : ((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q) ∧
  s ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution s ∧
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r))
    (_hC1 : HypothesisC1 G V)
    (hC2 : HypothesisC2 G S W t s)
    (hWcyclic : IsCyclic W)
    (hIsoPackage : ∃ hKnormS : K ≤ Subgroup.normalizer (S : Set G),
      letI : MulDistribMulAction K S :=
        Subgroup.conjMulDistribMulActionOfLeNormalizer K S hKnormS
      External.Higman.Theorem1IsomorphicSummands K S)
    (hKW_fixed_point_free : ∀ d : G, d ∈ K ⊔ W → d ≠ 1 →
      ∀ x : G, x ∈ Q → x ∉ Q0 →
        rightConjugateElem x d * x⁻¹ ∉ Q0)
    (hSQ : S = Q) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E) (_ : CharP E 2)
        (F : Subfield E)
        (theta : F ≃+* F) (sigma : E ≃+* E)
        (phi : E → E → E)
        (K1 W1 : Subgroup Eˣ)
        (S1 : Type) (_ : Group S1)
        (coord : S1 ≃
          {p : E × E //
            (theta = 1 ∧ p.2 + sigma p.2 = p.1 * sigma p.1) ∨
              (theta ≠ 1 ∧ p.2 ∈ F)})
        (rho : (K ⊔ W : Subgroup G) →* MulAut S)
        (rho1 : (K1 ⊔ W1 : Subgroup Eˣ) →* MulAut S1)
        (sIso : S ≃* S1)
        (kwIso : (K ⊔ W : Subgroup G) ≃* (K1 ⊔ W1 : Subgroup Eˣ))
        (modelIso :
          SemidirectProduct S (K ⊔ W : Subgroup G) rho ≃*
            SemidirectProduct S1 (K1 ⊔ W1 : Subgroup Eˣ) rho1),
      Module.finrank F E = 2 ∧
        Nat.card F = Nat.card Q0 ∧
        Odd (orderOf theta) ∧
        (∀ a : F, sigma (a : E) = (theta a : F)) ∧
        (theta = 1 → ∀ x : E, sigma x = x ^ Nat.card F) ∧
        (∀ a : Eˣ, a ∈ K1 ↔
          ∃ b : Fˣ, (a : E) = ((b : F) : E)) ∧
        W1 ≠ ⊥ ∧
        (∀ a : Eˣ, a ∈ W1 → (a : E) ^ (Nat.card F + 1) = 1) ∧
        (∀ a : Eˣ, a ∈ W1 → sigma (a : E) = (a : E)⁻¹) ∧
        (theta = 1 → ∀ x y : E, phi x y = x * sigma y) ∧
        (theta ≠ 1 →
          (∀ x y : E, phi x y ∈ F) ∧
          (∀ x y z : E, phi (x + y) z = phi x z + phi y z) ∧
          (∀ x y z : E, phi x (y + z) = phi x y + phi x z) ∧
          (∀ a b : F, ∀ x y : E,
            phi ((a : E) * x) ((b : E) * y) =
              (a : E) * (theta b : F) * phi x y) ∧
          (∀ x : E, x ≠ 0 → phi x x ≠ 0)) ∧
        (∀ x y : S1,
          ((coord (x * y) :
              {p : E × E //
                (theta = 1 ∧ p.2 + sigma p.2 = p.1 * sigma p.1) ∨
              (theta ≠ 1 ∧ p.2 ∈ F)}) : E × E) =
            ((coord x).1.1 + (coord y).1.1,
              (coord x).1.2 + (coord y).1.2 + phi (coord x).1.1 (coord y).1.1)) ∧
        (∀ a : (K ⊔ W : Subgroup G), ∀ x : S,
          ((rho a x : S) : G) =
            (a : G) * (x : G) * (a : G)⁻¹) ∧
        (∀ a : (K1 ⊔ W1 : Subgroup Eˣ), ∀ x : S1,
          ((coord (rho1 a⁻¹ x) :
              {p : E × E //
                (theta = 1 ∧ p.2 + sigma p.2 = p.1 * sigma p.1) ∨
              (theta ≠ 1 ∧ p.2 ∈ F)}) : E × E) =
            (((a : Eˣ) : E) * (coord x).1.1,
              ((a : Eˣ) : E) * sigma ((a : Eˣ) : E) * (coord x).1.2)) ∧
        (∀ x : S,
          modelIso (SemidirectProduct.inl x) =
            SemidirectProduct.inl (sIso x)) ∧
        (∀ a : (K ⊔ W : Subgroup G),
          modelIso (SemidirectProduct.inr a) =
            SemidirectProduct.inr (kwIso a)) ∧
        Subgroup.map kwIso.toMonoidHom (K.subgroupOf (K ⊔ W)) =
          K1.subgroupOf (K1 ⊔ W1) ∧
        Subgroup.map kwIso.toMonoidHom (W.subgroupOf (K ⊔ W)) =
          W1.subgroupOf (K1 ⊔ W1) ∧
        ∃ hs : s ∈ S,
          ((coord (sIso ⟨s, hs⟩) :
              {p : E × E //
                (theta = 1 ∧ p.2 + sigma p.2 = p.1 * sigma p.1) ∨
              (theta ≠ 1 ∧ p.2 ∈ F)}) : E × E) = (0, 1) := by
  classical
  have hVleD : V ≤ D := by
    intro x hxV
    rw [hsection3.1.V_eq] at hxV
    exact hxV.1
  have hWleD : W ≤ D := hsection3.1.W_le_V.trans hVleD
  letI : (Q.subgroupOf H).Normal := hsection3.1.hA.A1.Q_normal_in_H
  have hHnormQ : H ≤ Subgroup.normalizer (Q : Set G) :=
    Subgroup.le_normalizer_of_normal_subgroupOf hsection3.1.hA.A1.Q_le_H
  have hDnormS : D ≤ Subgroup.normalizer (S : Set G) := by
    rw [hSQ]
    exact hsection3.1.hA.A1.D_le_H.trans hHnormQ
  have hKWnormS : K ⊔ W ≤ Subgroup.normalizer (S : Set G) :=
    sup_le (hsection3.1.K_le_D.trans hDnormS) (hWleD.trans hDnormS)
  letI : Subgroup.Normalizes (K ⊔ W) S := ⟨hKWnormS⟩
  let rhoActual : (K ⊔ W : Subgroup G) →* MulAut S :=
    MulDistribMulAction.toMulAut (K ⊔ W : Subgroup G) S
  have hrhoActual : ∀ a : (K ⊔ W : Subgroup G), ∀ x : S,
      ((rhoActual a x : S) : G) =
        (a : G) * (x : G) * (a : G)⁻¹ := by
    intro a x
    simp [rhoActual,
      Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
  have htypeBNotCommutative : ¬ IsMulCommutative S :=
    typeB_not_isMulCommutative S hC2.S_type_B
  have hKcyclic : IsCyclic K :=
    (PFchapter1section2.proposition_2
      H D Q K V W Q0 S Q1 t hsection3.1).1
  obtain ⟨hKnormS, hKfaithful, hKregular⟩ :=
    actualK_action_on_S H D Q K S t s hsection3.1.hA
      hsection3.1.K_le_D hsection3.1.K_def hsection3.2.1
      hsection3.2.2.1 hsection3.2.2.2 hSQ
  letI : Subgroup.Normalizes K S := ⟨hKnormS⟩
  rcases hIsoPackage with ⟨_hIsoKnormS, hIso⟩
  have hsQ0 : s ∈ Q0 :=
    (hsection3.1.Q0_def s).mpr
      (Or.inr ⟨hsection3.2.1, hsection3.2.2.1⟩)
  have hsS : s ∈ S := by
    rw [hSQ]
    exact hsection3.1.Q0_le_Q hsQ0
  let sS : S := ⟨s, hsS⟩
  have hsInvS : IsInvolution sS := by
    exact ⟨fun hsOne => hsection3.2.2.1.ne_one
        (congrArg (fun z : S => (z : G)) hsOne),
      Subtype.ext hsection3.2.2.1.sq_eq_one⟩
  obtain ⟨k0, hk0K, hk0ne⟩ :=
    PFchapter1section2.proposition_1_b_K_nontrivial
      H D Q K V W Q0 S Q1 t hsection3.1
  let k0K : K := ⟨k0, hk0K⟩
  let sK : S := k0K • sS
  have hsKInv : IsInvolution sK := hKregular.1 sS hsInvS k0K
  have hsKne : sS ≠ sK := by
    intro hEq
    rcases hKregular.2 sS hsInvS sS hsInvS with ⟨a, ha, haUnique⟩
    have hOne : (1 : K) = a := haUnique 1 (by simp)
    have hk0 : k0K = a := haUnique k0K (by simpa [sK] using hEq)
    have hk0One : k0 = 1 := by
      have : k0K = 1 := hk0.trans hOne.symm
      exact congrArg (fun z : K => (z : G)) this
    exact hk0ne hk0One
  have hS_suzuki : IsSuzukiTwoGroup S :=
    ⟨typeB_card_is_two_power hC2.S_type_B,
      htypeBNotCommutative,
      ⟨sS, sK, hsInvS, hsKInv, hsKne⟩,
      ⟨K, inferInstance, inferInstance, hKcyclic, hKfaithful, hKregular⟩⟩
  have hHigmanCoordinates :=
    higmanTheorem_isomorphic_summands_scalar_coordinates
      hS_suzuki hKcyclic hKfaithful hKregular hIso
  obtain ⟨nH, hnH, thetaH, eK, eQ, eZ, hperiodH,
      hKquotient, hKcenter⟩ := hHigmanCoordinates
  have hQ0CenterCard : Nat.card Q0 = Nat.card (Subgroup.center S) :=
    q0_card_eq_center_card H Q Q0 S hsection3.1.hA.A1.Q_le_H
      hsection3.1.Q0_le_Q hsection3.1.Q0_def hSQ hS_suzuki
  have hcenterCardH :
      Nat.card (Subgroup.center S) = Nat.card (BinaryGaloisField nH) := by
    simpa [Multiplicative] using Nat.card_congr eZ.toEquiv
  have hcardH_Q0 : Nat.card (BinaryGaloisField nH) = Nat.card Q0 :=
    hcenterCardH.symm.trans hQ0CenterCard.symm
  let quotientAction : (K ⊔ W : Subgroup G) →*
      Multiplicative (AddAut (BinaryGaloisField nH × BinaryGaloisField nH)) :=
    (MulAutMultiplicative
      (BinaryGaloisField nH × BinaryGaloisField nH)).toMonoidHom.comp
      ((MulAut.congr eQ).toMonoidHom.comp
        ((centerQuotientAction S).comp rhoActual))
  let qact (a : (K ⊔ W : Subgroup G)) (v : BinaryGaloisField nH × BinaryGaloisField nH) :=
    ((quotientAction a).toAdd : AddAut (BinaryGaloisField nH × BinaryGaloisField nH)) v
  let qAction (a : (K ⊔ W : Subgroup G)) : AddAut (BinaryGaloisField nH × BinaryGaloisField nH) :=
    (quotientAction a).toAdd
  let qact (a : (K ⊔ W : Subgroup G)) (v : BinaryGaloisField nH × BinaryGaloisField nH) :=
    ((quotientAction a).toAdd : AddAut (BinaryGaloisField nH × BinaryGaloisField nH)) v
  let kIncl : K →* (K ⊔ W : Subgroup G) :=
    Subgroup.inclusion le_sup_left
  let wIncl : W →* (K ⊔ W : Subgroup G) :=
    Subgroup.inclusion le_sup_right
  have hquotientAction_mk (a : (K ⊔ W : Subgroup G)) (x : S) :
      quotientAction a
          (eQ (QuotientGroup.mk' (Subgroup.center S) x)).toAdd =
        (eQ (QuotientGroup.mk' (Subgroup.center S)
          (rhoActual a x))).toAdd := by
    change (eQ ((centerQuotientAction S (rhoActual a))
      (eQ.symm (eQ (QuotientGroup.mk' (Subgroup.center S) x))))).toAdd =
        (eQ (QuotientGroup.mk' (Subgroup.center S) (rhoActual a x))).toAdd
    rw [eQ.symm_apply_apply]
    rfl
  have hKAction_mk (k : K) (x : S) :
      quotientAction (kIncl k)
          (eQ (QuotientGroup.mk' (Subgroup.center S) x)).toAdd =
        ((eK k : BinaryGaloisField nH) *
            (eQ (QuotientGroup.mk' (Subgroup.center S) x)).toAdd.1,
          (eK k : BinaryGaloisField nH) *
            (eQ (QuotientGroup.mk' (Subgroup.center S) x)).toAdd.2) := by
    rw [hquotientAction_mk]
    have haction : rhoActual (kIncl k) x = k • x := by
      apply Subtype.ext
      simp [rhoActual, kIncl,
        Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
    rw [haction]
    exact hKquotient k x
  have hKAction (k : K) (v : BinaryGaloisField nH × BinaryGaloisField nH) :
      quotientAction (kIncl k) v =
        ((eK k : BinaryGaloisField nH) * v.1,
          (eK k : BinaryGaloisField nH) * v.2) := by
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (Subgroup.center S)
      (eQ.symm (Multiplicative.ofAdd v))
    have h := hKAction_mk k x
    rw [hx] at h
    simpa using h
  have hWcentralizesK : W ≤ Subgroup.centralizer (K : Set G) := by
    rw [hsection3.1.W_eq, peterfalviW]
    exact inf_le_right
  have hWKcommute (w : W) (k : K) :
      wIncl w * kIncl k = kIncl k * wIncl w := by
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (hWcentralizesK w.property)
      (k : G) k.property).symm
  have hWAction_smul (w : W) (a : BinaryGaloisField nH)
      (v : BinaryGaloisField nH × BinaryGaloisField nH) :
      quotientAction (wIncl w) (a • v) =
        a • quotientAction (wIncl w) v := by
    by_cases ha : a = 0
    · subst a
      simp
    · let aUnit : (BinaryGaloisField nH)ˣ := Units.mk0 a ha
      obtain ⟨k, hk⟩ := eK.surjective aUnit
      have hcomm := congrArg quotientAction (hWKcommute w k)
      have hv : quotientAction (wIncl w) (quotientAction (kIncl k) v) =
          quotientAction (kIncl k) (quotientAction (wIncl w) v) := by
        calc
          quotientAction (wIncl w) (quotientAction (kIncl k) v) =
              (quotientAction (wIncl w) * quotientAction (kIncl k)) v := by
            simp
          _ = quotientAction (wIncl w * kIncl k) v := by simp
          _ = quotientAction (kIncl k * wIncl w) v := by rw [hWKcommute w k]
          _ = (quotientAction (kIncl k) * quotientAction (wIncl w)) v := by simp
          _ = quotientAction (kIncl k) (quotientAction (wIncl w) v) := by simp
      have hka : (eK k : BinaryGaloisField nH) = a := by
        simpa [aUnit] using congrArg Units.val hk
      rw [hKAction, hKAction, hka] at hv
      rcases v with ⟨v1, v2⟩
      apply Prod.ext
      · have hfst := congrArg Prod.fst hv
        simpa [Prod.smul_mk, smul_eq_mul] using hfst
      · have hsnd := congrArg Prod.snd hv
        simpa [Prod.smul_mk, smul_eq_mul] using hsnd
  let wLinear (w : W) :
      (BinaryGaloisField nH × BinaryGaloisField nH) ≃ₗ[BinaryGaloisField nH]
        (BinaryGaloisField nH × BinaryGaloisField nH) :=
    { (quotientAction (wIncl w)) with
      map_smul' := hWAction_smul w }
  obtain ⟨w0, hw0gen⟩ := IsCyclic.exists_generator (α := W)
  have hw0ne : w0 ≠ 1 := by
    obtain ⟨w, hwne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hC2.W_ne_bot
    intro hw0
    apply hwne
    rcases hw0gen w with ⟨m, hm⟩
    simpa [hw0] using hm.symm
  have hKinfW : K ⊓ W = ⊥ :=
    K_inf_W_eq_bot D K V W t hsection3.1.hA.A1.D_odd
      hsection3.1.hA.A1.involution_t hsection3.1.K_le_D
      hsection3.1.K_def hsection3.1.V_eq hsection3.1.W_le_V
  have hKW_no_fixed_vector :
      ∀ a : (K ⊔ W : Subgroup G), a ≠ 1 →
        ∀ v : BinaryGaloisField nH × BinaryGaloisField nH, v ≠ 0 →
          quotientAction a v ≠ v := by
    intro a haNe v hv hfix
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (Subgroup.center S)
      (eQ.symm (Multiplicative.ofAdd v))
    have hxCoord :
        (eQ (QuotientGroup.mk' (Subgroup.center S) x)).toAdd = v := by
      rw [hx, eQ.apply_symm_apply]
      rfl
    have hxNotCenter : x ∉ Subgroup.center S := by
      intro hxCenter
      apply hv
      have hxOne : QuotientGroup.mk' (Subgroup.center S) x = 1 :=
        (QuotientGroup.eq_one_iff x).mpr hxCenter
      have hzero :
          (eQ (QuotientGroup.mk' (Subgroup.center S) x)).toAdd = 0 := by
        rw [hxOne]
        simp
      exact hxCoord.symm.trans hzero
    have hquotFix :
        QuotientGroup.mk' (Subgroup.center S) (rhoActual a x) =
          QuotientGroup.mk' (Subgroup.center S) x := by
      apply eQ.injective
      apply Multiplicative.toAdd.injective
      have hact := hquotientAction_mk a x
      rw [hxCoord] at hact
      exact (hact.symm.trans hfix).trans hxCoord.symm
    have hcenterDiff : rhoActual a x * x⁻¹ ∈ Subgroup.center S := by
      simpa [div_eq_mul_inv] using
        (QuotientGroup.eq_iff_div_mem (N := Subgroup.center S)).mp hquotFix
    let d : G := ((a⁻¹ : (K ⊔ W : Subgroup G)) : G)
    have hdKW : d ∈ K ⊔ W := (a⁻¹).property
    have hdne : d ≠ 1 := by
      intro hdOne
      apply haNe
      have : a⁻¹ = 1 := Subtype.ext hdOne
      simpa using congrArg Inv.inv this
    have hxQ : (x : G) ∈ Q := by
      rw [← hSQ]
      exact x.property
    have hxNotQ0 : (x : G) ∉ Q0 := by
      intro hxQ0
      exact hxNotCenter ((q0_mem_iff_center H Q Q0 S
        hsection3.1.hA.A1.Q_le_H hsection3.1.Q0_le_Q
        hsection3.1.Q0_def hSQ hS_suzuki x).mp hxQ0)
    have hdiffQ0 :
        rightConjugateElem (x : G) d * (x : G)⁻¹ ∈ Q0 := by
      have hdiffCenter :
          (rhoActual a x * x⁻¹ : S) ∈ Subgroup.center S := hcenterDiff
      have hdiffQ0' := (q0_mem_iff_center H Q Q0 S
        hsection3.1.hA.A1.Q_le_H hsection3.1.Q0_le_Q
        hsection3.1.Q0_def hSQ hS_suzuki (rhoActual a x * x⁻¹)).mpr
          hdiffCenter
      convert hdiffQ0' using 1
      have hconjEq : rightConjugateElem (x : G) d =
          ((rhoActual a x : S) : G) := by
        rw [hrhoActual]
        simp [d, rightConjugateElem, mul_assoc]
      rw [hconjEq]
      rfl
    exact (hKW_fixed_point_free d hdKW hdne (x : G) hxQ hxNotQ0) hdiffQ0
  have hW_no_eigenline :
      ∀ w : W, w ≠ 1 →
        ∀ v : BinaryGaloisField nH × BinaryGaloisField nH, v ≠ 0 →
          ∀ a : BinaryGaloisField nH, wLinear w v ≠ a • v := by
    intro w hwne v hv a hEigen
    change quotientAction (wIncl w) v = a • v at hEigen
    by_cases ha : a = 0
    · subst a
      apply hv
      apply (quotientAction (wIncl w)).injective
      simpa using hEigen
    · let aUnit : (BinaryGaloisField nH)ˣ := Units.mk0 a ha
      obtain ⟨k, hk⟩ := eK.surjective aUnit
      have hka : (eK k : BinaryGaloisField nH) = a := by
        simpa [aUnit] using congrArg Units.val hk
      have hWvK : quotientAction (wIncl w) v =
          quotientAction (kIncl k) v := by
        rw [hKAction, hka]
        exact hEigen
      let dKW : (K ⊔ W : Subgroup G) := wIncl w * (kIncl k)⁻¹
      have hdFix : quotientAction dKW v = v := by
        have hcommInv := hWKcommute w k⁻¹
        have hcommInvV : quotientAction (wIncl w) (quotientAction (kIncl k⁻¹) v) =
            quotientAction (kIncl k⁻¹) (quotientAction (wIncl w) v) := by
          calc
            quotientAction (wIncl w) (quotientAction (kIncl k⁻¹) v) =
                (quotientAction (wIncl w) * quotientAction (kIncl k⁻¹)) v := by
              simp
            _ = quotientAction (wIncl w * kIncl k⁻¹) v := by simp
            _ = quotientAction (kIncl k⁻¹ * wIncl w) v := by rw [hcommInv]
            _ = (quotientAction (kIncl k⁻¹) * quotientAction (wIncl w)) v := by simp
            _ = quotientAction (kIncl k⁻¹) (quotientAction (wIncl w) v) := by simp
        calc
          quotientAction dKW v = quotientAction (wIncl w)
              (quotientAction ((kIncl k)⁻¹) v) := by
            simp [dKW]
          _ = quotientAction ((kIncl k)⁻¹)
              (quotientAction (wIncl w) v) := by
            simpa using hcommInvV
          _ = quotientAction ((kIncl k)⁻¹)
              (quotientAction (kIncl k) v) :=
            congrArg (quotientAction ((kIncl k)⁻¹)) hWvK
          _ = v := by simp
      have hdKWne : dKW ≠ 1 := by
        intro hdOne
        have hwk : wIncl w = kIncl k := by
          exact mul_inv_eq_one.mp hdOne
        have hwK : (w : G) ∈ K := by
          have hval := congrArg (fun z : (K ⊔ W : Subgroup G) => (z : G)) hwk
          have hval' : (w : G) = (k : G) := by
            simpa [wIncl, kIncl, Subgroup.inclusion] using hval
          change (w : G) ∈ K
          rw [hval']
          exact k.property
        have hwInf : (w : G) ∈ K ⊓ W := ⟨hwK, w.property⟩
        rw [hKinfW] at hwInf
        apply hwne
        apply Subtype.ext
        simpa using hwInf
      exact hKW_no_fixed_vector dKW hdKWne v hv hdFix
  have hw0_no_eigenline :
      ∀ v : BinaryGaloisField nH × BinaryGaloisField nH, v ≠ 0 →
        ∀ a : BinaryGaloisField nH, wLinear w0 v ≠ a • v :=
    hW_no_eigenline w0 hw0ne
  have hKnormW : K ≤ Subgroup.normalizer (W : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      have hcomm : k * w = w * k :=
        Subgroup.mem_centralizer_iff.mp (hWcentralizesK hw) k hk
      rw [hcomm, mul_inv_cancel_right]
      exact hw
    · intro hwConj
      have hcomm :
          k * (k * w * k⁻¹) = (k * w * k⁻¹) * k :=
        Subgroup.mem_centralizer_iff.mp (hWcentralizesK hwConj) k hk
      have hconj : k * w * k⁻¹ = w := by
        apply mul_left_cancel
        calc
          k * (k * w * k⁻¹) = (k * w * k⁻¹) * k := hcomm
          _ = k * w := by simp [mul_assoc]
      rw [hconj] at hwConj
      exact hwConj
  have hKW_decomp (a : (K ⊔ W : Subgroup G)) :
      ∃ k : K, ∃ w : W, a = kIncl k * wIncl w := by
    have ha : (a : G) ∈ (↑(K ⊔ W) : Set G) := a.property
    rw [Subgroup.coe_mul_of_left_le_normalizer_right K W hKnormW] at ha
    obtain ⟨k, hk, w, hw, hkw⟩ := ha
    refine ⟨⟨k, hk⟩, ⟨w, hw⟩, ?_⟩
    apply Subtype.ext
    exact hkw.symm
  have hWcentralizesKW :
      W ≤ Subgroup.centralizer ((K ⊔ W : Subgroup G) : Set G) := by
    intro w hw
    apply Subgroup.mem_centralizer_iff.mpr
    intro a ha
    let aKW : (K ⊔ W : Subgroup G) := ⟨a, ha⟩
    obtain ⟨k, z, haEq⟩ := hKW_decomp aKW
    have hkw : (k : G) * (w : G) = (w : G) * (k : G) := by
      exact (Subgroup.mem_centralizer_iff.mp (hWcentralizesK hw)
        (k : G) k.property)
    letI : CommGroup W := hWcyclic.commGroup
    have hzw : (z : G) * (w : G) = (w : G) * (z : G) := by
      exact congrArg (fun x : W => (x : G))
        (mul_comm z ⟨w, hw⟩)
    have haVal : a = (k : G) * (z : G) := by
      simpa [aKW, kIncl, wIncl, Subgroup.inclusion] using
        congrArg (fun x : (K ⊔ W : Subgroup G) => (x : G)) haEq
    change a * w = w * a
    rw [haVal]
    calc
      ((k : G) * (z : G)) * w = (k : G) * ((z : G) * w) := mul_assoc _ _ _
      _ = (k : G) * (w * (z : G)) := by rw [hzw]
      _ = ((k : G) * w) * (z : G) := (mul_assoc _ _ _).symm
      _ = (w * (k : G)) * (z : G) := by rw [hkw]
      _ = w * ((k : G) * (z : G)) := mul_assoc _ _ _
  have hKWAction_smul (a : (K ⊔ W : Subgroup G))
      (c : BinaryGaloisField nH)
      (v : BinaryGaloisField nH × BinaryGaloisField nH) :
      quotientAction a (c • v) = c • quotientAction a v := by
    obtain ⟨k, w, rfl⟩ := hKW_decomp a
    simp only [map_mul]
    change quotientAction (kIncl k) (quotientAction (wIncl w) (c • v)) =
      c • quotientAction (kIncl k) (quotientAction (wIncl w) v)
    rw [hWAction_smul, hKAction, hKAction]
    apply Prod.ext <;> dsimp <;> ring
  let kwLinear (a : (K ⊔ W : Subgroup G)) :
      (BinaryGaloisField nH × BinaryGaloisField nH) ≃ₗ[BinaryGaloisField nH]
        (BinaryGaloisField nH × BinaryGaloisField nH) :=
    { (quotientAction a) with
      map_smul' := hKWAction_smul a }
  let kwLinearGL : (K ⊔ W : Subgroup G) →*
      LinearMap.GeneralLinearGroup (BinaryGaloisField nH)
        (BinaryGaloisField nH × BinaryGaloisField nH) :=
    { toFun := fun a => LinearMap.GeneralLinearGroup.ofLinearEquiv (kwLinear a)
      map_one' := by
        apply Units.ext
        apply LinearMap.ext
        intro v
        change (Multiplicative.toAdd (quotientAction 1)) v = v
        rw [map_one]
        rfl
      map_mul' := by
        intro a b
        apply Units.ext
        apply LinearMap.ext
        intro v
        change (Multiplicative.toAdd (quotientAction (a * b))) v =
          (Multiplicative.toAdd (quotientAction a))
            ((Multiplicative.toAdd (quotientAction b)) v)
        rw [map_mul]
        rfl }
  have hActorComm (a : (K ⊔ W : Subgroup G)) :
      a * wIncl w0 = wIncl w0 * a := by
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp
      (hWcentralizesKW w0.property) (a : G) a.property
  have hkwLinearGL_injective : Function.Injective kwLinearGL := by
    intro a b hab
    by_contra hne
    let d : (K ⊔ W : Subgroup G) := a * b⁻¹
    have hdne : d ≠ 1 := by
      intro hd
      apply hne
      exact mul_inv_eq_one.mp hd
    have hdOne : kwLinearGL d = 1 := by
      change kwLinearGL (a * b⁻¹) = 1
      rw [map_mul, map_inv, hab]
      simp
    let v : BinaryGaloisField nH × BinaryGaloisField nH := (1, 0)
    have hv : v ≠ 0 := by simp [v]
    have hfix : (Multiplicative.toAdd (quotientAction d)) v = v := by
      have h := congrArg
        (fun g : LinearMap.GeneralLinearGroup (BinaryGaloisField nH)
          (BinaryGaloisField nH × BinaryGaloisField nH) => g.1 v) hdOne
      simpa [kwLinearGL, kwLinear, Multiplicative.toAdd,
        Multiplicative.ofAdd] using h
    exact hKW_no_fixed_vector d hdne v hv hfix
  have hActorNoEigen :
      ∀ v : BinaryGaloisField nH × BinaryGaloisField nH, v ≠ 0 →
        ∀ c : BinaryGaloisField nH,
          (kwLinearGL (wIncl w0)).1 v ≠ c • v := by
    simpa [kwLinearGL, kwLinear, wLinear] using hw0_no_eigenline
  obtain ⟨Eact, hEactField, hEactFinite, hEactAlgebra,
      quotientFieldEquiv, kwUnits, hEactFinrank, hkwUnitsInjective,
      hkwUnitsAction⟩ :=
    cyclic_irreducible_plane_field_model kwLinearGL (wIncl w0)
      hActorComm hActorNoEigen hkwLinearGL_injective
  let Actor := (K ⊔ W : Subgroup G)
  let K1 : Subgroup Eactˣ :=
    Subgroup.map kwUnits (K.subgroupOf Actor)
  let W1 : Subgroup Eactˣ :=
    Subgroup.map kwUnits (W.subgroupOf Actor)
  have hActorSup :
      K.subgroupOf Actor ⊔ W.subgroupOf Actor = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right]
    exact Subgroup.subgroupOf_self Actor
  have hkwUnitsRange : kwUnits.range = K1 ⊔ W1 := by
    calc
      kwUnits.range = Subgroup.map kwUnits (⊤ : Subgroup Actor) :=
        MonoidHom.range_eq_map kwUnits
      _ = Subgroup.map kwUnits
          (K.subgroupOf Actor ⊔ W.subgroupOf Actor) := by rw [hActorSup]
      _ = K1 ⊔ W1 := by rw [Subgroup.map_sup]
  let kwIso : Actor ≃* (K1 ⊔ W1 : Subgroup Eactˣ) :=
    (MonoidHom.ofInjective hkwUnitsInjective).trans
      (MulEquiv.subgroupCongr hkwUnitsRange)
  have hkwIso_val (a : Actor) :
      ((kwIso a : (K1 ⊔ W1 : Subgroup Eactˣ)) : Eactˣ) = kwUnits a := by
    simp [kwIso, MonoidHom.ofInjective_apply]
    rfl
  have hkwIso_comp :
      (K1 ⊔ W1 : Subgroup Eactˣ).subtype.comp kwIso.toMonoidHom =
        kwUnits := by
    apply MonoidHom.ext
    intro a
    exact hkwIso_val a
  have hmapK :
      Subgroup.map kwIso.toMonoidHom (K.subgroupOf Actor) =
        K1.subgroupOf (K1 ⊔ W1) := by
    apply Subgroup.map_injective
      (K1 ⊔ W1 : Subgroup Eactˣ).subtype_injective
    rw [Subgroup.map_map, hkwIso_comp,
      Subgroup.map_subgroupOf_eq_of_le le_sup_left]
  have hmapW :
      Subgroup.map kwIso.toMonoidHom (W.subgroupOf Actor) =
        W1.subgroupOf (K1 ⊔ W1) := by
    apply Subgroup.map_injective
      (K1 ⊔ W1 : Subgroup Eactˣ).subtype_injective
    rw [Subgroup.map_map, hkwIso_comp,
      Subgroup.map_subgroupOf_eq_of_le le_sup_right]
  let Fint : IntermediateField (BinaryGaloisField nH) Eact := ⊥
  let F : Subfield Eact := Fint.toSubfield
  letI : Fintype Eact := Fintype.ofFinite Eact
  letI : Module.Finite (BinaryGaloisField nH) Eact :=
    Module.Finite.equiv quotientFieldEquiv.symm
  letI : CharP Eact 2 :=
    charP_of_injective_algebraMap
      (algebraMap (BinaryGaloisField nH) Eact).injective 2
  letI : Algebra (ZMod 2) Eact := ZMod.algebra Eact 2
  letI : Fintype F := Fintype.ofFinite F
  have hfinrankFEact : Module.finrank F Eact = 2 := by
    simpa [F, Fint] using hEactFinrank
  let baseEquiv : F ≃+* BinaryGaloisField nH :=
    (IntermediateField.botEquiv (BinaryGaloisField nH) Eact).toRingEquiv
  have hcardF : Nat.card F = Nat.card Q0 := by
    calc
      Nat.card F = Nat.card (BinaryGaloisField nH) :=
        Nat.card_congr baseEquiv.toEquiv
      _ = Nat.card Q0 := hcardH_Q0
  let theta : F ≃+* F :=
    baseEquiv.trans (thetaH.trans baseEquiv.symm)
  have htheta_intertwine (a : F) :
      baseEquiv (theta a) = thetaH (baseEquiv a) := by
    simp [theta]
  have hthetaOdd : Odd (orderOf theta) := by
    obtain ⟨r, hrOdd, _hrPos, hr⟩ := hperiodH
    have hsemi : Function.Semiconj baseEquiv theta thetaH :=
      htheta_intertwine
    have hthetaIter : ∀ a : F, theta^[r] a = a := by
      intro a
      apply baseEquiv.injective
      rw [hsemi.iterate_right r, hr]
    apply hrOdd.of_dvd_nat
    apply (orderOf_dvd_iff_pow_eq_one).2
    apply DFunLike.ext _ _
    intro a
    simpa using hthetaIter a
  let scalarUnits : (BinaryGaloisField nH)ˣ →* Eactˣ :=
    Units.map (algebraMap (BinaryGaloisField nH) Eact)
  have hkwUnitsK (k : K) :
      (kwUnits (kIncl k) : Eact) =
        algebraMap (BinaryGaloisField nH) Eact (eK k : BinaryGaloisField nH) := by
    apply quotientFieldEquiv.injective
    have haction := hkwUnitsAction (kIncl k) 1
    change quotientFieldEquiv ((kwUnits (kIncl k) : Eact) * 1) =
      quotientAction (kIncl k) (quotientFieldEquiv 1) at haction
    have hscalar := quotientFieldEquiv.map_smul
      (eK k : BinaryGaloisField nH) (1 : Eact)
    rw [Algebra.smul_def, mul_one] at hscalar
    rw [hKAction] at haction
    simpa [Prod.smul_mk] using haction.trans hscalar.symm
  have hK1_scalar : K1 = scalarUnits.range := by
    ext u
    constructor
    · intro hu
      rcases Subgroup.mem_map.mp hu with ⟨a, ha, rfl⟩
      let k : K := ⟨(a : G), ha⟩
      refine ⟨eK k, ?_⟩
      apply Units.ext
      have haIncl : a = kIncl k := by
        apply Subtype.ext
        rfl
      rw [haIncl]
      simpa [scalarUnits] using (hkwUnitsK k).symm
    · rintro ⟨b, rfl⟩
      let k : K := eK.symm b
      refine Subgroup.mem_map.mpr ⟨kIncl k, ?_, ?_⟩
      · exact k.property
      · apply Units.ext
        simpa [k, scalarUnits] using hkwUnitsK k
  let scalarUnitsF : Fˣ →* Eactˣ := Units.map F.subtype
  let baseUnitsEquiv : (BinaryGaloisField nH)ˣ ≃* Fˣ :=
    Units.mapEquiv baseEquiv.symm.toMulEquiv
  have hscalarComp :
      scalarUnitsF.comp baseUnitsEquiv.toMonoidHom = scalarUnits := by
    ext b
    change (((IntermediateField.botEquiv (BinaryGaloisField nH) Eact).symm
      (b : BinaryGaloisField nH) :
        (⊥ : IntermediateField (BinaryGaloisField nH) Eact)) : Eact) =
      algebraMap (BinaryGaloisField nH) Eact (b : BinaryGaloisField nH)
    rw [IntermediateField.botEquiv_symm]
    exact IntermediateField.coe_algebraMap_apply (S :=
      (⊥ : IntermediateField (BinaryGaloisField nH) Eact))
      (b : BinaryGaloisField nH)
  have hscalarRanges : scalarUnits.range = scalarUnitsF.range := by
    ext u
    constructor
    · rintro ⟨b, rfl⟩
      refine ⟨baseUnitsEquiv b, ?_⟩
      exact DFunLike.congr_fun hscalarComp b
    · rintro ⟨b, rfl⟩
      refine ⟨baseUnitsEquiv.symm b, ?_⟩
      have h := DFunLike.congr_fun hscalarComp (baseUnitsEquiv.symm b)
      simpa using h.symm
  have hK1 : ∀ a : Eactˣ, a ∈ K1 ↔
      ∃ b : Fˣ, (a : Eact) = ((b : F) : Eact) := by
    intro a
    rw [hK1_scalar, hscalarRanges]
    constructor
    · rintro ⟨b, hb⟩
      refine ⟨b, ?_⟩
      exact congrArg Units.val hb.symm
    · rintro ⟨b, hb⟩
      refine ⟨b, ?_⟩
      apply Units.ext
      exact hb.symm
  have hW1ne : W1 ≠ ⊥ := by
    intro hW1bot
    have hWsubBot : W.subgroupOf Actor = ⊥ := by
      apply (Subgroup.map_eq_bot_iff_of_injective
        (W.subgroupOf Actor) hkwUnitsInjective).mp
      simpa [W1] using hW1bot
    apply hC2.W_ne_bot
    rw [eq_bot_iff]
    intro w hw
    let wActor : Actor := ⟨w, Subgroup.mem_sup_right hw⟩
    have hwSub : wActor ∈ W.subgroupOf Actor := hw
    rw [hWsubBot] at hwSub
    simpa [wActor] using hwSub
  have hActorInf :
      K.subgroupOf Actor ⊓ W.subgroupOf Actor = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    have haInf : (a : G) ∈ K ⊓ W := ⟨ha.1, ha.2⟩
    rw [hKinfW] at haInf
    simpa using haInf
  have hK1infW1 : K1 ⊓ W1 = ⊥ := by
    change Subgroup.map kwUnits (K.subgroupOf Actor) ⊓
      Subgroup.map kwUnits (W.subgroupOf Actor) = ⊥
    rw [← Subgroup.map_inf _ _ kwUnits hkwUnitsInjective,
      hActorInf, Subgroup.map_bot]
  let wQuot : W1 →* Eactˣ ⧸ K1 :=
    (QuotientGroup.mk' K1).comp W1.subtype
  have hwQuotInjective : Function.Injective wQuot := by
    apply (MonoidHom.ker_eq_bot_iff wQuot).mp
    rw [eq_bot_iff]
    intro w hw
    have hwK1 : (w : Eactˣ) ∈ K1 := by
      have hwOne := MonoidHom.mem_ker.mp hw
      change QuotientGroup.mk' K1 (w : Eactˣ) = 1 at hwOne
      exact (QuotientGroup.eq_one_iff (N := K1) (w : Eactˣ)).mp hwOne
    have hwInf : (w : Eactˣ) ∈ K1 ⊓ W1 := ⟨hwK1, w.property⟩
    rw [hK1infW1] at hwInf
    apply Subtype.ext
    simpa using hwInf
  have hW1cardDivQuot : Nat.card W1 ∣ Nat.card (Eactˣ ⧸ K1) :=
    Subgroup.card_dvd_of_injective wQuot hwQuotInjective
  have hcardEact : Nat.card Eact = Nat.card F ^ 2 := by
    calc
      Nat.card Eact = Nat.card (BinaryGaloisField nH) ^ 2 := by
        rw [Module.natCard_eq_pow_finrank
          (K := BinaryGaloisField nH) (V := Eact), hEactFinrank]
      _ = Nat.card F ^ 2 := by
        rw [Nat.card_congr baseEquiv.toEquiv]
  have hscalarUnitsFInjective : Function.Injective scalarUnitsF := by
    intro a b hab
    apply Units.ext
    apply F.subtype_injective
    exact congrArg Units.val hab
  have hcardK1 : Nat.card K1 = Nat.card F - 1 := by
    rw [hK1_scalar, hscalarRanges]
    calc
      Nat.card scalarUnitsF.range = Nat.card Fˣ :=
        (Nat.card_congr
          (Equiv.ofInjective scalarUnitsF hscalarUnitsFInjective)).symm
      _ = Nat.card F - 1 := Nat.card_units F
  have hcardQuot : Nat.card (Eactˣ ⧸ K1) = Nat.card F + 1 := by
    exact card_quotient_units_eq_add_one K1 (Nat.card F)
      Finite.one_lt_card hcardEact hcardK1
  have hW1cardDiv : Nat.card W1 ∣ Nat.card F + 1 := by
    rw [← hcardQuot]
    exact hW1cardDivQuot
  have hW1norm : ∀ a : Eactˣ, a ∈ W1 →
      (a : Eact) ^ (Nat.card F + 1) = 1 := by
    intro a ha
    obtain ⟨m, hm⟩ := hW1cardDiv
    let aW : W1 := ⟨a, ha⟩
    have hpow : aW ^ (Nat.card F + 1) = 1 := by
      rw [hm, pow_mul, pow_card_eq_one', one_pow]
    exact congrArg (fun u : W1 => ((u : Eactˣ) : Eact)) hpow
  have hcenterExp : ∀ z : Subgroup.center S, z ^ 2 = 1 :=
    (higmanTheorem_involutions_center hS_suzuki).2
  have hquotientData :=
    higmanTheorem_center_quotient_orders_and_exponent hS_suzuki
  letI : IsMulCommutative (S ⧸ Subgroup.center S) := hquotientData.1
  obtain ⟨qCenter, hqCenterOne, hqCenterSquare, hqCenterPolarLeft,
      _hqCenterPolarRight⟩ :=
    lemma1a_square_induces_quadratic
      (External.Higman.isPGroup_of_isSuzukiTwoGroup hS_suzuki)
      (Subgroup.center S) le_rfl
      ⟨hcenterExp, by
        intro x y
        exact Subtype.ext
          (Subgroup.mem_center_iff.mp x.property (y : S)).symm⟩
      ⟨hquotientData.2.1, by
        intro x y
        exact (isMulCommutative_iff.mp hquotientData.1) x y⟩
  let fieldToQuot : Multiplicative Eact ≃* S ⧸ Subgroup.center S :=
    quotientFieldEquiv.toAddEquiv.toMultiplicative.trans eQ.symm
  let baseAdd : BinaryGaloisField nH →+ Eact :=
    (algebraMap (BinaryGaloisField nH) Eact).toAddMonoidHom
  let centerToField : Subgroup.center S →* Multiplicative Eact :=
    baseAdd.toMultiplicative.comp eZ.toMonoidHom
  let qCoord : Multiplicative Eact → Multiplicative Eact := fun x =>
    centerToField (qCenter (fieldToQuot x))
  have hqCoordOne : qCoord 1 = 1 := by
    simp [qCoord, hqCenterOne]
  have hqCoordPolarLeft : ∀ x₁ x₂ y : Multiplicative Eact,
      qCoord ((x₁ * x₂) * y) * (qCoord (x₁ * x₂))⁻¹ * (qCoord y)⁻¹ =
        (qCoord (x₁ * y) * (qCoord x₁)⁻¹ * (qCoord y)⁻¹) *
          (qCoord (x₂ * y) * (qCoord x₂)⁻¹ * (qCoord y)⁻¹) := by
    intro x₁ x₂ y
    simpa only [qCoord] using
      transport_multiplicative_polar_identity fieldToQuot centerToField
        qCenter hqCenterPolarLeft x₁ x₂ y
  obtain ⟨qActual, hqActual⟩ :=
    quadraticMap_of_multiplicative_polar qCoord hqCoordOne hqCoordPolarLeft
  let qBase : Eact → BinaryGaloisField nH := fun x =>
    (eZ (qCenter (fieldToQuot (Multiplicative.ofAdd x)))).toAdd
  have hqActual_base (x : Eact) :
      qActual x = algebraMap (BinaryGaloisField nH) Eact (qBase x) := by
    rw [hqActual]
    rfl
  have hqActual_memF (x : Eact) : qActual x ∈ F := by
    rw [hqActual_base]
    change algebraMap (BinaryGaloisField nH) Eact (qBase x) ∈
      (algebraMap (BinaryGaloisField nH) Eact).fieldRange
    exact ⟨qBase x, rfl⟩
  let piActual : S →* Multiplicative Eact :=
    fieldToQuot.symm.toMonoidHom.comp
      (QuotientGroup.mk' (Subgroup.center S))
  have hpiActual_apply (x : S) :
      piActual x = fieldToQuot.symm
        (QuotientGroup.mk' (Subgroup.center S) x) := rfl
  have hpiActual_surjective : Function.Surjective piActual :=
    fieldToQuot.symm.surjective.comp
      (QuotientGroup.mk'_surjective (Subgroup.center S))
  have hpiActual_action (a : Actor) (x : S) :
      piActual (rhoActual a x) =
        Multiplicative.ofAdd ((kwUnits a : Eact) * (piActual x).toAdd) := by
    apply fieldToQuot.injective
    dsimp [piActual]
    rw [fieldToQuot.apply_symm_apply]
    change QuotientGroup.mk' (Subgroup.center S) (rhoActual a x) =
      eQ.symm (Multiplicative.ofAdd
        (quotientFieldEquiv ((kwUnits a : Eact) * (piActual x).toAdd)))
    rw [hkwUnitsAction]
    change QuotientGroup.mk' (Subgroup.center S) (rhoActual a x) =
      eQ.symm (Multiplicative.ofAdd
        (quotientAction a (quotientFieldEquiv (piActual x).toAdd)))
    have hxCoord : quotientFieldEquiv (piActual x).toAdd =
        (eQ (QuotientGroup.mk' (Subgroup.center S) x)).toAdd := by
      simp [piActual, fieldToQuot]
    rw [hxCoord, hquotientAction_mk]
    simp
  let iotaBase : Multiplicative (BinaryGaloisField nH) →* S :=
    (Subgroup.center S).subtype.comp eZ.symm.toMonoidHom
  have hiotaBase_injective : Function.Injective iotaBase :=
    (Subgroup.center S).subtype_injective.comp eZ.symm.injective
  have hqBase_square (x : S) :
      iotaBase (Multiplicative.ofAdd (qBase (piActual x).toAdd)) = x ^ 2 := by
    simpa [iotaBase, qBase, piActual, fieldToQuot] using hqCenterSquare x
  have hrhoActualK (k : K) (x : S) : rhoActual (kIncl k) x = k • x := by
    apply Subtype.ext
    simp [rhoActual, kIncl,
      Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
  have hKcenterBase (k : K) (z : BinaryGaloisField nH) :
      rhoActual (kIncl k) (iotaBase (Multiplicative.ofAdd z)) =
        iotaBase (Multiplicative.ofAdd
          ((eK k : BinaryGaloisField nH) * thetaH (eK k : BinaryGaloisField nH) * z)) := by
    rw [hrhoActualK]
    simpa [iotaBase] using hKcenter k z
  have hWfixCenter (w : W) (z : Subgroup.center S) :
      rhoActual (wIncl w) (z : S) = (z : S) := by
    have hzQ0 : ((z : S) : G) ∈ Q0 :=
      (q0_mem_iff_center H Q Q0 S hsection3.1.hA.A1.Q_le_H
        hsection3.1.Q0_le_Q hsection3.1.Q0_def hSQ hS_suzuki (z : S)).mpr
        z.property
    rcases (hsection3.1.Q0_def ((z : S) : G)).mp hzQ0 with hzOne | hzInv
    · have hzOneS : (z : S) = 1 := Subtype.ext hzOne
      rw [hzOneS]
      simp
    · have hWeq :=
        PFchapter1section2.peterfalvi_chapter1_section2_proposition_3_appendixI_input_W_eq_D_centralizer_involutions
          H D Q K V W t hsection3.1.hA.A1 hsection3.1.K_def
          hsection3.1.V_eq hsection3.1.W_eq
      have hwCent : (w : G) ∈
          Subgroup.centralizer ({x : G | x ∈ H ∧ IsInvolution x}) :=
        (hWeq.le w.property).2
      have hcomm : (w : G) * ((z : S) : G) =
          ((z : S) : G) * (w : G) :=
        Subgroup.mem_centralizer_iff.mp hwCent ((z : S) : G) hzInv |>.symm
      apply Subtype.ext
      rw [hrhoActual]
      change (w : G) * ((z : S) : G) * (w : G)⁻¹ = ((z : S) : G)
      rw [hcomm, mul_inv_cancel_right]
  have hWcenterBase (w : W) (z : BinaryGaloisField nH) :
      rhoActual (wIncl w) (iotaBase (Multiplicative.ofAdd z)) =
        iotaBase (Multiplicative.ofAdd z) := by
    simpa [iotaBase] using hWfixCenter w (eZ.symm (Multiplicative.ofAdd z))
  have hqBaseK (k : K) (x : Eact) :
      qBase ((kwUnits (kIncl k) : Eact) * x) =
        (eK k : BinaryGaloisField nH) * thetaH (eK k : BinaryGaloisField nH) *
          qBase x := by
    obtain ⟨s0, hs0⟩ := hpiActual_surjective (Multiplicative.ofAdd x)
    have hcoord := hpiActual_action (kIncl k) s0
    rw [hs0] at hcoord
    change piActual (rhoActual (kIncl k) s0) =
      Multiplicative.ofAdd ((kwUnits (kIncl k) : Eact) * x) at hcoord
    apply Multiplicative.ofAdd.injective
    apply hiotaBase_injective
    calc
      iotaBase (Multiplicative.ofAdd
          (qBase ((kwUnits (kIncl k) : Eact) * x))) =
          iotaBase (Multiplicative.ofAdd
            (qBase (piActual (rhoActual (kIncl k) s0)).toAdd)) := by
              rw [hcoord]
              simp
      _ = (rhoActual (kIncl k) s0) ^ 2 := hqBase_square _
      _ = rhoActual (kIncl k) (s0 ^ 2) := by rw [map_pow]
      _ = rhoActual (kIncl k)
          (iotaBase (Multiplicative.ofAdd (qBase x))) := by
            rw [← hqBase_square s0, hs0]
            simp
      _ = iotaBase (Multiplicative.ofAdd
          ((eK k : BinaryGaloisField nH) *
            thetaH (eK k : BinaryGaloisField nH) * qBase x)) :=
        hKcenterBase k (qBase x)
  have hqBaseW (w : W) (x : Eact) :
      qBase ((kwUnits (wIncl w) : Eact) * x) = qBase x := by
    obtain ⟨s0, hs0⟩ := hpiActual_surjective (Multiplicative.ofAdd x)
    have hcoord := hpiActual_action (wIncl w) s0
    rw [hs0] at hcoord
    change piActual (rhoActual (wIncl w) s0) =
      Multiplicative.ofAdd ((kwUnits (wIncl w) : Eact) * x) at hcoord
    apply Multiplicative.ofAdd.injective
    apply hiotaBase_injective
    calc
      iotaBase (Multiplicative.ofAdd
          (qBase ((kwUnits (wIncl w) : Eact) * x))) =
          iotaBase (Multiplicative.ofAdd
            (qBase (piActual (rhoActual (wIncl w) s0)).toAdd)) := by
              rw [hcoord]
              simp
      _ = (rhoActual (wIncl w) s0) ^ 2 := hqBase_square _
      _ = rhoActual (wIncl w) (s0 ^ 2) := by rw [map_pow]
      _ = rhoActual (wIncl w)
          (iotaBase (Multiplicative.ofAdd (qBase x))) := by
            rw [← hqBase_square s0, hs0]
            simp
      _ = iotaBase (Multiplicative.ofAdd (qBase x)) :=
        hWcenterBase w (qBase x)
  have hqActualK (k : K) (x : Eact) :
      qActual ((kwUnits (kIncl k) : Eact) * x) =
        algebraMap (BinaryGaloisField nH) Eact
            (eK k : BinaryGaloisField nH) *
          algebraMap (BinaryGaloisField nH) Eact
            (thetaH (eK k : BinaryGaloisField nH)) * qActual x := by
    rw [hqActual_base, hqBaseK, map_mul, map_mul, hqActual_base]
  have hqActualW (w : W) (x : Eact) :
      qActual ((kwUnits (wIncl w) : Eact) * x) = qActual x := by
    rw [hqActual_base, hqBaseW, hqActual_base]
  have hbaseCoe (a : F) :
      (a : Eact) = algebraMap (BinaryGaloisField nH) Eact (baseEquiv a) := by
    let aBot : (⊥ : IntermediateField (BinaryGaloisField nH) Eact) :=
      ⟨(a : Eact), a.property⟩
    have ha := congrArg
      (fun z : (⊥ : IntermediateField (BinaryGaloisField nH) Eact) =>
        (z : Eact))
      ((IntermediateField.botEquiv
        (BinaryGaloisField nH) Eact).symm_apply_apply aBot)
    change algebraMap (BinaryGaloisField nH) Eact
        ((IntermediateField.botEquiv (BinaryGaloisField nH) Eact) aBot) =
      (aBot : Eact) at ha
    simpa [aBot, F, Fint, baseEquiv] using ha.symm
  have hqActual_scalar (a : F) (x : Eact) :
      qActual ((a : Eact) * x) =
        (a : Eact) * (theta a : Eact) * qActual x := by
    by_cases ha : a = 0
    · subst a
      simp
    · let aUnit : Fˣ := Units.mk0 a ha
      let k : K := eK.symm (baseUnitsEquiv.symm aUnit)
      have hkVal : (eK k : BinaryGaloisField nH) = baseEquiv a := by
        simp [k, aUnit, baseUnitsEquiv]
      have hkw : (kwUnits (kIncl k) : Eact) = (a : Eact) := by
        rw [hkwUnitsK, hkVal, ← hbaseCoe]
      have h := hqActualK k x
      rw [hkw, hkVal, ← hbaseCoe,
        ← htheta_intertwine, ← hbaseCoe] at h
      exact h
  have hqActual_anisotropic (x : Eact) (hx : x ≠ 0) :
      qActual x ≠ 0 := by
    intro hqZero
    have hqBaseZero : qBase x = 0 := by
      apply (algebraMap (BinaryGaloisField nH) Eact).injective
      rw [← hqActual_base, hqZero, map_zero]
    obtain ⟨s0, hs0⟩ := hpiActual_surjective (Multiplicative.ofAdd x)
    have hs0sq : s0 ^ 2 = 1 := by
      calc
        s0 ^ 2 = iotaBase
            (Multiplicative.ofAdd (qBase (piActual s0).toAdd)) :=
          (hqBase_square s0).symm
        _ = 1 := by rw [hs0]; simp; rw [hqBaseZero]; simp
    have hs0Center : s0 ∈ Subgroup.center S := by
      by_cases hs0One : s0 = 1
      · rw [hs0One]
        exact Subgroup.one_mem _
      · have hs0Inv : IsInvolution s0 := ⟨hs0One, hs0sq⟩
        have hs0Mem : s0 ∈ involutions S := hs0Inv
        rw [(higmanTheorem_involutions_center hS_suzuki).1] at hs0Mem
        exact hs0Mem.1
    have hpiOne : piActual s0 = 1 := by
      change fieldToQuot.symm
          (QuotientGroup.mk' (Subgroup.center S) s0) = 1
      have hquotOne :
          QuotientGroup.mk' (Subgroup.center S) s0 = 1 :=
        (QuotientGroup.eq_one_iff s0).mpr hs0Center
      rw [hquotOne]
      simp
    apply hx
    have hmx : Multiplicative.ofAdd x = 1 := hs0.symm.trans hpiOne
    simpa using congrArg Multiplicative.toAdd hmx
  let qScale : F := ⟨qActual 1, hqActual_memF 1⟩
  have hqScaleNe : qScale ≠ 0 := by
    intro hzero
    apply hqActual_anisotropic 1 one_ne_zero
    exact congrArg Subtype.val hzero
  have hqScaleE : (qScale : Eact) ≠ 0 :=
    subfield_coe_ne_zero_of_ne_zero F qScale hqScaleNe
  let qNorm : QuadraticMap (ZMod 2) Eact Eact :=
    (qScale⁻¹ : Eact) • qActual
  have hqNorm_eval (x : Eact) :
      qNorm x = (qScale⁻¹ : Eact) * qActual x := by
    rfl
  have hqNorm_one : qNorm 1 = 1 := by
    rw [hqNorm_eval]
    change (qScale⁻¹ : Eact) * (qScale : Eact) = 1
    rw [inv_mul_cancel₀ hqScaleE]
  have hqNorm_memF (x : Eact) : qNorm x ∈ F := by
    rw [hqNorm_eval]
    exact F.mul_mem (F.inv_mem qScale.property) (hqActual_memF x)
  have hqNorm_scalar (a : F) (x : Eact) :
      qNorm ((a : Eact) * x) =
        (a : Eact) * (theta a : Eact) * qNorm x := by
    rw [hqNorm_eval, hqActual_scalar, hqNorm_eval]
    ring
  have hqActualW1 (w : Eactˣ) (hw : w ∈ W1) (x : Eact) :
      qActual ((w : Eact) * x) = qActual x := by
    rcases Subgroup.mem_map.mp hw with ⟨a, ha, hwa⟩
    let z : W := ⟨(a : G), ha⟩
    have haIncl : a = wIncl z := by
      apply Subtype.ext
      rfl
    have hwVal : (w : Eact) = (kwUnits (wIncl z) : Eact) := by
      rw [← haIncl]
      exact congrArg Units.val hwa.symm
    rw [hwVal]
    exact hqActualW z x
  have hqNormW1 (w : Eactˣ) (hw : w ∈ W1) (x : Eact) :
      qNorm ((w : Eact) * x) = qNorm x := by
    rw [hqNorm_eval, hqActualW1 w hw, hqNorm_eval]
  have hqNorm_anisotropic (x : Eact) (hx : x ≠ 0) :
      qNorm x ≠ 0 := by
    rw [hqNorm_eval]
    exact mul_ne_zero (inv_ne_zero hqScaleE)
      (hqActual_anisotropic x hx)
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  letI : IsScalarTower (ZMod 2) F Eact :=
    IsScalarTower.of_algebraMap_eq (fun z =>
      DFunLike.congr_fun
        (RingHom.ext_zmod (algebraMap (ZMod 2) Eact)
          ((algebraMap F Eact).comp (algebraMap (ZMod 2) F))) z)
  letI : Fintype (Eact ≃+* Eact) :=
    Fintype.ofInjective (fun tau : Eact ≃+* Eact => (tau : Eact → Eact)) (by
      intro tau upsilon h
      ext x
      exact congrFun h x)
  letI : Fintype (F ≃+* F) :=
    Fintype.ofInjective (fun tau : F ≃+* F => (tau : F → F)) (by
      intro tau upsilon h
      ext x
      exact congrArg Subtype.val (congrFun h x))
  let asZModAlg (tau : Eact ≃+* Eact) : Eact ≃ₐ[ZMod 2] Eact :=
    AlgEquiv.ofRingEquiv (f := tau) (by
      intro z
      exact DFunLike.congr_fun
        (RingHom.ext_zmod
          (tau.toRingHom.comp (algebraMap (ZMod 2) Eact))
          (algebraMap (ZMod 2) Eact)) z)
  let restrictZMod : (Eact ≃ₐ[ZMod 2] Eact) →* (F ≃ₐ[ZMod 2] F) := by
    set_option backward.isDefEq.respectTransparency false in
      exact AlgEquiv.restrictNormalHom F
  let restrictAut (tau : Eact ≃+* Eact) : F ≃+* F :=
    (restrictZMod (asZModAlg tau)).toRingEquiv
  have hrestrictAut_apply (tau : Eact ≃+* Eact) (a : F) :
      tau (a : Eact) = (restrictAut tau a : F) := by
    set_option backward.isDefEq.respectTransparency false in
      change asZModAlg tau (algebraMap F Eact a) =
        algebraMap F Eact
          (((AlgEquiv.restrictNormalHom F) (asZModAlg tau)) a)
      exact (AlgEquiv.restrictNormal_commutes (asZModAlg tau) F a).symm
  let QIndex :=
    {u : Finset (Eact ≃+* Eact) // u.card = 1 ∨ u.card = 2}
  obtain ⟨quadBasis, hquadBasis⟩ :=
    lemma2c_fieldAutomorphism_products_basis_quadraticMaps Eact
  let qCoeff : QIndex → Eact := quadBasis.repr qNorm
  let qWeight (u : QIndex) (x : Eact) : Eact :=
    if u.1.card = 1 then
      (∏ tau ∈ u.1, tau x) ^ 2
    else ∏ tau ∈ u.1, tau x
  have hquadBasis_weight (u : QIndex) (x : Eact) :
      quadBasis u x = qWeight u x := by
    exact hquadBasis u x
  have hqNorm_sum :
      ∑ u : QIndex, qCoeff u • quadBasis u = qNorm := by
    exact quadBasis.sum_repr qNorm
  have hqNorm_expansion (x : Eact) :
      qNorm x = ∑ u : QIndex, qCoeff u * qWeight u x := by
    have hx := congrArg (fun q : QuadraticMap (ZMod 2) Eact Eact => q x)
      hqNorm_sum
    simpa [hquadBasis_weight, smul_eq_mul] using hx.symm
  have hqWeight_mul (u : QIndex) (a x : Eact) :
      qWeight u (a * x) = qWeight u a * qWeight u x := by
    by_cases hu : u.1.card = 1
    · simp only [qWeight, hu, if_pos, map_mul,
        Finset.prod_mul_distrib]
      ring
    · simp [qWeight, hu, map_mul, Finset.prod_mul_distrib]
  let mulZMod (a : Eact) : Eact →ₗ[ZMod 2] Eact :=
    LinearMap.mulLeft (ZMod 2) a
  have hqNorm_comp_expansion (a : Eact) :
      qNorm.comp (mulZMod a) =
        ∑ u : QIndex, (qCoeff u * qWeight u a) • quadBasis u := by
    ext x
    calc
      (qNorm.comp (mulZMod a)) x = qNorm (a * x) := by rfl
      _ = ∑ u : QIndex, qCoeff u * qWeight u (a * x) :=
        hqNorm_expansion _
      _ = ∑ u : QIndex,
          (qCoeff u * qWeight u a) * qWeight u x := by
        apply Finset.sum_congr rfl
        intro u hu
        rw [hqWeight_mul]
        ring
      _ = (∑ u : QIndex,
          (qCoeff u * qWeight u a) • quadBasis u) x := by
        simp [hquadBasis_weight, smul_eq_mul]
  have hqCoeff_scalar (u : QIndex) (hu : qCoeff u ≠ 0) (a : F) :
      qWeight u (a : Eact) = (a : Eact) * (theta a : Eact) := by
    have hmaps : qNorm.comp (mulZMod (a : Eact)) =
        ((a : Eact) * (theta a : Eact)) • qNorm := by
      ext x
      simpa [mulZMod, smul_eq_mul] using hqNorm_scalar a x
    have hcoeffEq :
        qCoeff u * qWeight u (a : Eact) =
          ((a : Eact) * (theta a : Eact)) * qCoeff u := by
      calc
        qCoeff u * qWeight u (a : Eact) =
            quadBasis.repr
              (∑ c : QIndex,
                (qCoeff c * qWeight c (a : Eact)) • quadBasis c) u := by
          have hrepr := quadBasis.repr_sum_self
            (fun c : QIndex => qCoeff c * qWeight c (a : Eact))
          exact (congrArg (fun f => f u) hrepr).symm
        _ = quadBasis.repr
            (((a : Eact) * (theta a : Eact)) • qNorm) u := by
          exact congrArg (fun q : QuadraticMap (ZMod 2) Eact Eact =>
            quadBasis.repr q u)
            ((hqNorm_comp_expansion (a : Eact)).symm.trans hmaps)
        _ = ((a : Eact) * (theta a : Eact)) * qCoeff u := by
          simp [qCoeff, smul_eq_mul]
    apply mul_left_cancel₀ hu
    calc
      qCoeff u * qWeight u (a : Eact) =
          ((a : Eact) * (theta a : Eact)) * qCoeff u := hcoeffEq
      _ = qCoeff u * ((a : Eact) * (theta a : Eact)) := by ring
  have hqCoeff_W (u : QIndex) (hu : qCoeff u ≠ 0)
      (w : Eactˣ) (hw : w ∈ W1) :
      qWeight u (w : Eact) = 1 := by
    have hmaps : qNorm.comp (mulZMod (w : Eact)) = qNorm := by
      ext x
      simpa [mulZMod] using hqNormW1 w hw x
    have hcoeffEq : qCoeff u * qWeight u (w : Eact) = qCoeff u := by
      calc
        qCoeff u * qWeight u (w : Eact) =
            quadBasis.repr
              (∑ c : QIndex,
                (qCoeff c * qWeight c (w : Eact)) • quadBasis c) u := by
          have hrepr := quadBasis.repr_sum_self
            (fun c : QIndex => qCoeff c * qWeight c (w : Eact))
          exact (congrArg (fun f => f u) hrepr).symm
        _ = quadBasis.repr qNorm u := by
          exact congrArg (fun q : QuadraticMap (ZMod 2) Eact Eact =>
            quadBasis.repr q u)
            ((hqNorm_comp_expansion (w : Eact)).symm.trans hmaps)
        _ = qCoeff u := by rfl
    apply mul_left_cancel₀ hu
    simpa using hcoeffEq
  let FQIndex := {u : Finset (F ≃+* F) // u.card = 1 ∨ u.card = 2}
  let restrictIndex (u : QIndex) : FQIndex :=
    ⟨u.1.image restrictAut, by
      have hnonempty : (u.1.image restrictAut).Nonempty := by
        apply Finset.Nonempty.image
        exact Finset.card_pos.mp (by omega : 0 < u.1.card)
      have hpos : 0 < (u.1.image restrictAut).card :=
        Finset.card_pos.mpr hnonempty
      have hle : (u.1.image restrictAut).card ≤ u.1.card :=
        Finset.card_image_le
      omega⟩
  let thetaIndex : FQIndex :=
    ⟨{1, theta}, Finset.card_pair_eq_one_or_two⟩
  obtain ⟨baseQuadBasis, hbaseQuadBasis⟩ :=
    lemma2c_fieldAutomorphism_products_basis_quadraticMaps F
  have hbaseQuadBasis_theta (a : F) :
      baseQuadBasis thetaIndex a = a * theta a := by
    rw [hbaseQuadBasis]
    by_cases htheta : theta = 1
    · simp [thetaIndex, htheta, pow_two]
    · have hcard : ({1, theta} : Finset (F ≃+* F)).card = 2 := by
        simpa using Finset.card_pair (Ne.symm htheta)
      rw [if_neg (by rw [hcard]; norm_num)]
      rw [Finset.prod_pair (Ne.symm htheta)]
      simp
  have hbaseQuadBasis_restrict (u : QIndex) (a : F) :
      (baseQuadBasis (restrictIndex u) a : Eact) =
        qWeight u (a : Eact) := by
    rw [hbaseQuadBasis]
    rcases u.2 with huCard | huCard
    · obtain ⟨tau, htau⟩ := Finset.card_eq_one.mp huCard
      have hu : u.1 = {tau} := htau
      simp [restrictIndex, qWeight, hu, hrestrictAut_apply, pow_two]
    · obtain ⟨tau, upsilon, hne, hpair⟩ := Finset.card_eq_two.mp huCard
      have hu : u.1 = {tau, upsilon} := hpair
      by_cases hr : restrictAut tau = restrictAut upsilon
      · simp [restrictIndex, qWeight, hu, hne, hr,
          hrestrictAut_apply, pow_two]
      · simp [restrictIndex, qWeight, hu, hne, hr,
          hrestrictAut_apply]
  have hqCoeff_restrict (u : QIndex) (hu : qCoeff u ≠ 0) :
      restrictIndex u = thetaIndex := by
    apply baseQuadBasis.injective
    ext a
    rw [hbaseQuadBasis_restrict, hqCoeff_scalar u hu,
      hbaseQuadBasis_theta]
    simp
  let barAlg : Eact ≃ₐ[F] Eact :=
    FiniteField.frobeniusAlgEquivOfAlgebraic F Eact
  let bar : Eact ≃+* Eact := barAlg.toRingEquiv
  have hbar_apply (x : Eact) :
      bar x = x ^ Nat.card F := by
    simp [bar, barAlg]
  have hbar_fixes (a : F) : bar (a : Eact) = (a : Eact) := by
    change barAlg (algebraMap F Eact a) = algebraMap F Eact a
    exact barAlg.commutes a
  have hbar_involutive : Function.Involutive bar := by
    have hbarAlgOrder : orderOf barAlg = 2 := by
      exact (FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic F Eact).trans
        hfinrankFEact
    have hbarSq : barAlg ^ 2 = 1 := by
      rw [← hbarAlgOrder]
      exact pow_orderOf_eq_one barAlg
    intro x
    have hx := DFunLike.congr_fun hbarSq x
    simpa [bar, pow_two] using hx
  have hbarW1 (w : Eactˣ) (hw : w ∈ W1) :
      bar (w : Eact) = (w : Eact)⁻¹ := by
    rw [hbar_apply]
    apply eq_inv_of_mul_eq_one_left
    simpa [pow_add] using hW1norm w hw
  obtain ⟨w0, hw0gen⟩ := IsCyclic.exists_generator (α := W1)
  have hw0ne : w0 ≠ 1 := by
    obtain ⟨w, hwne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hW1ne
    intro hw0
    apply hwne
    rcases hw0gen w with ⟨m, hm⟩
    simpa [hw0] using hm.symm
  let traceW : F := Algebra.trace F Eact ((w0 : Eactˣ) : Eact)
  have htraceW_coe :
      (traceW : Eact) = ((w0 : Eactˣ) : Eact) +
        ((w0 : Eactˣ) : Eact)⁻¹ := by
    calc
      (traceW : Eact) =
          ((w0 : Eactˣ) : Eact) +
            ((w0 : Eactˣ) : Eact) ^ Nat.card F := by
        change algebraMap F Eact
          (Algebra.trace F Eact ((w0 : Eactˣ) : Eact)) = _
        rw [FiniteField.algebraMap_trace_eq_sum_pow]
        convert (by
          norm_num [Finset.sum_range_succ, Nat.card_eq_fintype_card] :
            ∑ i ∈ Finset.range 2,
              ((w0 : Eactˣ) : Eact) ^ Nat.card F ^ i =
                ((w0 : Eactˣ) : Eact) +
                  ((w0 : Eactˣ) : Eact) ^ Nat.card F) using 1
        exact congrArg (fun n =>
          ∑ i ∈ Finset.range n,
            ((w0 : Eactˣ) : Eact) ^ Nat.card F ^ i) hfinrankFEact
      _ = ((w0 : Eactˣ) : Eact) +
          ((w0 : Eactˣ) : Eact)⁻¹ := by
        rw [← hbar_apply, hbarW1 (w0 : Eactˣ) w0.property]
  have hw0_sq :
      ((w0 : Eactˣ) : Eact) * ((w0 : Eactˣ) : Eact) =
        1 + (traceW : Eact) * ((w0 : Eactˣ) : Eact) := by
    rw [htraceW_coe, add_mul]
    rw [inv_mul_cancel₀ (Units.ne_zero (w0 : Eactˣ))]
    rw [show 1 +
        (((w0 : Eactˣ) : Eact) * ((w0 : Eactˣ) : Eact) + 1) =
          ((w0 : Eactˣ) : Eact) * ((w0 : Eactˣ) : Eact) +
            (1 + 1) by ring,
      CharTwo.add_self_eq_zero, add_zero]
  have hqNormPolarW1 (w : Eactˣ) (hw : w ∈ W1) (x y : Eact) :
      qNorm.polarBilin ((w : Eact) * x) ((w : Eact) * y) =
        qNorm.polarBilin x y := by
    change qNorm ((w : Eact) * x + (w : Eact) * y) -
        qNorm ((w : Eact) * x) - qNorm ((w : Eact) * y) =
      qNorm (x + y) - qNorm x - qNorm y
    rw [← mul_add, hqNormW1 w hw, hqNormW1 w hw, hqNormW1 w hw]
  have hqNormPolar_same (a b : F) (x : Eact) :
      qNorm.polarBilin ((a : Eact) * x) ((b : Eact) * x) =
        ((a : Eact) * (theta b : Eact) +
          (b : Eact) * (theta a : Eact)) * qNorm x := by
    change qNorm ((a : Eact) * x + (b : Eact) * x) -
        qNorm ((a : Eact) * x) - qNorm ((b : Eact) * x) = _
    rw [← add_mul]
    change qNorm (((a + b : F) : Eact) * x) -
        qNorm ((a : Eact) * x) - qNorm ((b : Eact) * x) = _
    rw [hqNorm_scalar, hqNorm_scalar, hqNorm_scalar, map_add]
    push_cast
    ring
  have htheta_traceW : theta traceW = traceW := by
    have hpolarInv := hqNormPolarW1 (w0 : Eactˣ) w0.property
      1 ((w0 : Eactˣ) : Eact)
    rw [mul_one, hw0_sq, map_add] at hpolarInv
    have hpolarZero :
        qNorm.polarBilin ((w0 : Eactˣ) : Eact)
          ((traceW : Eact) * ((w0 : Eactˣ) : Eact)) = 0 := by
      have hcomm : qNorm.polarBilin ((w0 : Eactˣ) : Eact) 1 =
          qNorm.polarBilin 1 ((w0 : Eactˣ) : Eact) :=
        QuadraticMap.polar_comm qNorm ((w0 : Eactˣ) : Eact) 1
      rw [hcomm] at hpolarInv
      exact add_eq_left.mp hpolarInv
    have hsame := hqNormPolar_same (1 : F) traceW
      ((w0 : Eactˣ) : Eact)
    have hqw0 : qNorm ((w0 : Eactˣ) : Eact) = 1 := by
      simpa [hqNorm_one] using hqNormW1 (w0 : Eactˣ) w0.property 1
    rw [hqw0, mul_one] at hsame
    have hsame' : qNorm.polarBilin ((w0 : Eactˣ) : Eact)
        ((traceW : Eact) * ((w0 : Eactˣ) : Eact)) =
      (theta traceW : Eact) + (traceW : Eact) := by
      simpa using hsame
    rw [hpolarZero] at hsame'
    have hsum : (theta traceW : Eact) + (traceW : Eact) = 0 :=
      hsame'.symm
    have hneg : (theta traceW : Eact) = -(traceW : Eact) :=
      eq_neg_of_add_eq_zero_left hsum
    apply Subtype.ext
    simpa only [ZModModule.neg_eq_self] using hneg
  let thetaAlg : F ≃ₐ[ZMod 2] F :=
    AlgEquiv.ofRingEquiv (f := theta) (by
      intro z
      exact DFunLike.congr_fun
        (RingHom.ext_zmod
          (theta.toRingHom.comp (algebraMap (ZMod 2) F))
          (algebraMap (ZMod 2) F)) z)
  have hrestrictZMod_surjective : Function.Surjective restrictZMod := by
    set_option backward.isDefEq.respectTransparency false in
      change Function.Surjective (AlgEquiv.restrictNormalHom F)
      exact AlgEquiv.restrictNormalHom_surjective
        (F := ZMod 2) (K₁ := F) Eact
  have hsigma0_exists : ∃ sigma0Alg : Eact ≃ₐ[ZMod 2] Eact,
      restrictZMod sigma0Alg = thetaAlg :=
    hrestrictZMod_surjective thetaAlg
  let sigma0Alg : Eact ≃ₐ[ZMod 2] Eact :=
    Classical.choose hsigma0_exists
  have hsigma0_restrict : restrictZMod sigma0Alg = thetaAlg :=
    Classical.choose_spec hsigma0_exists
  let sigma0 : Eact ≃+* Eact := sigma0Alg.toRingEquiv
  have hsigma0_ext (a : F) :
      sigma0 (a : Eact) = (theta a : Eact) := by
    calc
      sigma0 (a : Eact) =
          algebraMap F Eact ((restrictZMod sigma0Alg) a) := by
        set_option backward.isDefEq.respectTransparency false in
          change sigma0Alg (algebraMap F Eact a) =
            algebraMap F Eact
              (((AlgEquiv.restrictNormalHom F) sigma0Alg) a)
          exact (AlgEquiv.restrictNormal_commutes sigma0Alg F a).symm
      _ = algebraMap F Eact (thetaAlg a) := by rw [hsigma0_restrict]
      _ = (theta a : Eact) := rfl
  have hsigma0_trace :
      sigma0 ((w0 : Eactˣ) : Eact) +
          (sigma0 ((w0 : Eactˣ) : Eact))⁻¹ =
        (traceW : Eact) := by
    calc
      sigma0 ((w0 : Eactˣ) : Eact) +
          (sigma0 ((w0 : Eactˣ) : Eact))⁻¹ =
          sigma0 (((w0 : Eactˣ) : Eact) +
            ((w0 : Eactˣ) : Eact)⁻¹) := by
        rw [map_add, map_inv₀]
      _ = sigma0 (traceW : Eact) := by rw [htraceW_coe]
      _ = (theta traceW : Eact) := hsigma0_ext traceW
      _ = (traceW : Eact) := by rw [htheta_traceW]
  have hsigma0_w0 :
      sigma0 ((w0 : Eactˣ) : Eact) = ((w0 : Eactˣ) : Eact) ∨
        sigma0 ((w0 : Eactˣ) : Eact) =
          ((w0 : Eactˣ) : Eact)⁻¹ := by
    let y : Eact := sigma0 ((w0 : Eactˣ) : Eact)
    have hyNe : y ≠ 0 := by
      intro hy
      apply Units.ne_zero (w0 : Eactˣ)
      apply sigma0.injective
      simp [y] at hy
    have hyMul : y * y + 1 = (traceW : Eact) * y := by
      have h := congrArg (fun z : Eact => z * y) hsigma0_trace
      change (y + y⁻¹) * y = (traceW : Eact) * y at h
      rw [add_mul, inv_mul_cancel₀ hyNe] at h
      exact h
    have hyPoly : y * y + (traceW : Eact) * y + 1 = 0 := by
      calc
        y * y + (traceW : Eact) * y + 1 =
            (y * y + 1) + (traceW : Eact) * y := by ring
        _ = (traceW : Eact) * y + (traceW : Eact) * y := by rw [hyMul]
        _ = 0 := CharTwo.add_self_eq_zero _
    have hfactor :
        (y + ((w0 : Eactˣ) : Eact)) *
          (y + ((w0 : Eactˣ) : Eact)⁻¹) = 0 := by
      calc
        (y + ((w0 : Eactˣ) : Eact)) *
            (y + ((w0 : Eactˣ) : Eact)⁻¹) =
            y * y + (((w0 : Eactˣ) : Eact) +
              ((w0 : Eactˣ) : Eact)⁻¹) * y +
              ((w0 : Eactˣ) : Eact) *
                ((w0 : Eactˣ) : Eact)⁻¹ := by ring
        _ = y * y + (traceW : Eact) * y + 1 := by
          rw [← htraceW_coe, mul_inv_cancel₀ (Units.ne_zero (w0 : Eactˣ))]
        _ = 0 := hyPoly
    rcases mul_eq_zero.mp hfactor with h | h
    · left
      have hneg : y = -((w0 : Eactˣ) : Eact) :=
        eq_neg_of_add_eq_zero_left h
      simpa only [ZModModule.neg_eq_self] using hneg
    · right
      have hneg : y = -(((w0 : Eactˣ) : Eact)⁻¹) :=
        eq_neg_of_add_eq_zero_left h
      simpa only [ZModModule.neg_eq_self] using hneg
  let sigma : Eact ≃+* Eact :=
    if theta = 1 then bar
    else if sigma0 ((w0 : Eactˣ) : Eact) =
      ((w0 : Eactˣ) : Eact)⁻¹ then sigma0
    else sigma0.trans bar
  have hsigma_w0 : sigma ((w0 : Eactˣ) : Eact) =
      ((w0 : Eactˣ) : Eact)⁻¹ := by
    by_cases htheta : theta = 1
    · rw [show sigma = bar by simp [sigma, htheta]]
      exact hbarW1 (w0 : Eactˣ) w0.property
    · rw [show sigma = if sigma0 ((w0 : Eactˣ) : Eact) =
          ((w0 : Eactˣ) : Eact)⁻¹ then
          sigma0 else sigma0.trans bar by simp [sigma, htheta]]
      split_ifs with h
      · exact h
      · rcases hsigma0_w0 with hs | hs
        · change bar (sigma0 ((w0 : Eactˣ) : Eact)) =
            ((w0 : Eactˣ) : Eact)⁻¹
          rw [hs, hbarW1 (w0 : Eactˣ) w0.property]
        · exact (h hs).elim
  have hsigma_ext (a : F) : sigma (a : Eact) = (theta a : Eact) := by
    by_cases htheta : theta = 1
    · rw [show sigma = bar by simp [sigma, htheta], hbar_fixes, htheta]
      rfl
    · rw [show sigma = if sigma0 ((w0 : Eactˣ) : Eact) =
          ((w0 : Eactˣ) : Eact)⁻¹ then
          sigma0 else sigma0.trans bar by simp [sigma, htheta]]
      split_ifs
      · exact hsigma0_ext a
      · change bar (sigma0 (a : Eact)) = (theta a : Eact)
        rw [hsigma0_ext, hbar_fixes]
  have hsigma_frobenius (htheta : theta = 1) (x : Eact) :
      sigma x = x ^ Nat.card F := by
    rw [show sigma = bar by simp [sigma, htheta], hbar_apply]
  have hsigma_involutive (htheta : theta = 1) : Function.Involutive sigma := by
    rw [show sigma = bar by simp [sigma, htheta]]
    exact hbar_involutive
  have hsigmaW1 (w : Eactˣ) (hw : w ∈ W1) :
      sigma (w : Eact) = (w : Eact)⁻¹ := by
    let wW : W1 := ⟨w, hw⟩
    rcases hw0gen wW with ⟨m, hm⟩
    have hmE : (w : Eact) = ((w0 : Eactˣ) : Eact) ^ m := by
      simpa [wW] using
        (congrArg (fun u : W1 => ((u : Eactˣ) : Eact)) hm).symm
    calc
      sigma (w : Eact) = sigma (((w0 : Eactˣ) : Eact) ^ m) := by rw [hmE]
      _ = (sigma ((w0 : Eactˣ) : Eact)) ^ m :=
        map_zpow₀ sigma ((w0 : Eactˣ) : Eact) m
      _ = (((w0 : Eactˣ) : Eact)⁻¹) ^ m := by rw [hsigma_w0]
      _ = (((w0 : Eactˣ) : Eact) ^ m)⁻¹ := by rw [inv_zpow]
      _ = (w : Eact)⁻¹ := by rw [← hmE]
  have htheta_moved (htheta : theta ≠ 1) :
      ∃ c : F, theta c ≠ c := by
    by_contra! hfix
    apply htheta
    ext a
    exact congrArg Subtype.val (hfix a)
  let cTheta : F :=
    if htheta : theta = 1 then 0
    else Classical.choose (htheta_moved htheta)
  have hcTheta (htheta : theta ≠ 1) : theta cTheta ≠ cTheta := by
    simpa [cTheta, htheta] using
      (Classical.choose_spec (htheta_moved htheta))
  let dTheta : F := cTheta + theta cTheta
  have hdTheta (htheta : theta ≠ 1) : dTheta ≠ 0 := by
    intro hd
    apply hcTheta htheta
    have hneg : theta cTheta = -cTheta :=
      eq_neg_of_add_eq_zero_right hd
    simpa only [ZModModule.neg_eq_self] using hneg
  have hdThetaE (htheta : theta ≠ 1) : (dTheta : Eact) ≠ 0 :=
    subfield_coe_ne_zero_of_ne_zero F dTheta (hdTheta htheta)
  have hqNormPolar_memF (x y : Eact) :
      qNorm.polarBilin x y ∈ F := by
    change qNorm (x + y) - qNorm x - qNorm y ∈ F
    exact F.sub_mem (F.sub_mem (hqNorm_memF (x + y)) (hqNorm_memF x))
      (hqNorm_memF y)
  let phiTwisted (x y : Eact) : Eact :=
    (dTheta⁻¹ : Eact) *
      (qNorm.polarBilin ((cTheta : Eact) * x) y +
        (theta cTheta : Eact) * qNorm.polarBilin x y)
  have hphiTwisted_memF (x y : Eact) : phiTwisted x y ∈ F := by
    exact F.mul_mem (dTheta⁻¹).property
      (F.add_mem (hqNormPolar_memF ((cTheta : Eact) * x) y)
        (F.mul_mem (theta cTheta).property (hqNormPolar_memF x y)))
  have hphiTwisted_add_left (x y z : Eact) :
      phiTwisted (x + y) z = phiTwisted x z + phiTwisted y z :=
    (phi_twisted_additive_core qNorm (cTheta : Eact)
      (theta cTheta : Eact) (dTheta⁻¹ : Eact)).1 x y z
  have hphiTwisted_add_right (x y z : Eact) :
      phiTwisted x (y + z) = phiTwisted x y + phiTwisted x z :=
    (phi_twisted_additive_core qNorm (cTheta : Eact)
      (theta cTheta : Eact) (dTheta⁻¹ : Eact)).2 x y z
  have hphiTwisted_diag (htheta : theta ≠ 1) (x : Eact) :
      phiTwisted x x = qNorm x := by
    have hself : qNorm.polarBilin x x = 0 := by
      simp [two_smul, CharTwo.add_self_eq_zero, QuadraticMap.polar_self]
    have hsame := hqNormPolar_same cTheta (1 : F) x
    have hsame' : qNorm.polarBilin ((cTheta : Eact) * x) x =
        ((cTheta : Eact) + (theta cTheta : Eact)) * qNorm x := by
      convert hsame using 1 <;> simp
    dsimp [phiTwisted]
    change (dTheta⁻¹ : Eact) *
      (qNorm.polarBilin ((cTheta : Eact) * x) x +
        (theta cTheta : Eact) * qNorm.polarBilin x x) = qNorm x
    rw [hsame', hself, mul_zero, add_zero]
    change (dTheta⁻¹ : Eact) * ((dTheta : Eact) * qNorm x) = qNorm x
    rw [← mul_assoc, inv_mul_cancel₀]
    · simp
    · exact hdThetaE htheta
  have hqNorm_add (x y : Eact) :
      qNorm (x + y) = qNorm x + qNorm y + qNorm.polarBilin x y := by
    change qNorm (x + y) = qNorm x + qNorm y +
      (qNorm (x + y) - qNorm x - qNorm y)
    abel
  have hqNormPolar_cross (a b : F) (x y : Eact) :
      qNorm.polarBilin ((a : Eact) * x) ((b : Eact) * y) +
          qNorm.polarBilin ((a : Eact) * y) ((b : Eact) * x) =
        ((a : Eact) * (theta b : Eact) +
          (b : Eact) * (theta a : Eact)) * qNorm.polarBilin x y := by
    have hsum := hqNormPolar_same a b (x + y)
    have hx := hqNormPolar_same a b x
    have hy := hqNormPolar_same a b y
    rw [mul_add, mul_add, hqNorm_add] at hsum
    simp only [map_add, LinearMap.add_apply] at hsum
    linear_combination hsum - hx - hy
  have hqNormPolar_scale_sum (a : F) (x y : Eact) :
      qNorm.polarBilin ((a : Eact) * x) y +
          qNorm.polarBilin x ((a : Eact) * y) =
        ((a : Eact) + (theta a : Eact)) * qNorm.polarBilin x y := by
    have h := hqNormPolar_cross a (1 : F) x y
    have h' : qNorm.polarBilin ((a : Eact) * x) y +
        qNorm.polarBilin ((a : Eact) * y) x =
          ((a : Eact) + (theta a : Eact)) *
            qNorm.polarBilin x y := by
      simpa using h
    rw [show qNorm.polarBilin ((a : Eact) * y) x =
      qNorm.polarBilin x ((a : Eact) * y) from
        QuadraticMap.polar_comm qNorm ((a : Eact) * y) x] at h'
    exact h'
  have hphiTwisted_polar_decomp (htheta : theta ≠ 1)
      (a : F) (x y : Eact) :
      qNorm.polarBilin ((a : Eact) * x) y =
        (a : Eact) * phiTwisted x y +
          (theta a : Eact) * phiTwisted y x := by
    dsimp [phiTwisted]
    exact phi_twisted_polar_decomp_core F theta qNorm cTheta dTheta rfl
      (hdThetaE htheta) hqNormPolar_scale_sum hqNormPolar_cross a x y
  have hphiTwisted_smul_left (htheta : theta ≠ 1)
      (a : F) (x y : Eact) :
      phiTwisted ((a : Eact) * x) y =
        (a : Eact) * phiTwisted x y := by
    dsimp [phiTwisted]
    exact phi_twisted_smul_left_core F theta qNorm cTheta dTheta rfl
      (hdThetaE htheta) hqNormPolar_scale_sum hqNormPolar_cross a x y
  have hphiTwisted_polar (htheta : theta ≠ 1) (x y : Eact) :
      qNorm.polarBilin x y = phiTwisted x y + phiTwisted y x := by
    simpa using hphiTwisted_polar_decomp htheta (1 : F) x y
  have hphiTwisted_smul_right (htheta : theta ≠ 1)
      (a : F) (x y : Eact) :
      phiTwisted x ((a : Eact) * y) =
        (theta a : Eact) * phiTwisted x y := by
    have hp := hphiTwisted_polar htheta x ((a : Eact) * y)
    have hd := hphiTwisted_polar_decomp htheta a y x
    rw [show qNorm.polarBilin x ((a : Eact) * y) =
      qNorm.polarBilin ((a : Eact) * y) x from
        QuadraticMap.polar_comm qNorm x ((a : Eact) * y),
      hphiTwisted_smul_left htheta a y x] at hp
    apply add_left_cancel
    calc
      (a : Eact) * phiTwisted y x + phiTwisted x ((a : Eact) * y) =
          phiTwisted x ((a : Eact) * y) +
            (a : Eact) * phiTwisted y x := add_comm _ _
      _ = qNorm.polarBilin ((a : Eact) * y) x := hp.symm
      _ = (a : Eact) * phiTwisted y x +
          (theta a : Eact) * phiTwisted x y := hd
  have hphiTwisted_smul (htheta : theta ≠ 1)
      (a b : F) (x y : Eact) :
      phiTwisted ((a : Eact) * x) ((b : Eact) * y) =
        (a : Eact) * (theta b : Eact) * phiTwisted x y := by
    rw [hphiTwisted_smul_left htheta, hphiTwisted_smul_right htheta]
    ring
  have hphiTwistedW1 (w : Eactˣ) (hw : w ∈ W1) (x y : Eact) :
      phiTwisted ((w : Eact) * x) ((w : Eact) * y) =
        phiTwisted x y := by
    dsimp [phiTwisted]
    rw [show (cTheta : Eact) * ((w : Eact) * x) =
      (w : Eact) * ((cTheta : Eact) * x) by ring,
      show qNorm.polarBilin ((w : Eact) * ((cTheta : Eact) * x))
          ((w : Eact) * y) = qNorm.polarBilin ((cTheta : Eact) * x) y from
        hqNormPolarW1 w hw ((cTheta : Eact) * x) y,
      show qNorm.polarBilin ((w : Eact) * x) ((w : Eact) * y) =
          qNorm.polarBilin x y from hqNormPolarW1 w hw x y]
  let phi (x y : Eact) : Eact :=
    if theta = 1 then x * sigma y else phiTwisted x y
  have hphi_one (htheta : theta = 1) (x y : Eact) :
      phi x y = x * sigma y := by
    simp [phi, htheta]
  have hphi_memF (htheta : theta ≠ 1) (x y : Eact) : phi x y ∈ F := by
    simpa [phi, htheta] using hphiTwisted_memF x y
  have hphi_add_left (x y z : Eact) :
      phi (x + y) z = phi x z + phi y z := by
    by_cases htheta : theta = 1
    · simp [phi, htheta, add_mul]
    · simpa [phi, htheta] using hphiTwisted_add_left x y z
  have hphi_add_right (x y z : Eact) :
      phi x (y + z) = phi x y + phi x z := by
    by_cases htheta : theta = 1
    · simp [phi, htheta, mul_add]
    · simpa [phi, htheta] using hphiTwisted_add_right x y z
  have hphi_smul (htheta : theta ≠ 1) (a b : F) (x y : Eact) :
      phi ((a : Eact) * x) ((b : Eact) * y) =
        (a : Eact) * (theta b : Eact) * phi x y := by
    simpa [phi, htheta] using hphiTwisted_smul htheta a b x y
  have hphi_diag_ne (htheta : theta ≠ 1) (x : Eact) (hx : x ≠ 0) :
      phi x x ≠ 0 := by
    rw [show phi x x = phiTwisted x x by simp [phi, htheta],
      hphiTwisted_diag htheta]
    exact hqNorm_anisotropic x hx
  have hphiW1 (w : Eactˣ) (hw : w ∈ W1) (x y : Eact) :
      phi ((w : Eact) * x) ((w : Eact) * y) = phi x y := by
    by_cases htheta : theta = 1
    · simp only [hphi_one htheta, map_mul]
      rw [hsigmaW1 w hw]
      field_simp
    · simpa [phi, htheta] using hphiTwistedW1 w hw x y
  have hbar_ne_one : bar ≠ 1 := by
    intro hbarOne
    have hwInv : ((w0 : Eactˣ) : Eact) =
        ((w0 : Eactˣ) : Eact)⁻¹ := by
      calc
        ((w0 : Eactˣ) : Eact) = bar ((w0 : Eactˣ) : Eact) := by
          simp [hbarOne]
        _ = ((w0 : Eactˣ) : Eact)⁻¹ :=
          hbarW1 (w0 : Eactˣ) w0.property
    have hwSq : ((w0 : Eactˣ) : Eact) * ((w0 : Eactˣ) : Eact) = 1 := by
      calc
        ((w0 : Eactˣ) : Eact) * ((w0 : Eactˣ) : Eact) =
            ((w0 : Eactˣ) : Eact)⁻¹ * ((w0 : Eactˣ) : Eact) := by
          exact congrArg (fun z : Eact => z * ((w0 : Eactˣ) : Eact)) hwInv
        _ = 1 := inv_mul_cancel₀ (Units.ne_zero (w0 : Eactˣ))
    have hplusSq :
        (((w0 : Eactˣ) : Eact) + 1) *
          (((w0 : Eactˣ) : Eact) + 1) = 0 := by
      calc
        (((w0 : Eactˣ) : Eact) + 1) *
            (((w0 : Eactˣ) : Eact) + 1) =
          ((w0 : Eactˣ) : Eact) * ((w0 : Eactˣ) : Eact) +
            (((w0 : Eactˣ) : Eact) + ((w0 : Eactˣ) : Eact)) + 1 := by ring
        _ = 0 := by
          rw [hwSq, CharTwo.add_self_eq_zero]
          simpa only [add_zero] using
            (CharTwo.add_self_eq_zero (1 : Eact))
    have hplus : ((w0 : Eactˣ) : Eact) + 1 = 0 :=
      mul_self_eq_zero.mp hplusSq
    apply hw0ne
    apply Subtype.ext
    apply Units.ext
    have hneg : ((w0 : Eactˣ) : Eact) = -(1 : Eact) :=
      eq_neg_of_add_eq_zero_left hplus
    change ((w0 : Eactˣ) : Eact) = (1 : Eact)
    simpa only [ZModModule.neg_eq_self] using hneg
  have hAut_fixF (tau : Eact ≃+* Eact)
      (htau : restrictAut tau = 1) : tau = 1 ∨ tau = bar := by
    let tauF : Eact ≃ₐ[F] Eact :=
      AlgEquiv.ofRingEquiv (f := tau) (by
        intro a
        change tau (a : Eact) = (a : Eact)
        rw [hrestrictAut_apply, htau]
        rfl)
    obtain ⟨i, hi⟩ :=
      (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow
        F Eact).surjective tauF
    have hiLt : i.1 < 2 := by
      have hiBound : i.1 < Module.finrank F Eact := i.isLt
      simpa only [hfinrankFEact] using hiBound
    have hiCases : i.1 = 0 ∨ i.1 = 1 := by omega
    rcases hiCases with hiZero | hiOne
    · left
      apply DFunLike.ext _ _
      intro x
      have hx := DFunLike.congr_fun hi x
      simpa [hiZero, tauF] using hx.symm
    · right
      apply DFunLike.ext _ _
      intro x
      have hx := DFunLike.congr_fun hi x
      simpa [hiOne, tauF, bar, barAlg] using hx.symm
  let normIndex : QIndex :=
    ⟨{1, bar}, Or.inr (Finset.card_pair (Ne.symm hbar_ne_one))⟩
  have hqWeight_normIndex (x : Eact) :
      qWeight normIndex x = x * bar x := by
    rw [show qWeight normIndex x =
        if ({1, bar} : Finset (Eact ≃+* Eact)).card = 1 then
          (∏ tau ∈ ({1, bar} : Finset (Eact ≃+* Eact)), tau x) ^ 2
        else ∏ tau ∈ ({1, bar} : Finset (Eact ≃+* Eact)), tau x by rfl]
    have hcard : ({1, bar} : Finset (Eact ≃+* Eact)).card = 2 :=
      Finset.card_pair (Ne.symm hbar_ne_one)
    rw [if_neg (by rw [hcard]; norm_num),
      Finset.prod_pair (Ne.symm hbar_ne_one)]
    simp
  have hsquare_one_charTwo (z : Eact) (hz : z * z = 1) : z = 1 := by
    have hplusSq : (z + 1) * (z + 1) = 0 := by
      calc
        (z + 1) * (z + 1) = z * z + (z + z) + 1 := by ring
        _ = 0 := by
          rw [hz, CharTwo.add_self_eq_zero]
          simpa only [add_zero] using
            (CharTwo.add_self_eq_zero (1 : Eact))
    have hplus : z + 1 = 0 := mul_self_eq_zero.mp hplusSq
    have hneg : z = -(1 : Eact) := eq_neg_of_add_eq_zero_left hplus
    simpa only [ZModModule.neg_eq_self] using hneg
  have hqCoeff_norm_support (htheta : theta = 1)
      (u : QIndex) (hu : qCoeff u ≠ 0) : u = normIndex := by
    have hrestrictSet : u.1.image restrictAut = {1} := by
      have h := congrArg Subtype.val (hqCoeff_restrict u hu)
      simpa [restrictIndex, thetaIndex, htheta] using h
    have hrestrict (tau : Eact ≃+* Eact) (htau : tau ∈ u.1) :
        restrictAut tau = 1 := by
      have hm : restrictAut tau ∈ ({1} : Finset (F ≃+* F)) := by
        rw [← hrestrictSet]
        exact Finset.mem_image.mpr ⟨tau, htau, rfl⟩
      simpa using hm
    have huCardNeOne : u.1.card ≠ 1 := by
      intro huCard
      obtain ⟨tau, htau⟩ := Finset.card_eq_one.mp huCard
      have hw := hqCoeff_W u hu (w0 : Eactˣ) w0.property
      change (if u.1.card = 1 then
          (∏ rho ∈ u.1, rho ((w0 : Eactˣ) : Eact)) ^ 2
        else ∏ rho ∈ u.1, rho ((w0 : Eactˣ) : Eact)) = 1 at hw
      rw [if_pos huCard, htau] at hw
      simp only [Finset.prod_singleton, pow_two] at hw
      have htauOne : tau ((w0 : Eactˣ) : Eact) = 1 :=
        hsquare_one_charTwo _ hw
      apply hw0ne
      apply Subtype.ext
      apply Units.ext
      apply tau.injective
      simpa using htauOne
    have huCardTwo : u.1.card = 2 := u.2.resolve_left huCardNeOne
    obtain ⟨tau, upsilon, hne, hpair⟩ := Finset.card_eq_two.mp huCardTwo
    have htauMem : tau ∈ u.1 := by rw [hpair]; simp
    have hupsilonMem : upsilon ∈ u.1 := by rw [hpair]; simp
    rcases hAut_fixF tau (hrestrict tau htauMem) with htau | htau <;>
      rcases hAut_fixF upsilon (hrestrict upsilon hupsilonMem) with hups | hups
    · exact (hne (htau.trans hups.symm)).elim
    · apply Subtype.ext
      simp [hpair, normIndex, htau, hups]
    · apply Subtype.ext
      simp [hpair, normIndex, htau, hups, Finset.pair_comm]
    · exact (hne (htau.trans hups.symm)).elim
  have hqCoeff_zero_of_ne (htheta : theta = 1)
      (u : QIndex) (hne : u ≠ normIndex) : qCoeff u = 0 := by
    by_contra hu
    exact hne (hqCoeff_norm_support htheta u hu)
  have hqNorm_norm (htheta : theta = 1) (x : Eact) :
      qNorm x = x * bar x := by
    have hsum (z : Eact) :
        ∑ u : QIndex, qCoeff u * qWeight u z =
          qCoeff normIndex * qWeight normIndex z := by
      apply Finset.sum_eq_single normIndex
      · intro u hu hune
        rw [hqCoeff_zero_of_ne htheta u hune, zero_mul]
      · simp
    have hcoeff : qCoeff normIndex = 1 := by
      have hone := hqNorm_expansion 1
      rw [hqNorm_one, hsum] at hone
      simpa [hqWeight_normIndex] using hone.symm
    calc
      qNorm x = ∑ u : QIndex, qCoeff u * qWeight u x :=
        hqNorm_expansion x
      _ = qCoeff normIndex * qWeight normIndex x := hsum x
      _ = x * bar x := by rw [hcoeff, one_mul, hqWeight_normIndex]
  have hphi_diag (x : Eact) : phi x x = qNorm x := by
    by_cases htheta : theta = 1
    · rw [hphi_one htheta, show sigma x = bar x by
        rw [show sigma = bar by simp [sigma, htheta]]]
      exact (hqNorm_norm htheta x).symm
    · rw [show phi x x = phiTwisted x x by simp [phi, htheta],
        hphiTwisted_diag htheta]
  let Actor1 := (K1 ⊔ W1 : Subgroup Eactˣ)
  have hactorDecomp (a : Actor1) :
      ∃ (b : Fˣ) (w : Eactˣ), w ∈ W1 ∧
        ((a : Eactˣ) : Eact) = ((b : F) : Eact) * (w : Eact) := by
    rcases Subgroup.mem_sup.mp a.property with ⟨k, hk, w, hw, hkw⟩
    obtain ⟨b, hb⟩ := (hK1 k).mp hk
    refine ⟨b, w, hw, ?_⟩
    have hval := congrArg Units.val hkw
    change (k : Eact) * (w : Eact) = ((a : Eactˣ) : Eact) at hval
    rw [← hval, hb]
  have hactorNorm (a : Actor1) (htheta : theta ≠ 1) :
      ((a : Eactˣ) : Eact) * sigma ((a : Eactˣ) : Eact) ∈ F := by
    rcases hactorDecomp a with ⟨b, w, hw, ha⟩
    rw [ha, map_mul, hsigma_ext, hsigmaW1 w hw]
    convert F.mul_mem (b : F).property (theta (b : F)).property using 1
    field_simp
  have hphiScale (a : Actor1) (x y : Eact) :
      phi (((a : Eactˣ) : Eact) * x) (((a : Eactˣ) : Eact) * y) =
        ((a : Eactˣ) : Eact) * sigma ((a : Eactˣ) : Eact) * phi x y := by
    by_cases htheta : theta = 1
    · rw [hphi_one htheta, hphi_one htheta, map_mul]
      ring
    · rcases hactorDecomp a with ⟨b, w, hw, ha⟩
      calc
        phi (((a : Eactˣ) : Eact) * x) (((a : Eactˣ) : Eact) * y) =
            phi ((w : Eact) * (((b : F) : Eact) * x))
              ((w : Eact) * (((b : F) : Eact) * y)) := by
                rw [ha]
                congr 1 <;> ring
        _ = phi (((b : F) : Eact) * x) (((b : F) : Eact) * y) :=
          hphiW1 w hw _ _
        _ = ((b : F) : Eact) * (theta (b : F) : Eact) * phi x y :=
          hphi_smul htheta (b : F) (b : F) x y
        _ = ((a : Eactˣ) : Eact) * sigma ((a : Eactˣ) : Eact) * phi x y := by
          rw [ha, map_mul, hsigma_ext, hsigmaW1 w hw]
          field_simp
  obtain ⟨S1, groupS1, coord, rho1, hcoordMul, hrho1⟩ :=
    typeB_group_model Eact F theta sigma phi K1 W1
      hsigma_involutive hphi_one hphi_add_left hphi_add_right
      hphi_memF hactorNorm hphiScale
  letI : Group S1 := groupS1
  have htrace_formula (x : Eact) :
      (Algebra.trace F Eact x : Eact) = x + bar x := by
    change algebraMap F Eact (Algebra.trace F Eact x) = _
    rw [FiniteField.algebraMap_trace_eq_sum_pow]
    have hsum2 :
        ∑ i ∈ Finset.range 2, x ^ Nat.card F ^ i = x + bar x := by
      simp [Finset.sum_range_succ, hbar_apply]
    convert hsum2 using 1
    congr 2
  have hmemF_of_bar_fixed (x : Eact) (hx : bar x = x) : x ∈ F := by
    have hfixed : Function.IsFixedPt (barAlg : Eact → Eact) x := by
      have hx' : barAlg.toRingEquiv x = x := by
        simpa only [bar] using hx
      have hfun :
          (barAlg.toRingEquiv : Eact → Eact) = (barAlg : Eact → Eact) :=
        AlgEquiv.coe_ringEquiv barAlg
      change barAlg x = x
      rw [← hfun]
      exact hx'
    have hrange : x ∈ Set.range (algebraMap F Eact) := by
      apply (IsGalois.mem_range_algebraMap_iff_fixed x).2
      intro tau
      obtain ⟨i, rfl⟩ :=
        (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow
          F Eact).surjective tau
      have hiter := hfixed.iterate i.1
      change ((barAlg : Eact → Eact)^[i.1]) x = x at hiter
      change (barAlg ^ i.1) x = x
      rw [AlgEquiv.coe_pow]
      exact hiter
    rcases hrange with ⟨a, rfl⟩
    exact a.property
  have hphi_zero_left (z : Eact) : phi 0 z = 0 := by
    have h := hphi_add_left 0 0 z
    apply add_left_cancel (a := phi 0 z)
    simpa using h.symm
  have hphi_zero_right (z : Eact) : phi z 0 = 0 := by
    have h := hphi_add_right z 0 0
    apply add_left_cancel (a := phi z 0)
    simpa using h.symm
  have hcoord_one : ((coord (1 : S1)).1 : Eact × Eact) = (0, 0) := by
    have h := hcoordMul (1 : S1) (1 : S1)
    simp only [one_mul] at h
    have hfst := congrArg Prod.fst h
    have hfstZero : (coord (1 : S1)).1.1 = 0 := by
      have hdouble : (coord (1 : S1)).1.1 +
          (coord (1 : S1)).1.1 = 0 :=
        CharTwo.add_self_eq_zero _
      rw [show (coord (1 : S1)).1.1 =
        (coord (1 : S1)).1.1 + (coord (1 : S1)).1.1 from hfst]
      exact hdouble
    have hsnd := congrArg Prod.snd h
    rw [hfstZero, hphi_zero_left] at hsnd
    simp only [add_zero] at hsnd
    have hsndZero : (coord (1 : S1)).1.2 = 0 := by
      have hdouble : (coord (1 : S1)).1.2 +
          (coord (1 : S1)).1.2 = 0 :=
        CharTwo.add_self_eq_zero _
      rw [show (coord (1 : S1)).1.2 =
        (coord (1 : S1)).1.2 + (coord (1 : S1)).1.2 from hsnd]
      exact hdouble
    exact Prod.ext hfstZero hsndZero
  let polarF : Eact →ₗ[ZMod 2] Eact →ₗ[ZMod 2] F :=
    { toFun := fun x =>
        { toFun := fun y => ⟨qNorm.polarBilin x y, hqNormPolar_memF x y⟩
          map_add' := by
            intro y z
            apply Subtype.ext
            exact map_add (qNorm.polarBilin x) y z
          map_smul' := by
            intro a y
            apply Subtype.ext
            exact map_smul (qNorm.polarBilin x) a y }
      map_add' := by
        intro x y
        apply LinearMap.ext
        intro z
        apply Subtype.ext
        exact DFunLike.congr_fun (map_add qNorm.polarBilin x y) z
      map_smul' := by
        intro a x
        apply LinearMap.ext
        intro y
        apply Subtype.ext
        exact DFunLike.congr_fun (map_smul qNorm.polarBilin a x) y }
  let qF : QuadraticMap (ZMod 2) Eact F :=
    { toFun := fun x => ⟨qNorm x, hqNorm_memF x⟩
      toFun_smul := by
        intro a x
        apply Subtype.ext
        exact qNorm.toFun_smul a x
      exists_companion' := ⟨polarF, by
        intro x y
        apply Subtype.ext
        exact hqNorm_add x y⟩ }
  have hqF_apply (x : Eact) : (qF x : Eact) = qNorm x := rfl
  let centerPoint (z : F) :
      {p : Eact × Eact //
        Or (And (theta = 1) (p.2 + sigma p.2 = p.1 * sigma p.1))
          (And (theta ≠ 1) (p.2 ∈ F))} :=
    ⟨(0, (z : Eact)), by
      by_cases htheta : theta = 1
      · exact Or.inl ⟨htheta, by
          rw [zero_mul, hsigma_ext, htheta]
          exact CharTwo.add_self_eq_zero _⟩
      · exact Or.inr ⟨htheta, z.property⟩⟩
  let piModel : S1 →* Multiplicative Eact :=
    { toFun := fun x => Multiplicative.ofAdd (coord x).1.1
      map_one' := by rw [hcoord_one]; rfl
      map_mul' := by
        intro x y
        change Multiplicative.ofAdd (coord (x * y)).1.1 =
          Multiplicative.ofAdd ((coord x).1.1 + (coord y).1.1)
        exact congrArg (fun p : Eact × Eact => Multiplicative.ofAdd p.1)
          (hcoordMul x y) }
  let iotaModel : Multiplicative F →* S1 :=
    { toFun := fun z => coord.symm (centerPoint z.toAdd)
      map_one' := by
        apply coord.injective
        rw [coord.apply_symm_apply]
        apply Subtype.ext
        simpa [centerPoint] using hcoord_one.symm
      map_mul' := by
        intro z w
        apply coord.injective
        rw [coord.apply_symm_apply]
        apply Subtype.ext
        change ((centerPoint (z * w).toAdd).1 : Eact × Eact) =
          ((coord
            (coord.symm (centerPoint z.toAdd) *
              coord.symm (centerPoint w.toAdd))).1 : Eact × Eact)
        rw [hcoordMul, coord.apply_symm_apply, coord.apply_symm_apply]
        simp [centerPoint, hphi_zero_left, add_comm] }
  have hpiModel_coord (x : S1) :
      (piModel x).toAdd = (coord x).1.1 := rfl
  have hiotaModel_coord (z : Multiplicative F) :
      ((coord (iotaModel z)).1 : Eact × Eact) =
        (0, (z.toAdd : Eact)) := by
    set_option backward.isDefEq.respectTransparency true in
      dsimp [iotaModel]
      rw [coord.apply_symm_apply]
  have hsigma_eq_bar (htheta : theta = 1) : sigma = bar := by
    simp [sigma, htheta]
  obtain ⟨hiotaModel_injective, hpiModel_surjective, hexactModel,
      hcentralModel, hsquareModel⟩ :=
    typeB_model_central_extension_data F theta sigma bar phi qNorm qF
      coord hcoordMul piModel iotaModel hpiModel_coord hiotaModel_coord
      htrace_formula hmemF_of_bar_fixed hsigma_eq_bar hqNorm_norm
      hphi_zero_left hphi_zero_right hphi_diag hqF_apply
  let centerScale : F →+ BinaryGaloisField nH :=
    { toFun := fun z => baseEquiv (qScale * z)
      map_zero' := by simp
      map_add' := by
        intro x y
        simp only [mul_add, map_add] }
  have hcenterScale_surjective : Function.Surjective centerScale := by
    intro z
    refine ⟨qScale⁻¹ * baseEquiv.symm z, ?_⟩
    change baseEquiv (qScale * (qScale⁻¹ * baseEquiv.symm z)) = z
    rw [show qScale * (qScale⁻¹ * baseEquiv.symm z) =
      baseEquiv.symm z by
        rw [← mul_assoc, mul_inv_cancel₀ hqScaleNe, one_mul],
      baseEquiv.apply_symm_apply]
  let iotaActual : Multiplicative F →* S :=
    iotaBase.comp centerScale.toMultiplicative
  have hcenterScale_injective : Function.Injective centerScale := by
    intro x y hxy
    apply mul_left_cancel₀ hqScaleNe
    exact baseEquiv.injective hxy
  have hcenterScale_mul_injective :
      Function.Injective centerScale.toMultiplicative := by
    intro x y hxy
    apply Multiplicative.toAdd.injective
    apply hcenterScale_injective
    exact congrArg Multiplicative.toAdd hxy
  have hiotaActual_injective : Function.Injective iotaActual :=
    hiotaBase_injective.comp hcenterScale_mul_injective
  have hiotaBase_range : iotaBase.range = Subgroup.center S := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact (eZ.symm z).property
    · intro hx
      refine ⟨eZ ⟨x, hx⟩, ?_⟩
      apply Subtype.ext
      simp [iotaBase]
  have hiotaActual_range : iotaActual.range = Subgroup.center S := by
    rw [← hiotaBase_range]
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨centerScale.toMultiplicative z, rfl⟩
    · rintro ⟨z, rfl⟩
      obtain ⟨w, rfl⟩ := hcenterScale_surjective z.toAdd
      exact ⟨Multiplicative.ofAdd w, rfl⟩
  have hpiActual_ker : piActual.ker = Subgroup.center S := by
    ext x
    constructor
    · intro hx
      have hpi := MonoidHom.mem_ker.mp hx
      rw [hpiActual_apply] at hpi
      have hquot : QuotientGroup.mk' (Subgroup.center S) x = 1 := by
        exact fieldToQuot.symm.injective
          (hpi.trans (map_one fieldToQuot.symm).symm)
      exact (QuotientGroup.eq_one_iff x).mp hquot
    · intro hx
      apply MonoidHom.mem_ker.mpr
      have hquot : QuotientGroup.mk' (Subgroup.center S) x = 1 :=
        (QuotientGroup.eq_one_iff x).mpr hx
      rw [hpiActual_apply, hquot, map_one]
  have hexactActual : iotaActual.range = piActual.ker := by
    rw [hiotaActual_range, hpiActual_ker]
  have hcentralActual : iotaActual.range ≤ Subgroup.center S := by
    rw [hiotaActual_range]
  have hsquareActual (x : S) :
      iotaActual (Multiplicative.ofAdd (qF (piActual x).toAdd)) = x ^ 2 := by
    rw [← hqBase_square x]
    change iotaBase (Multiplicative.ofAdd
      (baseEquiv (qScale * qF (piActual x).toAdd))) =
        iotaBase (Multiplicative.ofAdd (qBase (piActual x).toAdd))
    congr 2
    apply (algebraMap (BinaryGaloisField nH) Eact).injective
    calc
      algebraMap (BinaryGaloisField nH) Eact
          (baseEquiv (qScale * qF (piActual x).toAdd)) =
          ((qScale * qF (piActual x).toAdd : F) : Eact) :=
        (hbaseCoe (qScale * qF (piActual x).toAdd)).symm
      _ = (qScale : Eact) * qNorm (piActual x).toAdd := by
        change (qScale : Eact) * (qF (piActual x).toAdd : Eact) =
          (qScale : Eact) * qNorm (piActual x).toAdd
        rw [hqF_apply]
      _ = qActual (piActual x).toAdd := by
        rw [hqNorm_eval, ← mul_assoc, mul_inv_cancel₀ hqScaleE, one_mul]
      _ = algebraMap (BinaryGaloisField nH) Eact
          (qBase (piActual x).toAdd) := hqActual_base _
  obtain ⟨sIso0, hsIso0_pi, hsIso0_iota⟩ :=
    central_extensions_equivalent_same_quadratic_lift_right
      iotaActual piActual iotaModel piModel qF
      hiotaActual_injective hpiActual_surjective
      hexactActual hcentralActual
      hiotaModel_injective hpiModel_surjective
      hexactModel hcentralModel
      hsquareActual hsquareModel
  let invActor : Actor1 ≃* Actor1 := MulEquiv.inv Actor1
  let kwIsoFinal : Actor ≃* Actor1 := kwIso.trans invActor
  have hkwIsoFinal_val (a : Actor) :
      ((kwIsoFinal a : Actor1) : Eactˣ) = (kwUnits a)⁻¹ := by
    change (((kwIso a : Actor1) : Eactˣ))⁻¹ = (kwUnits a)⁻¹
    rw [hkwIso_val]
  have hmapInv (L : Subgroup Actor1) :
      Subgroup.map invActor.toMonoidHom L = L := by
    ext a
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact L.inv_mem hb
    · intro ha
      refine ⟨a⁻¹, L.inv_mem ha, ?_⟩
      simp [invActor]
  have hkwIsoFinal_hom :
      kwIsoFinal.toMonoidHom =
        invActor.toMonoidHom.comp kwIso.toMonoidHom := by
    apply MonoidHom.ext
    intro a
    rfl
  have hmapKFinal :
      Subgroup.map kwIsoFinal.toMonoidHom (K.subgroupOf Actor) =
        K1.subgroupOf Actor1 := by
    rw [hkwIsoFinal_hom, ← Subgroup.map_map, hmapK, hmapInv]
  have hmapWFinal :
      Subgroup.map kwIsoFinal.toMonoidHom (W.subgroupOf Actor) =
        W1.subgroupOf Actor1 := by
    rw [hkwIsoFinal_hom, ← Subgroup.map_map, hmapW, hmapInv]
  have hactorNormAll (a : Actor1) :
      ((a : Eactˣ) : Eact) * sigma ((a : Eactˣ) : Eact) ∈ F := by
    by_cases htheta : theta = 1
    · apply hmemF_of_bar_fixed
      have hsigmaBar : sigma = bar := by simp [sigma, htheta]
      rw [hsigmaBar, map_mul, hbar_involutive]
      ring
    · exact hactorNorm a htheta
  let actorScaleF (a : Actor) : F :=
    ⟨(kwUnits a : Eact) * sigma (kwUnits a : Eact), by
      simpa [hkwIso_val] using hactorNormAll (kwIso a)⟩
  have hactorScaleF_coe (a : Actor) :
      (actorScaleF a : Eact) =
        (kwUnits a : Eact) * sigma (kwUnits a : Eact) := rfl
  let rhoModel : Actor →* MulAut S1 :=
    rho1.comp kwIsoFinal.toMonoidHom
  have hrhoModel_coord (a : Actor) (x : S1) :
      ((coord (rhoModel a x)).1 : Eact × Eact) =
        ((kwUnits a : Eact) * (coord x).1.1,
          (actorScaleF a : Eact) * (coord x).1.2) := by
    have h := hrho1 (kwIsoFinal a)⁻¹ x
    have hvalInv :
        ((((kwIsoFinal a)⁻¹ : Actor1) : Eactˣ)) = kwUnits a := by
      calc
        ((((kwIsoFinal a)⁻¹ : Actor1) : Eactˣ)) =
            (((kwIsoFinal a : Actor1) : Eactˣ))⁻¹ := rfl
        _ = ((kwUnits a)⁻¹)⁻¹ :=
          congrArg Inv.inv (hkwIsoFinal_val a)
        _ = kwUnits a := inv_inv _
    change ((coord (rho1 (kwIsoFinal a) x)).1 : Eact × Eact) = _
    simpa only [inv_inv, hvalInv, hactorScaleF_coe] using h
  have hrhoModel_pi (a : Actor) (x : S1) :
      piModel (rhoModel a x) =
        Multiplicative.ofAdd
          ((kwUnits a : Eact) * (piModel x).toAdd) := by
    apply Multiplicative.ofAdd.injective
    simpa [piModel] using congrArg Prod.fst (hrhoModel_coord a x)
  have hrhoModel_iota (a : Actor) (z : Multiplicative F) :
      rhoModel a (iotaModel z) =
        iotaModel (Multiplicative.ofAdd (actorScaleF a * z.toAdd)) := by
    apply coord.injective
    apply Subtype.ext
    calc
      ((coord (rhoModel a (iotaModel z))).1 : Eact × Eact) =
          ((kwUnits a : Eact) * 0,
            (actorScaleF a : Eact) * (z.toAdd : Eact)) := by
        rw [hrhoModel_coord]
        have hz := hiotaModel_coord z
        rw [hz]
      _ = (0, ((actorScaleF a * z.toAdd : F) : Eact)) := by simp
      _ = ((coord (iotaModel
          (Multiplicative.ofAdd (actorScaleF a * z.toAdd)))).1 :
            Eact × Eact) :=
        (hiotaModel_coord
          (Multiplicative.ofAdd (actorScaleF a * z.toAdd))).symm
  have hactorScaleF_decomp (a : Actor) (k : K) (w : W)
      (ha : a = kIncl k * wIncl w) :
      baseEquiv (actorScaleF a) =
        (eK k : BinaryGaloisField nH) *
          thetaH (eK k : BinaryGaloisField nH) := by
    exact actor_scale_decomp_of_decomposition
      F baseEquiv theta thetaH sigma kwUnits kIncl wIncl eK.toMonoidHom
      actorScaleF hactorScaleF_coe hbaseCoe htheta_intertwine hkwUnitsK
      hsigma_ext
      (fun w => hsigmaW1 (kwUnits (wIncl w))
        (Subgroup.mem_map.mpr ⟨wIncl w, w.property, rfl⟩))
      a k w ha
  have hrhoActual_iota (a : Actor) (z : Multiplicative F) :
      rhoActual a (iotaActual z) =
        iotaActual
          (Multiplicative.ofAdd (actorScaleF a * z.toAdd)) := by
    obtain ⟨k, w, ha⟩ := hKW_decomp a
    subst a
    rw [map_mul]
    change rhoActual (kIncl k)
        (rhoActual (wIncl w)
          (iotaBase
            (Multiplicative.ofAdd (centerScale z.toAdd)))) =
      iotaBase (Multiplicative.ofAdd
        (centerScale
          (actorScaleF (kIncl k * wIncl w) * z.toAdd)))
    rw [hWcenterBase, hKcenterBase]
    apply congrArg iotaBase
    apply congrArg Multiplicative.ofAdd
    change (eK k : BinaryGaloisField nH) *
        thetaH (eK k : BinaryGaloisField nH) *
          baseEquiv (qScale * z.toAdd) =
      baseEquiv (qScale *
        (actorScaleF (kIncl k * wIncl w) * z.toAdd))
    rw [map_mul, map_mul, map_mul,
      hactorScaleF_decomp (kIncl k * wIncl w) k w rfl]
    ring
  let rhoTransport : Actor →* MulAut S1 :=
    (MulAut.congr sIso0).toMonoidHom.comp rhoActual
  have hrhoTransport_pi (a : Actor) (x : S1) :
      piModel (rhoTransport a x) =
        Multiplicative.ofAdd
          ((kwUnits a : Eact) * (piModel x).toAdd) := by
    apply Multiplicative.toAdd.injective
    calc
      (piModel (rhoTransport a x)).toAdd =
          (piActual (rhoActual a (sIso0.symm x))).toAdd := by
        simpa [rhoTransport, MulAut.congr] using
          hsIso0_pi (rhoActual a (sIso0.symm x))
      _ = (kwUnits a : Eact) *
          (piActual (sIso0.symm x)).toAdd := by
        rw [hpiActual_action]
        rfl
      _ = (kwUnits a : Eact) * (piModel x).toAdd := by
        apply congrArg (fun y : Eact => (kwUnits a : Eact) * y)
        calc
          (piActual (sIso0.symm x)).toAdd =
              (piModel (sIso0 (sIso0.symm x))).toAdd :=
            (hsIso0_pi (sIso0.symm x)).symm
          _ = (piModel x).toAdd := by
            rw [sIso0.apply_symm_apply]
  have hrhoTransport_iota (a : Actor) (z : Multiplicative F) :
      rhoTransport a (iotaModel z) =
        iotaModel
          (Multiplicative.ofAdd (actorScaleF a * z.toAdd)) := by
    change sIso0
        (rhoActual a (sIso0.symm (iotaModel z))) = _
    rw [← hsIso0_iota, sIso0.symm_apply_apply, hrhoActual_iota,
      hsIso0_iota]
  have hactorScaleF_ne (a : Actor) : actorScaleF a ≠ 0 := by
    intro hzero
    have hzeroCoe : (actorScaleF a : Eact) = 0 :=
      congrArg Subtype.val hzero
    rw [hactorScaleF_coe] at hzeroCoe
    have hsigmaNe : sigma (kwUnits a : Eact) ≠ 0 :=
      (map_ne_zero sigma).2 (Units.ne_zero (kwUnits a))
    exact (mul_ne_zero (Units.ne_zero (kwUnits a)) hsigmaNe) hzeroCoe
  have hrhoModel_inv_iota (a : Actor) (z : Multiplicative F) :
      (rhoModel a)⁻¹ (iotaModel z) =
        iotaModel (Multiplicative.ofAdd
          ((actorScaleF a)⁻¹ * z.toAdd)) := by
    apply (rhoModel a).injective
    calc
      rhoModel a ((rhoModel a)⁻¹ (iotaModel z)) = iotaModel z :=
        (rhoModel a).apply_symm_apply (iotaModel z)
      _ = rhoModel a (iotaModel (Multiplicative.ofAdd
          ((actorScaleF a)⁻¹ * z.toAdd))) := by
        rw [hrhoModel_iota]
        apply congrArg iotaModel
        apply congrArg Multiplicative.ofAdd
        change z.toAdd = actorScaleF a *
          ((actorScaleF a)⁻¹ * z.toAdd)
        symm
        calc
          actorScaleF a * ((actorScaleF a)⁻¹ * z.toAdd) =
              (actorScaleF a * (actorScaleF a)⁻¹) * z.toAdd :=
            (mul_assoc _ _ _).symm
          _ = z.toAdd := by
            rw [mul_inv_cancel₀ (hactorScaleF_ne a), one_mul]
  have hActorOdd : Odd (Nat.card Actor) :=
    hsection3.1.hA.A1.D_odd.of_dvd_nat
      (Subgroup.card_dvd_of_le
        (sup_le hsection3.1.K_le_D hWleD))
  have hboundaryPi (a : Actor) (x : S1) :
      piModel (rhoTransport a x) = piModel (rhoModel a x) :=
    (hrhoTransport_pi a x).trans (hrhoModel_pi a x).symm
  have hboundaryIota (a : Actor) (z : Multiplicative F) :
      rhoTransport a (iotaModel z) = rhoModel a (iotaModel z) :=
    (hrhoTransport_iota a z).trans (hrhoModel_iota a z).symm
  have hrhoModel_pi_congr (a : Actor) (x y : S1)
      (hxy : piModel x = piModel y) :
      piModel (rhoModel a x) = piModel (rhoModel a y) := by
    rw [hrhoModel_pi, hrhoModel_pi, hxy]
  obtain ⟨uCorrect, halignAut⟩ :=
    align_odd_actions_from_matching_boundary
      iotaModel piModel hiotaModel_injective hpiModel_surjective
      hexactModel hcentralModel rhoTransport rhoModel
      (fun a z => Multiplicative.ofAdd
        ((actorScaleF a)⁻¹ * z.toAdd))
      hActorOdd hboundaryPi hboundaryIota hrhoModel_pi_congr
      hrhoModel_inv_iota
  let sIsoAligned : S ≃* S1 :=
    sIso0.trans uCorrect.symm
  have hsIsoAligned_action (a : Actor) (x : S) :
      sIsoAligned (rhoActual a x) =
        rhoModel a (sIsoAligned x) := by
    have h := DFunLike.congr_fun (halignAut a) (sIsoAligned x)
    simpa [sIsoAligned, rhoTransport, MulAut.congr] using h
  obtain ⟨target, htarget_inv, hcoord_target⟩ :=
    typeB_model_target_involution F theta sigma phi coord
      hcoordMul hcoord_one hphi_zero_left
  let targetS : S := sIsoAligned.symm target
  have htargetS_inv : IsInvolution targetS := by
    constructor
    · intro h
      apply htarget_inv.1
      have := congrArg sIsoAligned h
      simpa [targetS] using this
    · apply sIsoAligned.injective
      simp [targetS, htarget_inv.2]
  obtain ⟨kNorm, hkNorm, _⟩ :=
    hKregular.2 sS hsInvS targetS htargetS_inv
  let sIso : S ≃* S1 :=
    sIsoAligned.trans (rhoModel (kIncl kNorm))
  have hActor_comm (a b : Actor) : a * b = b * a := by
    apply kwIsoFinal.injective
    rw [map_mul, map_mul, mul_comm]
  have hsIso_action (a : Actor) (x : S) :
      sIso (rhoActual a x) = rhoModel a (sIso x) := by
    change rhoModel (kIncl kNorm)
        (sIsoAligned (rhoActual a x)) =
      rhoModel a (rhoModel (kIncl kNorm) (sIsoAligned x))
    rw [hsIsoAligned_action]
    change (rhoModel (kIncl kNorm) * rhoModel a)
        (sIsoAligned x) =
      (rhoModel a * rhoModel (kIncl kNorm)) (sIsoAligned x)
    rw [← map_mul, hActor_comm, map_mul]
  have hAction (a : Actor) :
      (rhoActual a).trans sIso =
        sIso.trans (rho1 (kwIsoFinal a)) := by
    apply DFunLike.ext _ _
    intro x
    exact hsIso_action a x
  let modelIso :
      SemidirectProduct S Actor rhoActual ≃*
        SemidirectProduct S1 Actor1 rho1 :=
    SemidirectProduct.congr sIso kwIsoFinal hAction
  have hmodelIso_inl (x : S) :
      modelIso (SemidirectProduct.inl x) =
        SemidirectProduct.inl (sIso x) := by
    ext <;> simp [modelIso]
  have hmodelIso_inr (a : Actor) :
      modelIso (SemidirectProduct.inr a) =
        SemidirectProduct.inr (kwIsoFinal a) := by
    ext <;> simp [modelIso]
  have hsIso_target : sIso sS = target := by
    change rhoModel (kIncl kNorm) (sIsoAligned sS) = target
    calc
      rhoModel (kIncl kNorm) (sIsoAligned sS) =
          sIsoAligned (rhoActual (kIncl kNorm) sS) :=
        (hsIsoAligned_action (kIncl kNorm) sS).symm
      _ = sIsoAligned (kNorm • sS) := by rw [hrhoActualK]
      _ = sIsoAligned targetS := by rw [hkNorm]
      _ = target := by simp [targetS]
  refine ⟨Eact, hEactField, hEactFinite, inferInstance, F, theta,
    sigma, phi, K1, W1, S1, groupS1, coord, rhoActual, rho1, sIso,
    kwIsoFinal, modelIso, hfinrankFEact, hcardF, hthetaOdd, hsigma_ext,
    hsigma_frobenius, hK1, hW1ne, hW1norm, hsigmaW1, hphi_one, ?_,
    hcoordMul, hrhoActual, hrho1, hmodelIso_inl, hmodelIso_inr,
    hmapKFinal, hmapWFinal, ?_⟩
  · intro htheta
    exact ⟨hphi_memF htheta, hphi_add_left, hphi_add_right,
      hphi_smul htheta, hphi_diag_ne htheta⟩
  · refine ⟨hsS, ?_⟩
    change ((coord (sIso sS)).1 : Eact × Eact) = (0, 1)
    rw [hsIso_target, hcoord_target]

set_option maxHeartbeats 2000000 in
/--
Peterfalvi, Part II, Chapter III, Section 3, Proposition.

The cyclicity of `W` and the fixed-point-free action needed in the coordinate
construction are the two consequences of Chapter I, Section 3, Lemma 5 used
in the printed proof.  This theorem derives them from the induction hypothesis
rather than exposing them as extra assumptions of the proposition.
-/
public theorem proposition
    {G : Type u} {Ω : Type v}
    [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t s : G)
    (hsection3 : ((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q) ∧
  s ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution s ∧
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r))
    (hC1 : HypothesisC1 G V)
    (hC2 : HypothesisC2 G S W t s)
    (hind :
      ∀ (L : Type u) [Group L] [Finite L],
        ∀ (ΩL : Type v) [MulAction L ΩL] [Finite ΩL]
          (HL DL QL : Subgroup L) (tL : L),
          Nat.card L < Nat.card G → HypothesisA L ΩL HL DL QL tL →
            suzukiConclusion L ΩL)
    (hSQ : S = Q) :
    TypeBChapter3Data G K Q0 S W s := by
  have hSuzukiS : IsSuzukiTwoGroup S := by
    rcases PFchapter1section2.corollary
        H D Q K V W Q0 S Q1 t hsection3.section2 with hcomm | hSuzuki
    · exact False.elim (typeB_not_isMulCommutative S hC2.S_type_B hcomm)
    · exact hSuzuki
  have hSuzukiQ : IsSuzukiTwoGroup Q := by
    rw [← hSQ]
    exact hSuzukiS
  have hQcard : Nat.card Q = Nat.card Q0 ^ 3 :=
    typeB_natCard_eq_cube H Q Q0 S hC2.S_type_B
      hsection3.section2.S_le_Q hsection3.section2.hA.A1.Q_le_H
      hsection3.section2.Q0_le_Q hsection3.section2.Q0_def hSQ
  have hlemma5 := PFchapter1section3.lemma_5
    H D Q K V W Q0 S Q1 t s hsection3 hind hC2.st_order_three
      hSuzukiQ hQcard
  have hWcyclic : IsCyclic W := hlemma5.1
  have hIsoQ := PFchapter1section3.lemma_5_isomorphic_summands
    H D Q K V W Q0 S Q1 t s hsection3 hind hC2.st_order_three
      hSuzukiQ hQcard hC2.W_ne_bot
  have hIsoS : ∃ hKnormS : K ≤ Subgroup.normalizer (S : Set G),
      letI : MulDistribMulAction K S :=
        Subgroup.conjMulDistribMulActionOfLeNormalizer K S hKnormS
      External.Higman.Theorem1IsomorphicSummands K S := by
    cases hSQ
    exact hIsoQ
  have hVleD : V ≤ D := by
    rw [hsection3.section2.V_eq]
    exact inf_le_left
  have hWleD : W ≤ D := hsection3.section2.W_le_V.trans hVleD
  have hQ0sq : ∀ z : G, z ∈ Q0 → z ^ 2 = 1 := by
    intro z hz
    rcases (hsection3.section2.Q0_def z).1 hz with rfl | hz
    · simp
    · exact hz.2.sq_eq_one
  have hsq_mem_Q0 : ∀ x : G, x ∈ Q → x ^ 2 = 1 → x ∈ Q0 := by
    intro x hxQ hx2
    by_cases hxone : x = 1
    · simp [hxone, Q0.one_mem]
    · exact (hsection3.section2.Q0_def x).2
        (Or.inr ⟨hsection3.section2.hA.A1.Q_le_H hxQ, hxone, hx2⟩)
  have hsquare : ∀ x : G, x ∈ Q → x ^ 2 ∈ Q0 := by
    intro x hxQ
    apply typeB_square_mem_Q0 H Q Q0 S hC2.S_type_B
      hsection3.section2.S_le_Q hsection3.section2.hA.A1.Q_le_H
      hsection3.section2.Q0_def x
    simpa [hSQ] using hxQ
  have hQ0commQ : ∀ z : G, z ∈ Q0 → ∀ x : G, x ∈ Q →
      z * x = x * z := by
    intro z hzQ0 x hxQ
    rcases (hsection3.section2.Q0_def z).1 hzQ0 with rfl | hz
    · simp
    · exact (hC2.S_type_B.commute_of_isInvolution
        (by simpa [hSQ] using hsection3.section2.Q0_le_Q hzQ0)
        hz.2 (by simpa [hSQ] using hxQ)).eq
  have hWcommQ0 : ∀ w : G, w ∈ W → ∀ z : G, z ∈ Q0 →
      z * w = w * z := by
    have hWdesc :=
      PFchapter1section2.peterfalvi_chapter1_section2_proposition_3_appendixI_input_W_eq_D_centralizer_involutions
        H D Q K V W t hsection3.section2.hA.A1
        hsection3.section2.K_def hsection3.section2.V_eq
        hsection3.section2.W_eq
    intro w hwW z hzQ0
    rcases (hsection3.section2.Q0_def z).1 hzQ0 with rfl | hz
    · simp
    · have hw := hwW
      rw [hWdesc] at hw
      exact Subgroup.mem_centralizer_iff.mp hw.2 z hz
  have hregular :
      ConjugationRegularOn K {z : G | z ∈ S ∧ IsInvolution z} :=
    PFchapter1section2.corollary_K_regular_on_S_involutions
      H D Q K V W Q0 S Q1 t hsection3.section2
  have hcentralizer : ∀ w : G, w ∈ W → w ≠ 1 →
      Subgroup.centralizer (Subgroup.zpowers w : Set G) ⊓ Q = Q0 := by
    intro w hwW hwne
    exact PFchapter1section3.lemma_5_nontrivial_W_centralizer_eq_Q0
      H D Q K V W Q0 S Q1 t s w hsection3 hind hC2.st_order_three
        hSuzukiQ hQcard hwW hwne
  have hWcentralizesK : W ≤ Subgroup.centralizer (K : Set G) := by
    intro w hwW
    rw [hsection3.section2.W_eq] at hwW
    exact hwW.2
  have hWnormalizesK : W ≤ Subgroup.normalizer (K : Set G) :=
    hWcentralizesK.trans (centralizer_le_normalizer K)
  have hKWdecomp : ∀ d : G, d ∈ K ⊔ W →
      ∃ w k : G, w ∈ W ∧ k ∈ K ∧ d = w * k := by
    intro d hdKW
    change d ∈ ((K ⊔ W : Subgroup G) : Set G) at hdKW
    rw [Subgroup.coe_mul_of_right_le_normalizer_left K W hWnormalizesK] at hdKW
    rcases Set.mem_mul.mp hdKW with ⟨k, hkK, w, hwW, hkw⟩
    have hcomm : k * w = w * k :=
      Subgroup.mem_centralizer_iff.mp (hWcentralizesK hwW) k hkK
    exact ⟨w, k, hwW, hkK, hkw.symm.trans hcomm⟩
  have hKW_fixed_point_free : ∀ d : G, d ∈ K ⊔ W → d ≠ 1 →
      ∀ x : G, x ∈ Q → x ∉ Q0 →
        rightConjugateElem x d * x⁻¹ ∉ Q0 :=
    fixedPointFree_quotient_core D (K ⊔ W) Q K W Q0 S
      hsection3.section2.hA.A1.D_odd hWleD hKWdecomp hSQ hQ0sq
      hsq_mem_Q0 hsquare hQ0commQ hWcommQ0 hregular hcentralizer
  exact proposition_of_KW_fixed_point_free
    H D Q K V W Q0 S Q1 t s hsection3 hC1 hC2 hWcyclic hIsoS
      hKW_fixed_point_free hSQ

end PFchapter3section3
end CFSG.BenderSuzuki
