module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section9Lemma98
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Corollary85
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.II1Section4
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84Sylow
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.Nilpotent
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.lemma_3_1
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection5.theorem_5_3
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection6.lemma_6_5_a
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.corollary_12_9_b
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem

namespace CFSG
end CFSG
open CFSG

/-!
# Section 9, Lemma 9.9

This file isolates the exact earlier-book inputs used by Lemma 9.9 and proves
its checked final reduction from the two assertions labelled `(9F)`.  It also
contains the nilpotent-normalizer bridge omitted in the source sentence that
identifies the maximal subgroup `H` with the `p′`-core of the Fitting subgroup.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1
open scoped Pointwise

universe u

/-- Exact `[IG; 9.11(ii)]` endpoint used after the first half of `(9F)`. -/
@[expose] public def IG911iiNilpotentFrobeniusComplementCyclic
    {X : Type u} [Group X] [Finite X] : Prop :=
  ∀ (S K R : Subgroup X), K ≤ S → R ≤ S →
    IsFrobeniusGroupWithKernelComplement
        (K.subgroupOf S) (R.subgroupOf S) →
      Group.IsNilpotent R → Odd (Nat.card R) → IsCyclic R

/-- The two checked conclusions called `(9F)` in the source. -/
public structure Lemma99NineF
    {X : Type u} [Group X] [Finite X]
    (D E : Subgroup X) (t : X) : Prop where
  fitting_fixedPointFree :
    let K : Subgroup X := Subgroup.closure (peterfalviKSet D t)
    let R : Subgroup X := E ⊓ peterfalviV D t
    let F : Subgroup X := (fittingSubgroup R).map R.subtype
    ∀ x : X, x ∈ F → x ≠ 1 →
      ∀ k : X, k ∈ K → k * x = x * k → k = 1
  derived_inf_fixed_le_fitting :
    let R : Subgroup X := E ⊓ peterfalviV D t
    let F : Subgroup X := (fittingSubgroup R).map R.subtype
    (derivedSubgroup E).map E.subtype ⊓ peterfalviV D t ≤ F

private theorem lemma99_isMulCommutative_of_closure_eq_set
    {X : Type u} [Group X]
    {D K : Subgroup X} {t : X}
    (hKset : (K : Set X) = peterfalviKSet D t) :
    IsMulCommutative K := by
  refine IsMulCommutative.mk ⟨?_⟩
  intro a b
  apply Subtype.ext
  have haI : (a : X) ∈ peterfalviKSet D t := by
    rw [← hKset]
    exact a.property
  have hbI : (b : X) ∈ peterfalviKSet D t := by
    rw [← hKset]
    exact b.property
  have habI : (a : X) * (b : X) ∈ peterfalviKSet D t := by
    rw [← hKset]
    exact K.mul_mem a.property b.property
  have hinvComm : (a : X)⁻¹ * (b : X)⁻¹ =
      (b : X)⁻¹ * (a : X)⁻¹ := by
    calc
      (a : X)⁻¹ * (b : X)⁻¹ =
          rightConjugateElem (a : X) t *
            rightConjugateElem (b : X) t := by rw [haI.2, hbI.2]
      _ = rightConjugateElem ((a : X) * (b : X)) t := by
            simp [rightConjugateElem, mul_assoc]
      _ = ((a : X) * (b : X))⁻¹ := habI.2
      _ = (b : X)⁻¹ * (a : X)⁻¹ := by simp
  have := congrArg Inv.inv hinvComm
  simpa using this.symm

/-- Checked final assembly: `[II1; 4.3(c)]`, `(9F)`, Corollary 9.6, and
`[IG; 9.11(ii)]` contradict Lemma 9.8(b). -/
public theorem lemma99_false_of_nineF
    {X : Type u} [Group X] [Finite X]
    {D E : Subgroup X} {t : X}
    (hED : E ≤ D)
    (hDodd : Odd (Nat.card D))
    (hIne : ∃ k : X, k ∈ peterfalviKSet D t ∧ k ≠ 1)
    (h43c : II1Lemma43cConclusion D t)
    (h96 : Corollary96Conclusion D E t)
    (h98 : Lemma98Conclusion D E t)
    (h9F : Lemma99NineF D E t)
    (h911 : IG911iiNilpotentFrobeniusComplementCyclic (X := X)) :
    False := by
  classical
  let K : Subgroup X := Subgroup.closure (peterfalviKSet D t)
  let V : Subgroup X := peterfalviV D t
  let R : Subgroup X := E ⊓ V
  let F : Subgroup X := (fittingSubgroup R).map R.subtype
  have hKE : K ≤ E := by
    simpa [K] using h96.closure_le_derived.trans
      (Subgroup.map_subtype_le (derivedSubgroup E))
  have hKset : (K : Set X) = peterfalviKSet D t := by
    simpa [K] using h43c.closure_eq_set
  have hKcomm : IsMulCommutative K :=
    lemma99_isMulCommutative_of_closure_eq_set hKset
  letI : IsMulCommutative K := hKcomm
  have hRleE : R ≤ E := inf_le_left
  have hFleR : F ≤ R := by
    simpa [F] using Subgroup.map_subtype_le (fittingSubgroup R)
  have hFleE : F ≤ E := hFleR.trans hRleE
  have hKnormalD : (K.subgroupOf D).Normal := by
    simpa [K] using h43c.normal
  have hDnormK : D ≤ Subgroup.normalizer (K : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (by simpa [K] using h43c.closure_le)).mp hKnormalD
  have hKnormalE : (K.subgroupOf E).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKE).mpr
      (hED.trans hDnormK)
  have hKdisjV : Disjoint K V := by
    rw [Subgroup.disjoint_def]
    intro x hxK hxV
    have hxD : x ∈ D := by simpa [K] using h43c.closure_le hxK
    let xD : D := ⟨x, hxD⟩
    have hxKV : xD ∈
        (K.subgroupOf D) ⊓ (V.subgroupOf D) := ⟨hxK, hxV⟩
    have hxbot : xD ∈ (⊥ : Subgroup D) := by
      rw [← h43c.isComplement'.disjoint.eq_bot]
      exact hxKV
    exact congrArg Subtype.val (by simpa using hxbot)
  have hKFdisj : Disjoint (K.subgroupOf (K ⊔ F)) (F.subgroupOf (K ⊔ F)) := by
    rw [Subgroup.disjoint_def]
    intro x hxK hxF
    apply Subtype.ext
    have hxbot : (x : X) ∈ (⊥ : Subgroup X) := by
      rw [← hKdisjV.eq_bot]
      exact ⟨hxK, hFleR hxF |>.2⟩
    simpa using hxbot
  have hKnormalKF : (K.subgroupOf (K ⊔ F)).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
    exact (sup_le hKE hFleE).trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hKE).mp hKnormalE)
  have hKFcomp :
      (K.subgroupOf (K ⊔ F)).IsComplement' (F.subgroupOf (K ⊔ F)) := by
    letI : (K.subgroupOf (K ⊔ F)).Normal := hKnormalKF
    exact isComplement'_of_disjoint_sup_eq_top_of_normal
      (K.subgroupOf (K ⊔ F)) (F.subgroupOf (K ⊔ F))
      hKFdisj (by
        rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right]
        simp)
  have hKne : K ≠ ⊥ := by
    obtain ⟨k, hkI, hkne⟩ := hIne
    intro hbot
    have hkbot : k ∈ (⊥ : Subgroup X) := by
      rw [← hbot]
      exact Subgroup.subset_closure hkI
    exact hkne (by simpa using hkbot)
  have hFne : F ≠ ⊥ := by
    have hderF :
        (derivedSubgroup E).map E.subtype ⊓ V ≤ F := by
      simpa [R, F, V] using h9F.derived_inf_fixed_le_fitting
    exact fun hbot => h98.derived_inf_fixed_ne_bot
      (le_antisymm (by simpa [hbot] using hderF) bot_le)
  have hKsubNe : K.subgroupOf (K ⊔ F) ≠ ⊥ := by
    intro hbot
    exact hKne ((Subgroup.subgroupOf_eq_bot.mp hbot).eq_bot_of_le le_sup_left)
  have hFsubNe : F.subgroupOf (K ⊔ F) ≠ ⊥ := by
    intro hbot
    exact hFne ((Subgroup.subgroupOf_eq_bot.mp hbot).eq_bot_of_le le_sup_right)
  have hKFrob : IsFrobeniusGroupWithKernelComplement
      (K.subgroupOf (K ⊔ F)) (F.subgroupOf (K ⊔ F)) := by
    apply (lemma_3_1 _ _ hKsubNe hFsubNe hKnormalKF hKFcomp).mpr
    intro x hxne
    rw [Subgroup.eq_bot_iff_forall]
    intro k hk
    apply Subtype.ext
    have hxF : (x : X) ∈ F := x.property
    have hxneX : (x : X) ≠ 1 := by
      intro hx
      exact hxne (Subtype.ext (Subtype.ext hx))
    have hkK : (k : X) ∈ K := hk.1
    have hcomm : (k : X) * (x : X) = (x : X) * (k : X) :=
      congrArg Subtype.val
        (Subgroup.mem_centralizer_singleton_iff.mp hk.2)
    have hfix := h9F.fitting_fixedPointFree
    change ∀ y : X, y ∈ F → y ≠ 1 →
      ∀ q : X, q ∈ K → q * y = y * q → q = 1 at hfix
    have hkone : (k : X) = 1 :=
      hfix (x : X) hxF hxneX (k : X) hkK hcomm
    exact hkone
  have hRodd : Odd (Nat.card R) :=
    hDodd.of_dvd_nat (Subgroup.card_dvd_of_le
      (hRleE.trans hED))
  have hFodd : Odd (Nat.card F) :=
    hRodd.of_dvd_nat (Subgroup.card_dvd_of_le hFleR)
  have hFnil : Group.IsNilpotent F := by
    change Group.IsNilpotent (fittingSubgroupOf (G := X) R)
    exact fittingSubgroupOf_isNilpotent (G := X) R
  have hFcyclic : IsCyclic F :=
    h911 (K ⊔ F) K F le_sup_left le_sup_right hKFrob hFnil hFodd
  have hKRdisj : Disjoint K R := by
    rw [Subgroup.disjoint_def]
    intro x hxK hxR
    exact Subgroup.disjoint_def.mp hKdisjV hxK hxR.2
  have hKRdisjE :
      Disjoint (K.subgroupOf E) (R.subgroupOf E) := by
    rw [Subgroup.disjoint_def]
    intro x hxK hxR
    apply Subtype.ext
    have hxbot : (x : X) ∈ (⊥ : Subgroup X) := by
      rw [← hKRdisj.eq_bot]
      exact ⟨hxK, hxR⟩
    simpa using hxbot
  have hKRmul :
      (K.subgroupOf E : Set E) * (R.subgroupOf E : Set E) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    have hxE : (x : X) ∈ (E : Set X) := x.property
    rw [show (E : Set X) = (K : Set X) * (R : Set X) by
      simpa [K, R, V] using h96.eq_mul_fixed] at hxE
    rcases Set.mem_mul.mp hxE with ⟨k, hk, r, hr, hkr⟩
    let kE : E := ⟨k, hKE hk⟩
    let rE : E := ⟨r, hRleE hr⟩
    exact Set.mem_mul.mpr ⟨kE, hk, rE, hr, Subtype.ext hkr⟩
  have hKRcomp : (K.subgroupOf E).IsComplement' (R.subgroupOf E) :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hKRdisjE hKRmul
  have hKsubEne : K.subgroupOf E ≠ ⊥ := by
    intro hbot
    exact hKne ((Subgroup.subgroupOf_eq_bot.mp hbot).eq_bot_of_le hKE)
  have hRne : R ≠ ⊥ := by
    simpa [R, V] using h96.inf_fixed_ne_bot
  have hRsubEne : R.subgroupOf E ≠ ⊥ := by
    intro hbot
    exact hRne ((Subgroup.subgroupOf_eq_bot.mp hbot).eq_bot_of_le hRleE)
  have hERfrob : IsFrobeniusGroupWithKernelComplement
      (K.subgroupOf E) (R.subgroupOf E) := by
    apply (lemma_3_1 _ _ hKsubEne hRsubEne hKnormalE hKRcomp).mpr
    intro x hxne
    rw [Subgroup.eq_bot_iff_forall]
    intro k hk
    apply Subtype.ext
    let xX : X := ((x : E) : X)
    have hxR : xX ∈ R := x.property
    have hxneX : xX ≠ 1 := by
      intro hx
      exact hxne (Subtype.ext (Subtype.ext hx))
    have hkK : (k : X) ∈ K := hk.1
    have hkI : (k : X) ∈ peterfalviKSet D t := by
      rw [← hKset]
      exact hkK
    have hcomm : (k : X) * xX = xX * (k : X) :=
      congrArg Subtype.val
        (Subgroup.mem_centralizer_singleton_iff.mp hk.2)
    by_cases hxDer : xX ∈ (derivedSubgroup E).map E.subtype
    · have hderF := h9F.derived_inf_fixed_le_fitting
      change (derivedSubgroup E).map E.subtype ⊓ V ≤ F at hderF
      have hxF : xX ∈ F := hderF ⟨hxDer, hxR.2⟩
      have hfix := h9F.fitting_fixedPointFree
      change ∀ y : X, y ∈ F → y ≠ 1 →
        ∀ q : X, q ∈ K → q * y = y * q → q = 1 at hfix
      exact hfix xX hxF hxneX (k : X) hkK hcomm
    · exact h96.fixedPointFree xX (by simpa [R, V] using hxR)
        hxDer (k : X) hkI hcomm
  apply h98.not_frobenius
  change K ≤ E ∧ (K : Set X) = peterfalviKSet D t ∧
    ∃ Q : Subgroup X, Q ≤ E ∧
      IsFrobeniusGroupWithKernelComplement
        (K.subgroupOf E) (Q.subgroupOf E)
  exact ⟨hKE, hKset, R, hRleE, hERfrob⟩

/-! ## A prime in the abelianization -/

/-- A nontrivial finite odd-order group has a prime divisor in its
abelianization.  Solvability makes the derived subgroup proper. -/
public theorem lemma99_exists_prime_dvd_abelianization
    {E : Type*} [Group E] [Finite E] [Nontrivial E]
    (hEodd : Odd (Nat.card E)) :
    ∃ p : ℕ, Nat.Prime p ∧ p ∣ Nat.card (E ⧸ derivedSubgroup E) := by
  have hsolv : Group.IsSolvable E := odd_order_theorem E hEodd
  have hder_lt : derivedSubgroup E < ⊤ := by
    change commutator E < ⊤
    exact Group.IsSolvable.commutator_lt_top_of_nontrivial (G := E)
  have hqne : Nat.card (E ⧸ derivedSubgroup E) ≠ 1 := by
    intro hq
    have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (derivedSubgroup E)
    change Nat.card E = Nat.card (E ⧸ derivedSubgroup E) *
      Nat.card (derivedSubgroup E) at hcard
    have hcard_eq : Nat.card E = Nat.card (derivedSubgroup E) := by
      rw [hq, Nat.one_mul] at hcard
      exact hcard
    have hder_eq : derivedSubgroup E = ⊤ := by
      apply Subgroup.eq_of_le_of_card_ge le_top
      simp [hcard_eq]
    exact hder_lt.ne hder_eq
  obtain ⟨p, hp, hpdiv⟩ := Nat.exists_prime_and_dvd hqne
  exact ⟨p, hp, hpdiv⟩

/-- Source-faithful choice at the start of the first assertion of `(9F)`:
choose a prime in the abelianization, use Corollary 9.5 for a cyclic Sylow
subgroup contained in `V`, and then choose an ambient subgroup of order `p`
inside it. -/
public theorem lemma99_exists_prime_sylow_order_p_subgroup
    {X : Type u} [Group X] [Finite X]
    {D E : Subgroup X} {t : X}
    (hEodd : Odd (Nat.card E))
    (hEne : E ≠ ⊥)
    (h95 : ∀ p : ℕ, Nat.Prime p →
      p ∣ Nat.card (E ⧸ derivedSubgroup E) →
      Lemma94AlternativeB D E t p) :
    ∃ p : ℕ, Nat.Prime p ∧
      p ∣ Nat.card (E ⧸ derivedSubgroup E) ∧
      ∃ S : Sylow p E, ∃ P : Subgroup X,
        IsCyclic (S : Subgroup E) ∧
        (S : Subgroup E).map E.subtype ≤ peterfalviV D t ∧
        P ≤ (S : Subgroup E).map E.subtype ∧
        Nat.card P = p ∧
        P ≤ E ⊓ peterfalviV D t ∧
        PeterfalviCentralizersTrivial D t P := by
  classical
  letI : Nontrivial E := (Subgroup.nontrivial_iff_ne_bot E).2 hEne
  obtain ⟨p, hp, hpAb⟩ := lemma99_exists_prime_dvd_abelianization hEodd
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨S, hScyclic, hSV, hStrivial⟩ := h95 p hp hpAb
  have hpE : p ∣ Nat.card E :=
    hpAb.trans (Subgroup.card_quotient_dvd_card
      (s := derivedSubgroup E))
  have hpS : p ∣ Nat.card (S : Subgroup E) :=
    S.dvd_card_of_dvd_card hpE
  obtain ⟨P0, hP0card⟩ :=
    Sylow.exists_subgroup_card_pow_prime (G := (S : Subgroup E))
      p (n := 1) (by simpa using hpS)
  let PE : Subgroup E := P0.map (S : Subgroup E).subtype
  let P : Subgroup X := PE.map E.subtype
  have hPEleS : PE ≤ (S : Subgroup E) := by
    simpa [PE] using Subgroup.map_subtype_le P0
  have hPleS : P ≤ (S : Subgroup E).map E.subtype := by
    change PE.map E.subtype ≤ (S : Subgroup E).map E.subtype
    exact Subgroup.map_mono hPEleS
  have hPcard : Nat.card P = p := by
    let e0 : P0 ≃* PE :=
      Subgroup.equivMapOfInjective P0 (S : Subgroup E).subtype
        (S : Subgroup E).subtype_injective
    let e1 : PE ≃* P :=
      Subgroup.equivMapOfInjective PE E.subtype E.subtype_injective
    calc
      Nat.card P = Nat.card PE := (Nat.card_congr e1.toEquiv).symm
      _ = Nat.card P0 := (Nat.card_congr e0.toEquiv).symm
      _ = p := by simpa using hP0card
  have hPleE : P ≤ E := by
    simpa [P] using Subgroup.map_subtype_le PE
  have hPleV : P ≤ peterfalviV D t := hPleS.trans hSV
  have hPtrivial : PeterfalviCentralizersTrivial D t P := by
    intro g hgP hgne k hkI hcomm
    exact hStrivial g (hPleS hgP) hgne k hkI hcomm
  exact ⟨p, hp, hpAb, S, P, hScyclic, hSV, hPleS, hPcard,
    le_inf hPleE hPleV, hPtrivial⟩

/-! ## Centralizing the Fitting subgroup -/

private theorem lemma99_pCore_le_mapped_pPrimeCore_fitting_of_ne
    {R : Type*} [Group R] [Finite R]
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hqp : q ≠ p) :
    pCore q R ≤
      (pPrimeCore p (fittingSubgroup R)).map (fittingSubgroup R).subtype := by
  classical
  let F : Subgroup R := fittingSubgroup R
  let QF : Subgroup F := (pCore q R).subgroupOf F
  have hqF : pCore q R ≤ F := by
    simpa [F] using pCore_le_fitting R q
  have hQFnormal : QF.Normal := by
    simpa [QF] using
      (inferInstance : (pCore q R).Normal).subgroupOf F
  have hQFq : IsPGroup q QF := by
    exact (pCore_isPGroup (G := R) (p := q)).of_equiv
      (Subgroup.subgroupOfEquivOfLe hqF).symm
  have hQFcop : Nat.Coprime p (Nat.card QF) := by
    obtain ⟨n, hcard⟩ := hQFq.exists_card_eq
    rw [hcard]
    exact ((Nat.coprime_primes (Fact.out : p.Prime)
      (Fact.out : q.Prime)).2 hqp.symm).pow_right n
  have hQFO : QF ≤ pPrimeCore p F := by
    exact le_sSup
      (show QF ∈ {H : Subgroup F |
          H.Normal ∧ Nat.Coprime p (Nat.card H)} from
        ⟨hQFnormal, hQFcop⟩)
  calc
    pCore q R = QF.map F.subtype := by
      simpa [QF, F] using
        (Subgroup.map_subgroupOf_eq_of_le hqF).symm
    _ ≤ (pPrimeCore p F).map F.subtype := Subgroup.map_mono hQFO
    _ = (pPrimeCore p (fittingSubgroup R)).map
        (fittingSubgroup R).subtype := by rfl

public theorem lemma99_pSubgroup_le_centralizer_fitting
    {R : Type*} [Group R] [Finite R]
    {p : ℕ} [Fact p.Prime]
    (P : Subgroup R)
    (hPp : IsPGroup p P)
    (hcyclic : ∀ S : Sylow p R, IsCyclic (S : Subgroup R))
    (hPcentral :
      P ≤ Subgroup.centralizer
        ((pPrimeCore p (fittingSubgroup R)).map
          (fittingSubgroup R).subtype : Set R)) :
    P ≤ Subgroup.centralizer (fittingSubgroup R : Set R) := by
  classical
  refine subgroup_le_centralizer_fitting_of_le_centralizer_pCores
    (G := R) (P := P) ?_
  intro q
  let qNat : ℕ := q.1.1
  have hqPrime : qNat.Prime := Nat.prime_of_mem_primeFactors q.1.2
  letI : Fact qNat.Prime := ⟨hqPrime⟩
  change P ≤ Subgroup.centralizer (pCore qNat R : Set R)
  by_cases hqp : qNat = p
  · simpa only [hqp] using
      (pSubgroup_le_centralizer_pCore_of_cyclic_sylow_fitting
        (G := R) (p := p) (P := P) hPp hcyclic)
  · exact hPcentral.trans (Subgroup.centralizer_le
      (lemma99_pCore_le_mapped_pPrimeCore_fitting_of_ne
        (R := R) (p := p) (q := qNat) hqp))

public theorem lemma99_order_p_fitting_centralizer_chain
    {R : Type*} [Group R] [Finite R]
    {p : ℕ} [Fact p.Prime]
    (P : Subgroup R)
    (hPcard : Nat.card P = p)
    (hcyclic : ∀ S : Sylow p R, IsCyclic (S : Subgroup R))
    (hPcentral :
      P ≤ Subgroup.centralizer
        ((pPrimeCore p (fittingSubgroup R)).map
          (fittingSubgroup R).subtype : Set R))
    (hsolv : Group.IsSolvable R) :
    P ≤ Subgroup.centralizer (fittingSubgroup R : Set R) ∧
      P ≤ fittingSubgroup R ∧
      P.subgroupOf (fittingSubgroup R) ≤
        Subgroup.center (fittingSubgroup R) := by
  have hPp : IsPGroup p P := by
    apply IsPGroup.of_card (n := 1)
    simpa using hPcard
  have hPcentralF :
      P ≤ Subgroup.centralizer (fittingSubgroup R : Set R) :=
    lemma99_pSubgroup_le_centralizer_fitting
      P hPp hcyclic hPcentral
  have hPF : P ≤ fittingSubgroup R :=
    hPcentralF.trans
      (centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv)
  refine ⟨hPcentralF, hPF, ?_⟩
  intro x hxP
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  simpa using ((Subgroup.mem_centralizer_iff.mp
    (hPcentralF hxP)) (y : R) y.property)

private theorem lemma99_all_sylow_cyclic_of_ambient_sylow
    {X : Type*} [Group X] [Finite X]
    {p : ℕ} [Fact p.Prime]
    (E R : Subgroup X) (hRE : R ≤ E)
    (S : Sylow p E) (hScyclic : IsCyclic (S : Subgroup E)) :
    ∀ Q : Sylow p R, IsCyclic (Q : Subgroup R) := by
  let fRE : R →* E :=
    { toFun := fun r : R => (⟨(r : X), hRE r.property⟩ : E)
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hfRE : Function.Injective fRE := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : E => (z : X)) hxy
  intro Q
  let QE : Subgroup E := (Q : Subgroup R).map fRE
  have hQEp : IsPGroup p QE := Q.isPGroup'.map fRE
  obtain ⟨S2, hQES2⟩ := hQEp.exists_le_sylow
  have hS2cyclic : IsCyclic (S2 : Subgroup E) :=
    (Sylow.equiv S2 S).isCyclic.mpr hScyclic
  have hQEsubCyclic : IsCyclic (QE.subgroupOf (S2 : Subgroup E)) := by
    letI : IsCyclic (S2 : Subgroup E) := hS2cyclic
    infer_instance
  have hQEcyclic : IsCyclic QE :=
    (Subgroup.subgroupOfEquivOfLe hQES2).isCyclic.mp hQEsubCyclic
  let eQ : (Q : Subgroup R) ≃* QE :=
    Subgroup.equivMapOfInjective (Q : Subgroup R) fRE hfRE
  exact eQ.isCyclic.mpr hQEcyclic

private theorem lemma99_ambient_order_p_fitting_centralizer_chain
    {X : Type*} [Group X] [Finite X]
    {p : ℕ} [Fact p.Prime]
    (R P : Subgroup X)
    (hPR : P ≤ R)
    (hPcard : Nat.card P = p)
    (hcyclic : ∀ S : Sylow p R, IsCyclic (S : Subgroup R))
    (hPcentral :
      P ≤ Subgroup.centralizer
        ((((pPrimeCore p (fittingSubgroup R)).map
          (fittingSubgroup R).subtype).map R.subtype : Subgroup X) : Set X))
    (hsolv : Group.IsSolvable R) :
    P ≤ Subgroup.centralizer
        (((fittingSubgroup R).map R.subtype : Subgroup X) : Set X) ∧
      P ≤ (fittingSubgroup R).map R.subtype ∧
      P.subgroupOf ((fittingSubgroup R).map R.subtype) ≤
        Subgroup.center ((fittingSubgroup R).map R.subtype) := by
  let PR : Subgroup R := P.subgroupOf R
  let A : Subgroup R :=
    (pPrimeCore p (fittingSubgroup R)).map (fittingSubgroup R).subtype
  have hPRcard : Nat.card PR = p := by
    simpa [PR] using (natCard_subgroupOf_eq P R hPR).trans hPcard
  have hPRcentral : PR ≤ Subgroup.centralizer (A : Set R) := by
    intro x hxP
    rw [Subgroup.mem_centralizer_iff]
    intro y hyA
    apply Subtype.ext
    have hxPX : (x : X) ∈ P := hxP
    have hyAX : (y : X) ∈ A.map R.subtype :=
      Subgroup.mem_map_of_mem R.subtype hyA
    have hcommX := (Subgroup.mem_centralizer_iff.mp
      (hPcentral hxPX)) (y : X) hyAX
    simpa using hcommX
  obtain ⟨hPRcentralF, hPRF, hPRcenter⟩ :=
    lemma99_order_p_fitting_centralizer_chain
      PR hPRcard hcyclic (by simpa [A] using hPRcentral) hsolv
  have hPcentralFX :
      P ≤ Subgroup.centralizer
        (((fittingSubgroup R).map R.subtype : Subgroup X) : Set X) := by
    intro x hxP
    rw [Subgroup.mem_centralizer_iff]
    intro y hyF
    rcases Subgroup.mem_map.mp hyF with ⟨yR, hyRF, rfl⟩
    let xR : R := ⟨x, hPR hxP⟩
    have hxPR : xR ∈ PR := hxP
    have hcommR := (Subgroup.mem_centralizer_iff.mp
      (hPRcentralF hxPR)) yR hyRF
    simpa [xR] using congrArg Subtype.val hcommR
  have hPF : P ≤ (fittingSubgroup R).map R.subtype := by
    intro x hxP
    let xR : R := ⟨x, hPR hxP⟩
    exact Subgroup.mem_map.mpr
      ⟨xR, hPRF (show xR ∈ PR from hxP), rfl⟩
  have hPcenter :
      P.subgroupOf ((fittingSubgroup R).map R.subtype) ≤
        Subgroup.center ((fittingSubgroup R).map R.subtype) := by
    intro x hxP
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hxPX : (x : X) ∈ P := hxP
    have hyFX : (y : X) ∈
        ((fittingSubgroup R).map R.subtype : Subgroup X) := y.property
    exact (Subgroup.mem_centralizer_iff.mp
      (hPcentralFX hxPX)) (y : X) hyFX
  exact ⟨hPcentralFX, hPF, hPcenter⟩

/-! ## The first centralizer step of (9F) -/

private theorem lemma99_subgroupCentralizerIn_eq_bot
    {X : Type*} [Group X]
    {D K P : Subgroup X} {t : X}
    (hKset : (K : Set X) = peterfalviKSet D t)
    (hPne : P ≠ ⊥)
    (hPtrivial : PeterfalviCentralizersTrivial D t P) :
    subgroupCentralizerIn K P = ⊥ := by
  obtain ⟨g, hgP, hgnot⟩ :=
    SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hPne)
  have hgne : g ≠ 1 := by simpa using hgnot
  rw [Subgroup.eq_bot_iff_forall]
  intro k hk
  have hkI : k ∈ peterfalviKSet D t := by
    rw [← hKset]
    exact hk.1
  have hcomm : k * g = g * k :=
    ((Subgroup.mem_centralizer_iff.mp hk.2) g hgP).symm
  exact hPtrivial g hgP hgne k hkI hcomm

/-- The fixed-point count used in `[II1; 4.3(a)]`: a `q`-subgroup acting
fixed-point-freely by conjugation on `K` forces `q ∤ |K|`. -/
private theorem lemma99_prime_not_dvd_card_of_fixedPointFree
    {X : Type u} [Group X] [Finite X]
    {K U : Subgroup X} {q : ℕ}
    (hq : Nat.Prime q)
    (hUq : IsPGroup q U)
    (hUnormK : U ≤ Subgroup.normalizer (K : Set X))
    (hfix : subgroupCentralizerIn K U = ⊥) :
    ¬ q ∣ Nat.card K := by
  classical
  letI : Fact q.Prime := ⟨hq⟩
  letI : Subgroup.Normalizes U K := ⟨hUnormK⟩
  intro hqK
  have hone_fixed : (1 : K) ∈ MulAction.fixedPoints U K := by
    simp [MulAction.mem_fixedPoints]
  obtain ⟨x, hxfix, h1x⟩ :=
    hUq.exists_fixed_point_of_prime_dvd_card_of_fixed_point
      (α := K) hqK hone_fixed
  have hfixed_eq :
      fixedPointSubgroup (↥U) (↥K) =
        (subgroupCentralizerIn K U).subgroupOf K := by
    simpa using
      fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn K U hUnormK
  have hxfix_sub : x ∈ fixedPointSubgroup (↥U) (↥K) := by
    simpa [fixedPointSubgroup] using hxfix
  have hxCsub : x ∈ (subgroupCentralizerIn K U).subgroupOf K := by
    simpa [hfixed_eq] using hxfix_sub
  have hxC : (x : X) ∈ subgroupCentralizerIn K U := by
    simpa [Subgroup.mem_subgroupOf] using hxCsub
  have hxbot : (x : X) ∈ (⊥ : Subgroup X) := by
    simpa [hfix] using hxC
  have hxone : x = 1 := by
    apply Subtype.ext
    simpa using hxbot
  exact h1x hxone.symm

/-- Under the temporary negation of Lemma 9.9, the Fitting subgroup of the
normal fixed-point section has order coprime to the Peterfalvi complement.

For every common prime `q`, a Sylow `q`-subgroup of the Fitting subgroup is
characteristic, hence gives a nontrivial normal subgroup of `V`.  Its
Peterfalvi centralizer is trivial by the negated conclusion, while the
`q`-group fixed-point count says `q ∤ |K|`, a contradiction. -/
private theorem lemma99_fitting_coprime_peterfalviK
    {X : Type u} [Group X] [Finite X]
    {D K R : Subgroup X} {t : X}
    (hRleV : R ≤ peterfalviV D t)
    (hRnormalV : (R.subgroupOf (peterfalviV D t)).Normal)
    (hRnormK : R ≤ Subgroup.normalizer (K : Set X))
    (hKset : (K : Set X) = peterfalviKSet D t)
    (hNoNormal : ∀ Y : Subgroup X,
      Y ≤ peterfalviV D t →
        Y ≠ ⊥ →
        (Y.subgroupOf (peterfalviV D t)).Normal →
        ¬ HasNontrivialPeterfalviCentralizer D t Y) :
    Nat.Coprime (Nat.card (fittingSubgroup R)) (Nat.card K) := by
  classical
  by_contra hcop
  obtain ⟨q, hq, hqF, hqK⟩ :=
    Nat.Prime.not_coprime_iff_dvd.mp hcop
  letI : Fact q.Prime := ⟨hq⟩
  let F0 : Subgroup R := fittingSubgroup R
  let Q : Sylow q F0 := default
  have hQne : (Q : Subgroup F0) ≠ ⊥ :=
    Sylow.ne_bot_of_dvd_card Q (by simpa [F0] using hqF)
  have hQnormal : (Q : Subgroup F0).Normal :=
    Group.IsNilpotent.sylow_normal
      (inferInstance : Group.IsNilpotent F0) q Q
  have hQchar : (Q : Subgroup F0).Characteristic :=
    Sylow.characteristic_of_normal Q hQnormal
  let Q0 : Subgroup R := (Q : Subgroup F0).map F0.subtype
  have hQ0char : Q0.Characteristic := by
    letI : F0.Characteristic := fittingSubgroup_characteristic
    letI : (Q : Subgroup F0).Characteristic := hQchar
    simpa [Q0, F0] using
      characteristic_map_subtype_of_characteristic
        (G := R) F0 (Q : Subgroup F0)
  let U : Subgroup X := Q0.map R.subtype
  have hUleR : U ≤ R := by
    simpa [U] using Subgroup.map_subtype_le Q0
  have hUleV : U ≤ peterfalviV D t := hUleR.trans hRleV
  have hUne : U ≠ ⊥ := by
    intro hUbot
    have hQ0bot : Q0 = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective
        (H := Q0) (f := R.subtype) R.subtype_injective).mp
        (by simpa [U] using hUbot)
    have hQbot : (Q : Subgroup F0) = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective
        (H := (Q : Subgroup F0)) (f := F0.subtype)
        F0.subtype_injective).mp
        (by simpa [Q0] using hQ0bot)
    exact hQne hQbot
  have hUnormalV :
      (U.subgroupOf (peterfalviV D t)).Normal := by
    exact normal_subgroupOf_map_of_characteristic_of_normal
      R U (peterfalviV D t) hRleV hRnormalV Q0 hQ0char rfl hUleV
  have hUnormK : U ≤ Subgroup.normalizer (K : Set X) :=
    hUleR.trans hRnormK
  have hUq : IsPGroup q U := by
    simpa [U, Q0] using
      IsPGroup.map (p := q)
        (H := (Q : Subgroup F0).map F0.subtype)
        (IsPGroup.map (p := q) (H := (Q : Subgroup F0))
          Q.isPGroup' F0.subtype)
        R.subtype
  have hfix : subgroupCentralizerIn K U = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    by_contra hxne
    exact (hNoNormal U hUleV hUne hUnormalV)
      ⟨x, (by rw [← hKset]; exact hx.1), hx.2, hxne⟩
  exact lemma99_prime_not_dvd_card_of_fixedPointFree
    hq hUq hUnormK hfix hqK

private theorem lemma99_p_le_centralizer_mapped_pPrimeCore_fitting
    {X : Type u} [Group X] [Finite X]
    {D K R P : Subgroup X} {t : X} {p : ℕ}
    (hp : Nat.Prime p)
    (hPcard : Nat.card P = p)
    (hPleR : P ≤ R)
    (hRleV : R ≤ peterfalviV D t)
    (hRnormalV : (R.subgroupOf (peterfalviV D t)).Normal)
    (hRnormK : R ≤ Subgroup.normalizer (K : Set X))
    (hRodd : Odd (Nat.card R))
    (hKset : (K : Set X) = peterfalviKSet D t)
    (hPtrivial : PeterfalviCentralizersTrivial D t P)
    (hNoNormal : ∀ Y : Subgroup X,
      Y ≤ peterfalviV D t →
        Y ≠ ⊥ →
        (Y.subgroupOf (peterfalviV D t)).Normal →
        ¬ HasNontrivialPeterfalviCentralizer D t Y)
    (h97 : peterfalviV D t ⊓
      Subgroup.centralizer (peterfalviKSet D t) = ⊥) :
    P ≤ Subgroup.centralizer
      (((pPrimeCore p (fittingSubgroup R)).map
        (fittingSubgroup R).subtype).map R.subtype : Set X) := by
  classical
  let F0 : Subgroup R := fittingSubgroup R
  let A0 : Subgroup R :=
    (pPrimeCore p F0).map F0.subtype
  let A : Subgroup X := A0.map R.subtype
  have hAleR : A ≤ R := by
    simpa [A] using Subgroup.map_subtype_le A0
  have hA0normal : A0.Normal := by
    haveI : F0.Characteristic := fittingSubgroup_characteristic
    haveI : (pPrimeCore p F0).Characteristic :=
      pPrimeCore_characteristic (G := F0) (p := p)
    have hA0char : A0.Characteristic := by
      simpa [A0] using
        characteristic_map_subtype_of_characteristic (G := R) F0
          (pPrimeCore p F0)
    letI : A0.Characteristic := hA0char
    exact inferInstance
  have hAnormalR : (A.subgroupOf R).Normal := by
    rw [show A.subgroupOf R = A0 by
      simpa [A] using subgroupOf_map_subtype_eq A0]
    exact hA0normal
  have hRnormA : R ≤ Subgroup.normalizer (A : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAleR).mp hAnormalR
  have hPnormA : P ≤ Subgroup.normalizer (A : Set X) :=
    hPleR.trans hRnormA
  have hAPnormK : A ⊔ P ≤ Subgroup.normalizer (K : Set X) :=
    (sup_le hAleR hPleR).trans hRnormK
  have hAodd : Odd (Nat.card A) := by
    exact hRodd.of_dvd_nat (Subgroup.card_dvd_of_le hAleR)
  have hPne : P ≠ ⊥ := by
    intro hPbot
    have hcard1 : Nat.card P = 1 := by simp [hPbot]
    exact hp.ne_one (hPcard.symm.trans hcard1)
  have hSC : subgroupCentralizerIn K P = ⊥ :=
    lemma99_subgroupCentralizerIn_eq_bot hKset hPne hPtrivial
  letI : Fact p.Prime := ⟨hp⟩
  have hPp : IsPGroup p P := by
    apply IsPGroup.of_card (n := 1)
    simp [hPcard]
  have hAcard : Nat.card A = Nat.card (pPrimeCore p F0) := by
    calc
      Nat.card A = Nat.card A0 := by
        simpa [A] using
          (Subgroup.card_map_of_injective
            (K := A0) (f := R.subtype) R.subtype_injective)
      _ = Nat.card (pPrimeCore p F0) := by
        simpa [A0] using
          (Subgroup.card_map_of_injective
            (K := pPrimeCore p F0) (f := F0.subtype)
            F0.subtype_injective)
  have hcopPA : Nat.Coprime (Nat.card P) (Nat.card A) := by
    rw [hPcard, hAcard]
    exact pPrimeCore_coprime_card (G := F0) (p := p)
  have hcopFK : Nat.Coprime (Nat.card F0) (Nat.card K) := by
    simpa [F0] using lemma99_fitting_coprime_peterfalviK
      hRleV hRnormalV hRnormK hKset hNoNormal
  have hAdvdF : Nat.card A ∣ Nat.card F0 := by
    rw [hAcard]
    exact Subgroup.card_subgroup_dvd_card (pPrimeCore p F0)
  have hcopAK : Nat.Coprime (Nat.card A) (Nat.card K) :=
    Nat.Coprime.of_dvd_left hAdvdF hcopFK
  have hPnormK : P ≤ Subgroup.normalizer (K : Set X) :=
    le_sup_right.trans hAPnormK
  have hpNotDvdK : ¬ p ∣ Nat.card K :=
    lemma99_prime_not_dvd_card_of_fixedPointFree
      hp hPp hPnormK hSC
  have hcopPK : Nat.Coprime (Nat.card P) (Nat.card K) := by
    rw [hPcard]
    exact hp.coprime_iff_not_dvd.mpr hpNotDvdK
  have hoddAP : Odd (Nat.card (A ⊔ P : Subgroup X)) :=
    hRodd.of_dvd_nat
      (Subgroup.card_dvd_of_le (sup_le hAleR hPleR))
  have hcommC : ⁅A, P⁆ ≤ Subgroup.centralizer (K : Set X) :=
    ig1114_i_commutator_le_centralizer_of_fixedPointFree
      K A P hPnormA hAPnormK hoddAP hcopPA hcopAK hcopPK
        (by simpa [hPcard] using hp) hSC
  have hAleV : A ≤ peterfalviV D t := hAleR.trans hRleV
  have hPleV : P ≤ peterfalviV D t := hPleR.trans hRleV
  have hcommV : ⁅A, P⁆ ≤ peterfalviV D t := by
    rw [Subgroup.commutator_le]
    intro a ha q hq
    have haV := hAleV ha
    have hqV := hPleV hq
    exact (peterfalviV D t).mul_mem
      ((peterfalviV D t).mul_mem
        ((peterfalviV D t).mul_mem haV hqV)
        ((peterfalviV D t).inv_mem haV))
      ((peterfalviV D t).inv_mem hqV)
  have hcommI : ⁅A, P⁆ ≤
      Subgroup.centralizer (peterfalviKSet D t : Set X) := by
    simpa [hKset] using hcommC
  have hcommbot : ⁅A, P⁆ = ⊥ := by
    apply le_bot_iff.mp
    rw [← h97]
    exact le_inf hcommV hcommI
  rw [Subgroup.commutator_comm] at hcommbot
  exact (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hcommbot

public theorem lemma99_first_nineF_p_le_centralizer_pPrimeCore
    {X : Type u} [Group X] [Finite X]
    {D E P : Subgroup X} {t : X} {p : ℕ}
    (hp : Nat.Prime p)
    (hED : E ≤ D)
    (hEN : (E.subgroupOf D).Normal)
    (hDodd : Odd (Nat.card D))
    (h43c : II1Lemma43cConclusion D t)
    (h97 : peterfalviV D t ⊓
      Subgroup.centralizer (peterfalviKSet D t) = ⊥)
    (hPcard : Nat.card P = p)
    (hPleR : P ≤ E ⊓ peterfalviV D t)
    (hPtrivial : PeterfalviCentralizersTrivial D t P)
    (hNoNormal : ∀ Y : Subgroup X,
      Y ≤ peterfalviV D t →
        Y ≠ ⊥ →
        (Y.subgroupOf (peterfalviV D t)).Normal →
        ¬ HasNontrivialPeterfalviCentralizer D t Y) :
    let R : Subgroup X := E ⊓ peterfalviV D t
    let A : Subgroup X :=
      ((pPrimeCore p (fittingSubgroup R)).map
        (fittingSubgroup R).subtype).map R.subtype
    P ≤ Subgroup.centralizer (A : Set X) := by
  let K : Subgroup X := Subgroup.closure (peterfalviKSet D t)
  let V : Subgroup X := peterfalviV D t
  let R : Subgroup X := E ⊓ V
  have hRleD : R ≤ D := inf_le_left.trans hED
  have hRleV : R ≤ V := inf_le_right
  have hVleD : V ≤ D := by
    simp [V, peterfalviV]
  have hRnormalV : (R.subgroupOf V).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hRleV]
    intro r v hr hv
    refine ⟨?_, ?_⟩
    · exact ((Subgroup.normal_subgroupOf_iff hED).mp hEN)
        r v hr.1 (hVleD hv)
    · exact V.mul_mem (V.mul_mem hv hr.2) (V.inv_mem hv)
  have hRodd : Odd (Nat.card R) :=
    hDodd.of_dvd_nat (Subgroup.card_dvd_of_le hRleD)
  have hKleD : K ≤ D := by
    simpa [K] using h43c.closure_le
  have hKnormalD : (K.subgroupOf D).Normal := by
    simpa [K] using h43c.normal
  have hDnormK : D ≤ Subgroup.normalizer (K : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKleD).mp hKnormalD
  have hRnormK : R ≤ Subgroup.normalizer (K : Set X) :=
    hRleD.trans hDnormK
  have hKset : (K : Set X) = peterfalviKSet D t := by
    simpa [K] using h43c.closure_eq_set
  simpa [R, V] using
    (lemma99_p_le_centralizer_mapped_pPrimeCore_fitting
      (D := D) (K := K) (R := R) (P := P) (t := t) (p := p)
      hp hPcard hPleR (by simpa [V] using hRleV)
      (by simpa [V] using hRnormalV) hRnormK hRodd hKset hPtrivial
      hNoNormal h97)

public theorem lemma99_first_nineF_fitting_center
    {X : Type u} [Group X] [Finite X]
    {D E P : Subgroup X} {t : X} {p : ℕ}
    (S : Sylow p E)
    (hp : Nat.Prime p)
    (hED : E ≤ D)
    (hEN : (E.subgroupOf D).Normal)
    (hDodd : Odd (Nat.card D))
    (h43c : II1Lemma43cConclusion D t)
    (h97 : peterfalviV D t ⊓
      Subgroup.centralizer (peterfalviKSet D t) = ⊥)
    (hScyclic : IsCyclic (S : Subgroup E))
    (hPcard : Nat.card P = p)
    (hPleR : P ≤ E ⊓ peterfalviV D t)
    (hPtrivial : PeterfalviCentralizersTrivial D t P)
    (hNoNormal : ∀ Y : Subgroup X,
      Y ≤ peterfalviV D t →
        Y ≠ ⊥ →
        (Y.subgroupOf (peterfalviV D t)).Normal →
        ¬ HasNontrivialPeterfalviCentralizer D t Y) :
    let R : Subgroup X := E ⊓ peterfalviV D t
    let F : Subgroup X := (fittingSubgroup R).map R.subtype
    P ≤ Subgroup.centralizer (F : Set X) ∧
      P ≤ F ∧
      P.subgroupOf F ≤ Subgroup.center F := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let R : Subgroup X := E ⊓ peterfalviV D t
  let F : Subgroup X := (fittingSubgroup R).map R.subtype
  let A : Subgroup X :=
    ((pPrimeCore p (fittingSubgroup R)).map
      (fittingSubgroup R).subtype).map R.subtype
  have hPcentralA : P ≤ Subgroup.centralizer (A : Set X) := by
    simpa [R, A] using
      (lemma99_first_nineF_p_le_centralizer_pPrimeCore
        (D := D) (E := E) (P := P) (t := t) (p := p)
        hp hED hEN hDodd h43c h97 hPcard hPleR hPtrivial hNoNormal)
  have hRleE : R ≤ E := inf_le_left
  have hRleD : R ≤ D := hRleE.trans hED
  have hRodd : Odd (Nat.card R) :=
    hDodd.of_dvd_nat (Subgroup.card_dvd_of_le hRleD)
  have hRsolv : Group.IsSolvable R := odd_order_theorem R hRodd
  have hcyclic : ∀ Q : Sylow p R, IsCyclic (Q : Subgroup R) :=
    lemma99_all_sylow_cyclic_of_ambient_sylow E R hRleE S hScyclic
  simpa [R, F, A] using
    lemma99_ambient_order_p_fitting_centralizer_chain
      R P hPleR hPcard hcyclic hPcentralA hRsolv

/-! ## Second assertion of `(9F)` -/

private theorem lemma99_conjNormal_ker_eq_centralizer
    {G : Type*} [Group G] {H : Subgroup G} [H.Normal] :
    (MulAut.conjNormal (H := H)).ker = Subgroup.centralizer (H : Set G) := by
  let phi : G →* MulAut H := MulAut.conjNormal (H := H)
  ext x
  rw [Subgroup.mem_centralizer_iff, MonoidHom.mem_ker]
  constructor
  · intro hx h hh
    have hx_apply : phi x ⟨h, hh⟩ = ⟨h, hh⟩ := by
      change (MulAut.conjNormal (H := H) x) ⟨h, hh⟩ = ⟨h, hh⟩
      rw [hx]
      rfl
    have hconj : x * h * x⁻¹ = h := by
      simpa [phi, MulAut.conjNormal_apply, MulAut.conj_apply] using
        congrArg Subtype.val hx_apply
    have heq := congrArg (fun y : G => y * x) hconj
    simpa [mul_assoc] using heq.symm
  · intro hx
    ext h
    have hcomm : (h : G) * x = x * h := hx h h.2
    have hconj : x * (h : G) * x⁻¹ = h := by
      calc
        x * (h : G) * x⁻¹ = ((h : G) * x) * x⁻¹ := by rw [hcomm]
        _ = h := by simp [mul_assoc]
    simpa [phi, MulAut.conjNormal_apply, MulAut.conj_apply] using hconj

private theorem lemma99_fitting_quotient_commutative
    {R : Type*} [Group R] [Finite R]
    (hsolv : Group.IsSolvable R)
    (hFcyclic : IsCyclic (fittingSubgroup R)) :
    IsMulCommutative (R ⧸ fittingSubgroup R) := by
  letI : IsCyclic (fittingSubgroup R) := hFcyclic
  have hcent_eq :
      Subgroup.centralizer (fittingSubgroup R : Set R) = fittingSubgroup R := by
    apply le_antisymm
    · exact centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv
    · exact Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance
  let phi : R →* MulAut (fittingSubgroup R) :=
    MulAut.conjNormal (H := fittingSubgroup R)
  have hker : phi.ker = fittingSubgroup R := by
    simpa [phi, lemma99_conjNormal_ker_eq_centralizer] using hcent_eq
  have hAutComm : IsMulCommutative (MulAut (fittingSubgroup R)) := by
    refine ⟨⟨fun alpha beta => ?_⟩⟩
    apply (IsCyclic.mulAutMulEquiv (fittingSubgroup R)).injective
    simpa only [map_mul] using
      (mul_comm
        ((IsCyclic.mulAutMulEquiv (fittingSubgroup R)) alpha)
        ((IsCyclic.mulAutMulEquiv (fittingSubgroup R)) beta))
  letI : IsMulCommutative (MulAut (fittingSubgroup R)) := hAutComm
  let equivRange :
      R ⧸ fittingSubgroup R ≃* phi.range :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivRange phi)
  refine ⟨⟨fun x y => ?_⟩⟩
  apply equivRange.injective
  simpa only [map_mul] using (mul_comm' (equivRange x) (equivRange y))

private theorem lemma99_commutator_le_fitting_of_cyclic
    {R : Type*} [Group R] [Finite R]
    (hsolv : Group.IsSolvable R)
    (hFcyclic : IsCyclic (fittingSubgroup R)) :
    derivedSubgroup R ≤ fittingSubgroup R := by
  letI : (fittingSubgroup R).Normal := inferInstance
  simpa only [derivedSubgroup, derivedSeries_one] using
    (Subgroup.Normal.quotient_commutative_iff_commutator_le).mp
      (lemma99_fitting_quotient_commutative hsolv hFcyclic)

public theorem lemma99_derived_inf_le_of_factorization
    {X : Type u} [Group X] [Finite X]
    {E K R F V : Subgroup X}
    (hRE : R ≤ E)
    (hFR : F ≤ R)
    (hFV : F ≤ V)
    (hKnormalE : (K.subgroupOf E).Normal)
    (hKRtop : K.subgroupOf E ⊔ R.subgroupOf E = ⊤)
    (hRcommF : ⁅R, R⁆ ≤ F)
    (hKdisjV : Disjoint K V) :
    (derivedSubgroup E).map E.subtype ⊓ V ≤ F := by
  classical
  let KE : Subgroup E := K.subgroupOf E
  let RE : Subgroup E := R.subgroupOf E
  let FE : Subgroup E := F.subgroupOf E
  letI : KE.Normal := by simpa [KE] using hKnormalE
  have hREcommFE : ⁅RE, RE⁆ ≤ FE := by
    rw [← Subgroup.map_le_map_iff_of_injective E.subtype_injective]
    calc
      (⁅RE, RE⁆).map E.subtype = ⁅R, R⁆ := by
        simpa [RE] using commutator_subgroupOf_map_eq E R R hRE hRE
      _ ≤ F := hRcommF
      _ = FE.map E.subtype := by
        symm
        simpa [FE] using
          (Subgroup.map_subgroupOf_eq_of_le (H := F) (K := E)
            (hFR.trans hRE))
  have hderSup : derivedSubgroup E ≤ KE ⊔ FE :=
    (lemma_6_5_derived_le_sup_commutator (K := KE) (U := RE)
      (by simpa [KE, RE] using hKRtop)).trans
      (sup_le_sup_left hREcommFE KE)
  intro x hx
  rcases Subgroup.mem_map.mp hx.1 with ⟨e, heDer, hex⟩
  have heSup : e ∈ KE ⊔ FE := hderSup heDer
  rcases Subgroup.mem_sup_of_normal_left.mp heSup with
    ⟨k, hkK, f, hfF, hkfe⟩
  have heV : (e : X) ∈ V := by
    change E.subtype e ∈ V
    rw [hex]
    exact hx.2
  have hfV : (f : X) ∈ V := hFV hfF
  have hk_eq : (k : X) = (e : X) * (f : X)⁻¹ := by
    rw [← hkfe]
    simp [mul_assoc]
  have hkV : (k : X) ∈ V := by
    rw [hk_eq]
    exact V.mul_mem heV (V.inv_mem hfV)
  have hkOne : (k : X) = 1 := by
    have hkBot : (k : X) ∈ (⊥ : Subgroup X) :=
      (Subgroup.disjoint_def.mp hKdisjV) hkK hkV
    simpa using hkBot
  have he_eq_f : (e : X) = (f : X) := by
    rw [← hkfe]
    simp [hkOne]
  change x ∈ F
  rw [← hex]
  change (e : X) ∈ F
  rw [he_eq_f]
  exact hfF

public theorem lemma99_second_nineF
    {X : Type u} [Group X] [Finite X]
    {D E : Subgroup X} {t : X}
    (hED : E ≤ D)
    (hDodd : Odd (Nat.card D))
    (h43c : II1Lemma43cConclusion D t)
    (h96 : Corollary96Conclusion D E t)
    (hFcyclic :
      let R : Subgroup X := E ⊓ peterfalviV D t
      let F : Subgroup X := (fittingSubgroup R).map R.subtype
      IsCyclic F) :
    let R : Subgroup X := E ⊓ peterfalviV D t
    let F : Subgroup X := (fittingSubgroup R).map R.subtype
    (derivedSubgroup E).map E.subtype ⊓ peterfalviV D t ≤ F := by
  classical
  let K : Subgroup X := Subgroup.closure (peterfalviKSet D t)
  let V : Subgroup X := peterfalviV D t
  let R : Subgroup X := E ⊓ V
  let F : Subgroup X := (fittingSubgroup R).map R.subtype
  have hKE : K ≤ E := by
    simpa [K] using h96.closure_le_derived.trans
      (Subgroup.map_subtype_le (derivedSubgroup E))
  have hRE : R ≤ E := inf_le_left
  have hFR : F ≤ R := by
    simpa [F] using Subgroup.map_subtype_le (fittingSubgroup R)
  have hFV : F ≤ V := hFR.trans inf_le_right
  have hKnormalD : (K.subgroupOf D).Normal := by
    simpa [K] using h43c.normal
  have hDnormK : D ≤ Subgroup.normalizer (K : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (by simpa [K] using h43c.closure_le)).mp hKnormalD
  have hKnormalE : (K.subgroupOf E).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKE).mpr
      (hED.trans hDnormK)
  have hKdisjV : Disjoint K V := by
    rw [Subgroup.disjoint_def]
    intro x hxK hxV
    have hxD : x ∈ D := by simpa [K] using h43c.closure_le hxK
    let xD : D := ⟨x, hxD⟩
    have hxKV : xD ∈
        (K.subgroupOf D) ⊓ (V.subgroupOf D) := ⟨hxK, hxV⟩
    have hxbot : xD ∈ (⊥ : Subgroup D) := by
      rw [← h43c.isComplement'.disjoint.eq_bot]
      exact hxKV
    exact congrArg Subtype.val (by simpa using hxbot)
  have hKRmul :
      (K.subgroupOf E : Set E) * (R.subgroupOf E : Set E) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    have hxE : (x : X) ∈ (E : Set X) := x.property
    rw [show (E : Set X) = (K : Set X) * (R : Set X) by
      simpa [K, R, V] using h96.eq_mul_fixed] at hxE
    rcases Set.mem_mul.mp hxE with ⟨k, hk, r, hr, hkr⟩
    let kE : E := ⟨k, hKE hk⟩
    let rE : E := ⟨r, hRE hr⟩
    exact Set.mem_mul.mpr ⟨kE, hk, rE, hr, Subtype.ext hkr⟩
  have hKRtop : K.subgroupOf E ⊔ R.subgroupOf E = ⊤ := by
    apply top_unique
    intro x _hx
    rcases Set.mem_mul.mp (by simp [hKRmul] : x ∈
        (K.subgroupOf E : Set E) * (R.subgroupOf E : Set E)) with
      ⟨k, hk, r, hr, hkr⟩
    rw [← hkr]
    exact (K.subgroupOf E ⊔ R.subgroupOf E).mul_mem
      (Subgroup.mem_sup_left hk) (Subgroup.mem_sup_right hr)
  have hRodd : Odd (Nat.card R) :=
    hDodd.of_dvd_nat (Subgroup.card_dvd_of_le (hRE.trans hED))
  have hRsolv : Group.IsSolvable R := odd_order_theorem R hRodd
  have hFitCyclic : IsCyclic (fittingSubgroup R) := by
    let e : fittingSubgroup R ≃* F :=
      Subgroup.equivMapOfInjective
        (fittingSubgroup R) R.subtype R.subtype_injective
    exact e.isCyclic.mpr (by simpa [F, R, V] using hFcyclic)
  have hRderFit : derivedSubgroup R ≤ fittingSubgroup R :=
    lemma99_commutator_le_fitting_of_cyclic hRsolv hFitCyclic
  have hRcommF : ⁅R, R⁆ ≤ F := by
    rw [← Subgroup.map_subtype_commutator R]
    exact Subgroup.map_mono hRderFit
  simpa [R, F, V] using
    lemma99_derived_inf_le_of_factorization hRE hFR hFV
      hKnormalE hKRtop hRcommF hKdisjV

/-! ## Corollary 8.5 maximal-subgroup glue -/

/-- From one nontrivial element of `F` with a nontrivial `K`-centralizer,
choose a subgroup `H ≤ F` maximal with that property. -/
public theorem lemma99_exists_maximal_nontrivial_centralizer
    {X : Type u} [Group X] [Finite X]
    {D F K : Subgroup X} {t x k : X}
    (hxF : x ∈ F) (hxne : x ≠ 1)
    (hkK : k ∈ K) (hkne : k ≠ 1)
    (hKset : (K : Set X) = peterfalviKSet D t)
    (hcomm : k * x = x * k) :
    ∃ H : Subgroup X,
      H ≤ F ∧ H ≠ ⊥ ∧
      HasNontrivialPeterfalviCentralizer D t H ∧
      ∀ L : Subgroup X,
        H ≤ L → L ≤ F →
          HasNontrivialPeterfalviCentralizer D t L → L = H := by
  classical
  let H0 : Subgroup X := Subgroup.zpowers x
  have hH0F : H0 ≤ F := by
    simpa [H0] using Subgroup.zpowers_le.mpr hxF
  have hH0ne : H0 ≠ ⊥ := by
    simpa [H0] using Subgroup.zpowers_ne_bot.mpr hxne
  have hkI : k ∈ peterfalviKSet D t := by
    rw [← hKset]
    exact hkK
  have hkCH0 : k ∈ Subgroup.centralizer (H0 : Set X) := by
    change k ∈ Subgroup.centralizer (Subgroup.zpowers x : Set X)
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
      Subgroup.mem_centralizer_iff]
    intro y hy
    rcases Set.mem_singleton_iff.mp hy with rfl
    exact hcomm.symm
  have hH0central : HasNontrivialPeterfalviCentralizer D t H0 :=
    ⟨k, hkI, hkCH0, hkne⟩
  let s : Set (Subgroup X) :=
    {H | H ≤ F ∧ HasNontrivialPeterfalviCentralizer D t H}
  have hsfin : s.Finite := Set.toFinite s
  have hsne : s.Nonempty := ⟨H0, hH0F, hH0central⟩
  obtain ⟨H, hHs, hHmax⟩ := hsfin.exists_maximal hsne
  have hHne : H ≠ ⊥ := by
    intro hHbot
    have hH0H : H0 ≤ H := by
      apply hHmax ⟨hH0F, hH0central⟩
      simp [hHbot]
    exact hH0ne (le_antisymm (hH0H.trans (by simp [hHbot])) bot_le)
  refine ⟨H, hHs.1, hHne, hHs.2, ?_⟩
  intro L hHL hLF hLcentral
  exact le_antisymm (hHmax ⟨hLF, hLcentral⟩ hHL) hHL

/-- The subtype normalizer factorization obtained from Corollary 8.5 after
choosing `H ≤ F` maximal with `C_I(H) ≠ 1`. -/
public theorem lemma99_normalizer_subgroupOf_eq_mul_of_corollary85
    {X : Type u} [Group X] [Finite X]
    {M F H P : Subgroup X} {t u0 : X}
    (hHF : H ≤ F)
    (hFV : F ≤
      (M ⊓ rightConjugate M t) ⊓
        Subgroup.centralizer ({u0} : Set X))
    (hPF : P ≤ F)
    (hPcentral : P ≤ Subgroup.centralizer (F : Set X))
    (hHcentral : HasNontrivialPeterfalviCentralizer
      (M ⊓ rightConjugate M t) t H)
    (hHmax : ∀ L : Subgroup X,
      H ≤ L → L ≤ F →
        HasNontrivialPeterfalviCentralizer
          (M ⊓ rightConjugate M t) t L →
        L = H)
    (h85 : Corollary85Conclusion M t u0 H P) :
    (Subgroup.normalizer (H.subgroupOf F : Set F) : Set F) =
      (H.subgroupOf F : Set F) * (P.subgroupOf F : Set F) := by
  classical
  let V0 : Subgroup X :=
    (M ⊓ rightConjugate M t) ⊓
      Subgroup.centralizer ({u0} : Set X)
  let V1 : Subgroup X := normalizerIn V0 H
  let L : Subgroup X :=
    (V1 ⊓ Subgroup.centralizer (h85.J : Set X)) ⊓ F
  have hHV0 : H ≤ V0 := by
    simpa [V0] using hHF.trans hFV
  have hHV1 : H ≤ V1 := by
    intro x hxH
    exact ⟨hHV0 hxH, Subgroup.le_normalizer hxH⟩
  have hHCJ : H ≤ Subgroup.centralizer (h85.J : Set X) := by
    intro x hxH
    rw [Subgroup.mem_centralizer_iff]
    intro j hjJ
    have hj :
        j ∈ peterfalviKSet (M ⊓ rightConjugate M t) t ∧
          j ∈ Subgroup.centralizer (H : Set X) := by
      have hjJ' : j ∈ (h85.J : Set X) := hjJ
      rw [h85.J_eq_centralizer] at hjJ'
      exact hjJ'
    exact ((Subgroup.mem_centralizer_iff.mp hj.2) x hxH).symm
  have hHL : H ≤ L := by
    intro x hxH
    exact ⟨⟨hHV1 hxH, hHCJ hxH⟩, hHF hxH⟩
  have hLcentral : HasNontrivialPeterfalviCentralizer
      (M ⊓ rightConjugate M t) t L := by
    obtain ⟨k, hkI, hkCH, hkne⟩ := hHcentral
    refine ⟨k, hkI, ?_, hkne⟩
    have hkJ : k ∈ h85.J := by
      change k ∈ (h85.J : Set X)
      rw [h85.J_eq_centralizer]
      exact ⟨hkI, hkCH⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hxL
    have hxCJ : x ∈ Subgroup.centralizer (h85.J : Set X) := hxL.1.2
    exact ((Subgroup.mem_centralizer_iff.mp hxCJ) k hkJ).symm
  have hLH : L = H :=
    hHmax L hHL (by simp [L]) hLcentral
  ext x
  constructor
  · intro hxN
    have hxNormH : (x : X) ∈ Subgroup.normalizer (H : Set X) := by
      have hxN' : x ∈
          (Subgroup.normalizer (H : Set X)).subgroupOf F := by
        rw [Subgroup.subgroupOf_normalizer_eq hHF]
        exact hxN
      exact hxN'
    have hxV1 : (x : X) ∈ V1 := by
      exact ⟨hFV x.property, hxNormH⟩
    have hxProd : (x : X) ∈
        ((V1 ⊓ Subgroup.centralizer (h85.J : Set X) : Subgroup X) : Set X) *
          (P : Set X) := by
      rw [← h85.local_normalizer_eq_mul_centralizer]
      exact hxV1
    rcases Set.mem_mul.mp hxProd with ⟨a, ha, p, hp, hap⟩
    have hpF : p ∈ F := hPF hp
    have haF : a ∈ F := by
      have haeq : a = (x : X) * p⁻¹ := by
        rw [← hap]
        simp
      rw [haeq]
      exact F.mul_mem x.property (F.inv_mem hpF)
    have haL : a ∈ L := ⟨ha, haF⟩
    have haH : a ∈ H := by
      rw [← hLH]
      exact haL
    let aF : F := ⟨a, haF⟩
    let pF : F := ⟨p, hpF⟩
    refine Set.mem_mul.mpr ⟨aF, haH, pF, hp, ?_⟩
    apply Subtype.ext
    exact hap
  · intro hxProd
    rcases Set.mem_mul.mp hxProd with ⟨h, hh, p, hp, hhp⟩
    have hhNorm : (h : X) ∈ Subgroup.normalizer (H : Set X) :=
      Subgroup.le_normalizer hh
    have hpCent : (p : X) ∈ Subgroup.centralizer (H : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hyH
      exact (Subgroup.mem_centralizer_iff.mp (hPcentral hp)) y (hHF hyH)
    have hpNorm : (p : X) ∈ Subgroup.normalizer (H : Set X) :=
      centralizer_le_normalizer H hpCent
    have hxNorm : (x : X) ∈ Subgroup.normalizer (H : Set X) := by
      rw [← hhp]
      exact (Subgroup.normalizer (H : Set X)).mul_mem hhNorm hpNorm
    rw [← Subgroup.subgroupOf_normalizer_eq hHF]
    exact hxNorm

/-- Corollary 8.5 supplies the preceding maximal-subgroup factorization from
the existing Peterfalvi fixed-point-free input. -/
public theorem lemma99_normalizer_subgroupOf_eq_mul_of_proposition84
    {X : Type u} [Group X] [Finite X]
    {M F H P : Subgroup X} {t : X}
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t) (htM : t ∉ M)
    (d83 : Lemma83Data M t)
    (h84 : Proposition84Statement M t d83.u)
    (hHF : H ≤ F)
    (hFV : F ≤ peterfalviV (M ⊓ rightConjugate M t) t)
    (hPF : P ≤ F)
    (hPcentral : P ≤ Subgroup.centralizer (F : Set X))
    (hHne : H ≠ ⊥)
    (hHcentral : HasNontrivialPeterfalviCentralizer
      (M ⊓ rightConjugate M t) t H)
    (hHmax : ∀ L : Subgroup X,
      H ≤ L → L ≤ F →
        HasNontrivialPeterfalviCentralizer
          (M ⊓ rightConjugate M t) t L →
        L = H)
    (hPne : P ≠ ⊥)
    (hPtrivial : PeterfalviCentralizersTrivial
      (M ⊓ rightConjugate M t) t P) :
    (Subgroup.normalizer (H.subgroupOf F : Set F) : Set F) =
      (H.subgroupOf F : Set F) * (P.subgroupOf F : Set F) := by
  have hVeq : peterfalviV (M ⊓ rightConjugate M t) t =
      (M ⊓ rightConjugate M t) ⊓
        Subgroup.centralizer ({d83.u} : Set X) := by
    simpa [peterfalviV] using d83.centralizer_eq
  have hFV0 : F ≤
      (M ⊓ rightConjugate M t) ⊓
        Subgroup.centralizer ({d83.u} : Set X) := by
    rw [← hVeq]
    exact hFV
  have hPCH : P ≤ Subgroup.centralizer (H : Set X) := by
    intro p hp
    rw [Subgroup.mem_centralizer_iff]
    intro x hxH
    exact (Subgroup.mem_centralizer_iff.mp (hPcentral hp)) x (hHF hxH)
  have hPV : P ≤ normalizerIn
      ((M ⊓ rightConjugate M t) ⊓
        Subgroup.centralizer ({d83.u} : Set X)) H := by
    intro p hp
    exact ⟨hFV0 (hPF hp), centralizer_le_normalizer H (hPCH hp)⟩
  have hI : HasNontrivialPeterfalviNormalizer
      (M ⊓ rightConjugate M t) t H := by
    obtain ⟨k, hkI, hkCH, hkne⟩ := hHcentral
    exact ⟨k, hkI, centralizer_le_normalizer H hkCH, hkne⟩
  have hfixed : Corollary85FixedPointFree
      (M ⊓ rightConjugate M t) t H P := by
    intro g hgP hgne k hkI _hkN hcomm
    exact hPtrivial g hgP hgne k hkI hcomm
  obtain ⟨h85⟩ :=
    Proposition84Statement.corollary85
      (Y := H) (P := P) d83 h84 hM ht htM
      (hHF.trans hFV0) hHne hI hPV hPne hfixed
  exact lemma99_normalizer_subgroupOf_eq_mul_of_corollary85
    hHF hFV0 hPF hPcentral hHcentral hHmax h85

/-! ## Nilpotent normalizer bridge -/

private theorem lemma99_quotient_pPrimeCore_isPGroup_of_nilpotent
    {F : Type*} [Group F] [Finite F]
    {p : ℕ} [Fact p.Prime]
    (hFnil : Group.IsNilpotent F) :
    IsPGroup p (F ⧸ pPrimeCore p F) := by
  classical
  let O : Subgroup F := pPrimeCore p F
  let q : F →* F ⧸ O := QuotientGroup.mk' O
  have htop : (⊤ : Subgroup F) ≤ pCore p F ⊔ O := by
    simpa [O] using nilpotent_top_le_pCore_sup_pPrimeCore hFnil
  apply (pCore_isPGroup (G := F) (p := p)).of_surjective
    (q.comp (pCore p F).subtype)
  intro z
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective O z
  have hxSup : x ∈ pCore p F ⊔ O := htop (Subgroup.mem_top x)
  rcases Subgroup.mem_sup_of_normal_right.mp hxSup with
    ⟨a, ha, b, hb, hab⟩
  refine ⟨⟨a, ha⟩, ?_⟩
  change q a = q x
  rw [← hab]
  simp [q, hb]

private theorem lemma99_le_pPrimeCore_of_nilpotent_of_coprime_card
    {F : Type*} [Group F] [Finite F]
    {p : ℕ} [Fact p.Prime]
    (hFnil : Group.IsNilpotent F)
    (H : Subgroup F)
    (hHcop : Nat.Coprime p (Nat.card H)) :
    H ≤ pPrimeCore p F := by
  let O : Subgroup F := pPrimeCore p F
  let q : F →* F ⧸ O := QuotientGroup.mk' O
  have hquotP : IsPGroup p (F ⧸ O) := by
    simpa [O] using
      (lemma99_quotient_pPrimeCore_isPGroup_of_nilpotent
        (F := F) (p := p) hFnil)
  intro x hxH
  obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp hquotP) (q x)
  have horderMapDvdH : orderOf (q x) ∣ Nat.card H :=
    (orderOf_map_dvd q x).trans (Subgroup.orderOf_dvd_natCard H hxH)
  have hpowDvdH : p ^ n ∣ Nat.card H := by simpa [hn] using horderMapDvdH
  have hnzero : n = 0 := by
    by_contra hnne
    have hpdvdPow : p ∣ p ^ n := by
      exact dvd_pow_self p hnne
    exact ((Fact.out : Nat.Prime p).coprime_iff_not_dvd.mp hHcop)
      (hpdvdPow.trans hpowDvdH)
  have hqone : q x = 1 := by
    apply orderOf_eq_one_iff.mp
    simpa [hnzero] using hn
  exact (QuotientGroup.eq_one_iff x).mp (by simpa [q, O] using hqone)

private theorem lemma99_unique_order_p_subgroup_of_cyclic_sylows
    {F : Type*} [Group F] [Finite F]
    {p : ℕ} [Fact p.Prime]
    (P Q : Subgroup F)
    (hPcenter : P ≤ Subgroup.center F)
    (hPcard : Nat.card P = p)
    (hQcard : Nat.card Q = p)
    (hcyclic : ∀ S : Sylow p F, IsCyclic (S : Subgroup F)) :
    Q = P := by
  classical
  have hPp : IsPGroup p P := by
    apply IsPGroup.of_card (n := 1)
    simpa using hPcard
  have hQp : IsPGroup p Q := by
    apply IsPGroup.of_card (n := 1)
    simpa using hQcard
  obtain ⟨S, hQS⟩ := hQp.exists_le_sylow
  have hP_le_normS : P ≤ Subgroup.normalizer ((S : Subgroup F) : Set F) := by
    intro x hxP
    apply centralizer_le_normalizer (S : Subgroup F)
    rw [Subgroup.mem_centralizer_iff]
    intro y _hyS
    exact (Subgroup.mem_center_iff.mp (hPcenter hxP)) y
  have hSfixed :
      S ∈ MulAction.fixedPoints P (Sylow p F) :=
    (Subgroup.sylow_mem_fixedPoints_iff P).2 hP_le_normS
  have hPS : P ≤ (S : Subgroup F) :=
    (IsPGroup.sylow_mem_fixedPoints_iff hPp).1 hSfixed
  let PS : Subgroup S := P.subgroupOf (S : Subgroup F)
  let QS : Subgroup S := Q.subgroupOf (S : Subgroup F)
  haveI : IsCyclic S := hcyclic S
  have hPS_card : Nat.card PS = p := by
    simpa [PS] using
      (natCard_subgroupOf_eq P (S : Subgroup F) hPS).trans hPcard
  have hQS_card : Nat.card QS = p := by
    simpa [QS] using
      (natCard_subgroupOf_eq Q (S : Subgroup F) hQS).trans hQcard
  have hsubEq : PS = QS :=
    unique_subgroup_of_prime_order_in_cyclic_pre PS QS hPS_card hQS_card
  have hmapEq := congrArg (Subgroup.map (S : Subgroup F).subtype) hsubEq
  simpa [PS, QS, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr hPS, inf_eq_left.mpr hQS] using hmapEq.symm

private theorem lemma99_coprime_card_of_not_le_central_prime_subgroup
    {F : Type*} [Group F] [Finite F]
    {p : ℕ} [Fact p.Prime]
    (P H : Subgroup F)
    (hPcenter : P ≤ Subgroup.center F)
    (hPcard : Nat.card P = p)
    (hcyclic : ∀ S : Sylow p F, IsCyclic (S : Subgroup F))
    (hPnotH : ¬ P ≤ H) :
    Nat.Coprime p (Nat.card H) := by
  apply (Fact.out : Nat.Prime p).coprime_iff_not_dvd.mpr
  intro hpdvd
  letI : Fintype H := Fintype.ofFinite H
  obtain ⟨x, hxorder⟩ := exists_prime_orderOf_dvd_card p (by
    simpa [Nat.card_eq_fintype_card] using hpdvd)
  let Q : Subgroup F := Subgroup.zpowers (x : F)
  have hQcard : Nat.card Q = p := by
    change Nat.card (Subgroup.zpowers (x : F)) = p
    rw [Nat.card_zpowers, Subgroup.orderOf_coe]
    exact hxorder
  have hQP : Q = P :=
    lemma99_unique_order_p_subgroup_of_cyclic_sylows
      P Q hPcenter hPcard hQcard hcyclic
  apply hPnotH
  rw [← hQP]
  exact Subgroup.zpowers_le.mpr x.property

/-- Exact source inference used near the end of Lemma 9.9. -/
public theorem lemma99_nilpotent_normalizer_eq_pPrimeCore
    {F : Type*} [Group F] [Finite F]
    {p : ℕ} [Fact p.Prime]
    (hFnil : Group.IsNilpotent F)
    (P H : Subgroup F)
    (hPcenter : P ≤ Subgroup.center F)
    (hPcard : Nat.card P = p)
    (hcyclic : ∀ S : Sylow p F, IsCyclic (S : Subgroup F))
    (hPnotH : ¬ P ≤ H)
    (hNormalizer :
      (Subgroup.normalizer (H : Set F) : Set F) =
        (H : Set F) * (P : Set F)) :
    H = pPrimeCore p F := by
  classical
  let O : Subgroup F := pPrimeCore p F
  have hHcop : Nat.Coprime p (Nat.card H) :=
    lemma99_coprime_card_of_not_le_central_prime_subgroup
      P H hPcenter hPcard hcyclic hPnotH
  have hHO : H ≤ O := by
    simpa [O] using
      (lemma99_le_pPrimeCore_of_nilpotent_of_coprime_card
        (F := F) (p := p) hFnil H hHcop)
  apply le_antisymm hHO
  by_contra hOnotH
  have hHsub_ne_top : H.subgroupOf O ≠ ⊤ := by
    intro htop
    apply hOnotH
    intro x hxO
    let xO : O := ⟨x, hxO⟩
    have hxTop : xO ∈ (⊤ : Subgroup O) := Subgroup.mem_top xO
    rw [← htop] at hxTop
    exact hxTop
  have hOnil : Group.IsNilpotent O := by
    letI : Group.IsNilpotent F := hFnil
    infer_instance
  letI : Group.IsNilpotent O := hOnil
  have hHsub_lt_top : H.subgroupOf O < ⊤ :=
    lt_top_iff_ne_top.mpr hHsub_ne_top
  have hnormalizerGrow :
      H.subgroupOf O < Subgroup.normalizer (H.subgroupOf O : Set O) :=
    Group.normalizerCondition_of_isNilpotent (H.subgroupOf O) hHsub_lt_top
  obtain ⟨x, hxNorm, hxNotH⟩ := SetLike.exists_of_lt hnormalizerGrow
  have hxNormF :
      (x : F) ∈ Subgroup.normalizer (H : Set F) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hyH
      let yO : O := ⟨y, hHO hyH⟩
      have hyHsub : yO ∈ H.subgroupOf O := hyH
      have hconj :=
        (Subgroup.mem_normalizer_iff.mp hxNorm yO).1 hyHsub
      exact hconj
    · intro hconjH
      let zO : O := ⟨(x : F) * y * (x : F)⁻¹, hHO hconjH⟩
      have hzHsub : zO ∈ H.subgroupOf O := hconjH
      have hxInvNorm :
          x⁻¹ ∈ Subgroup.normalizer (H.subgroupOf O : Set O) :=
        (Subgroup.normalizer (H.subgroupOf O : Set O)).inv_mem hxNorm
      have hback :=
        (Subgroup.mem_normalizer_iff.mp hxInvNorm zO).1 hzHsub
      change
        (x : F)⁻¹ * ((x : F) * y * (x : F)⁻¹) * ((x : F)⁻¹)⁻¹ ∈ H
        at hback
      simpa [mul_assoc] using hback
  have hxMul : (x : F) ∈ (H : Set F) * (P : Set F) := by
    rw [← hNormalizer]
    exact hxNormF
  rcases Set.mem_mul.mp hxMul with ⟨h, hhH, y, hyP, hhy⟩
  have hyO : y ∈ O := by
    have hhO : h ∈ O := hHO hhH
    have hyEq : y = h⁻¹ * (x : F) := by
      rw [← hhy]
      simp
    rw [hyEq]
    exact O.mul_mem (O.inv_mem hhO) x.property
  have hPOcop : Nat.Coprime (Nat.card P) (Nat.card O) := by
    rw [hPcard]
    simpa [O] using (pPrimeCore_coprime_card (G := F) (p := p))
  have hPOinf : P ⊓ O = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard hPOcop).eq_bot
  have hyOne : y = 1 := by
    have hyInf : y ∈ P ⊓ O := ⟨hyP, hyO⟩
    rw [hPOinf] at hyInf
    simpa using hyInf
  apply hxNotH
  change (x : F) ∈ H
  have hhx : h = (x : F) := by simpa [hyOne] using hhy
  simpa [← hhx] using hhH

/-- The first assertion of source `(9F)`: the Fitting subgroup of
`E ∩ V` acts fixed-point-freely on the Peterfalvi complement `K`. -/
public theorem lemma99_first_nineF
    {X : Type u} [Group X] [Finite X]
    {M E : Subgroup X} {t : X}
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t) (htM : t ∉ M)
    (d83 : Lemma83Data M t)
    (h84 : Proposition84Statement M t d83.u)
    (hED : E ≤ M ⊓ rightConjugate M t)
    (hEN : (E.subgroupOf (M ⊓ rightConjugate M t)).Normal)
    (hEne : E ≠ ⊥)
    (h43c : II1Lemma43cConclusion
      (M ⊓ rightConjugate M t) t)
    (h97 : Lemma97Conclusion M t)
    (h95 : ∀ p : ℕ, Nat.Prime p →
      p ∣ Nat.card (E ⧸ derivedSubgroup E) →
      Lemma94AlternativeB (M ⊓ rightConjugate M t) E t p)
    (hNoNormal : ∀ Y : Subgroup X,
      Y ≤ peterfalviV (M ⊓ rightConjugate M t) t →
        Y ≠ ⊥ →
        (Y.subgroupOf
          (peterfalviV (M ⊓ rightConjugate M t) t)).Normal →
        ¬ HasNontrivialPeterfalviCentralizer
          (M ⊓ rightConjugate M t) t Y) :
    let K : Subgroup X := Subgroup.closure
      (peterfalviKSet (M ⊓ rightConjugate M t) t)
    let R : Subgroup X := E ⊓ peterfalviV (M ⊓ rightConjugate M t) t
    let F : Subgroup X := (fittingSubgroup R).map R.subtype
    ∀ x : X, x ∈ F → x ≠ 1 →
      ∀ k : X, k ∈ K → k * x = x * k → k = 1 := by
  classical
  let D : Subgroup X := M ⊓ rightConjugate M t
  let V : Subgroup X := peterfalviV D t
  let K : Subgroup X := Subgroup.closure (peterfalviKSet D t)
  let R : Subgroup X := E ⊓ V
  let F : Subgroup X := (fittingSubgroup R).map R.subtype
  have hED' : E ≤ D := by simpa [D] using hED
  have hEN' : (E.subgroupOf D).Normal := by simpa [D] using hEN
  have hRleE : R ≤ E := inf_le_left
  have hRleV : R ≤ V := inf_le_right
  have hFleR : F ≤ R := by
    simpa [F] using Subgroup.map_subtype_le (fittingSubgroup R)
  have hFleV : F ≤ V := hFleR.trans hRleV
  have hKset : (K : Set X) = peterfalviKSet D t := by
    simpa [K, D] using h43c.closure_eq_set
  have hDodd : Odd (Nat.card D) := by
    simpa [D] using hM.inf_rightConjugate_card_odd htM
  have hEodd : Odd (Nat.card E) :=
    hDodd.of_dvd_nat (Subgroup.card_dvd_of_le hED')
  obtain ⟨p, hp, _hpAb, S, P, hScyclic, _hSV, _hPleS,
      hPcard, hPR, hPtrivial⟩ :=
    lemma99_exists_prime_sylow_order_p_subgroup
      (D := D) (E := E) (t := t) hEodd hEne (by
        intro q hq hqAb
        simpa [D] using h95 q hq hqAb)
  letI : Fact p.Prime := ⟨hp⟩
  have hPne : P ≠ ⊥ := by
    intro hPbot
    have hpOne : p = 1 := by
      simpa [hPbot] using hPcard.symm
    exact hp.ne_one hpOne
  obtain ⟨hPcentralF, hPF, hPcenter⟩ := by
    simpa [R, F] using
      (lemma99_first_nineF_fitting_center
        (D := D) (E := E) (P := P) (t := t) (p := p)
        S hp hED' hEN' hDodd h43c
        (by simpa [D] using h97.peterfalvi_centralizer_eq_bot)
        hScyclic hPcard hPR hPtrivial
        (by simpa [D, V] using hNoNormal))
  change ∀ x : X, x ∈ F → x ≠ 1 →
    ∀ k : X, k ∈ K → k * x = x * k → k = 1
  intro x hxF hxne k hkK hcomm
  by_contra hkone
  obtain ⟨H, hHF, hHne, hHcentral, hHmax⟩ :=
    lemma99_exists_maximal_nontrivial_centralizer
      hxF hxne hkK hkone hKset hcomm
  have hPnotH : ¬ P ≤ H := by
    intro hPH
    obtain ⟨g, hgP, hgnot⟩ :=
      SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hPne)
    have hgne : g ≠ 1 := by simpa using hgnot
    obtain ⟨q, hqI, hqCH, hqne⟩ := hHcentral
    have hqcomm : q * g = g * q :=
      ((Subgroup.mem_centralizer_iff.mp hqCH) g (hPH hgP)).symm
    exact hqne (hPtrivial g hgP hgne q hqI hqcomm)
  have hNormalizer :
      (Subgroup.normalizer (H.subgroupOf F : Set F) : Set F) =
        (H.subgroupOf F : Set F) * (P.subgroupOf F : Set F) := by
    apply lemma99_normalizer_subgroupOf_eq_mul_of_proposition84
      hM ht htM d83 h84 hHF
      (by simpa [D, V] using hFleV) hPF hPcentralF hHne
      (by simpa [D] using hHcentral)
      (by
        intro L hHL hLF hLcentral
        apply hHmax L hHL hLF
        simpa [D] using hLcentral)
      hPne (by simpa [D] using hPtrivial)
  have hFnil : Group.IsNilpotent F := by
    change Group.IsNilpotent (fittingSubgroupOf (G := X) R)
    exact fittingSubgroupOf_isNilpotent (G := X) R
  have hFleE : F ≤ E := hFleR.trans hRleE
  have hcyclicF : ∀ Q : Sylow p F, IsCyclic (Q : Subgroup F) :=
    lemma99_all_sylow_cyclic_of_ambient_sylow
      E F hFleE S hScyclic
  have hPcardF : Nat.card (P.subgroupOf F) = p := by
    simpa using (natCard_subgroupOf_eq P F hPF).trans hPcard
  have hPnotHsub : ¬ P.subgroupOf F ≤ H.subgroupOf F := by
    intro hsub
    apply hPnotH
    intro y hyP
    let yF : F := ⟨y, hPF hyP⟩
    exact hsub (show yF ∈ P.subgroupOf F from hyP)
  have hHcoreSub : H.subgroupOf F = pPrimeCore p F :=
    lemma99_nilpotent_normalizer_eq_pPrimeCore
      hFnil (P.subgroupOf F) (H.subgroupOf F) hPcenter
      hPcardF hcyclicF hPnotHsub hNormalizer
  have hHcore : H = (pPrimeCore p F).map F.subtype := by
    calc
      H = (H.subgroupOf F).map F.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hHF).symm
      _ = (pPrimeCore p F).map F.subtype := by rw [hHcoreSub]
  have hVleD : V ≤ D := by
    simp [V, peterfalviV]
  have hRnormalV : (R.subgroupOf V).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hRleV]
    intro r v hr hv
    refine ⟨?_, ?_⟩
    · exact ((Subgroup.normal_subgroupOf_iff hED').mp hEN')
        r v hr.1 (hVleD hv)
    · exact V.mul_mem (V.mul_mem hv hr.2) (V.inv_mem hv)
  have hFnormalV : (F.subgroupOf V).Normal := by
    exact normal_subgroupOf_map_of_characteristic_of_normal
      R F V hRleV hRnormalV (fittingSubgroup R)
      (by infer_instance) rfl hFleV
  have hHnormalV : (H.subgroupOf V).Normal := by
    exact normal_subgroupOf_map_of_characteristic_of_normal
      F H V hFleV hFnormalV (pPrimeCore p F)
      (by infer_instance) hHcore (hHF.trans hFleV)
  have hcontra : False :=
    (hNoNormal H (by simpa [D, V] using hHF.trans hFleV) hHne
      (by simpa [D, V] using hHnormalV))
      (by simpa [D] using hHcentral)
  exact hcontra

/-- Once the first assertion of `(9F)` is known, the Fitting complement is
cyclic by the nilpotent Frobenius-complement input.  Nontriviality of the
Fitting subgroup follows from the nontrivial fixed part supplied by
Corollary 9.6. -/
public theorem lemma99_fitting_cyclic_of_first_nineF
    {X : Type u} [Group X] [Finite X]
    {D E : Subgroup X} {t : X}
    (hED : E ≤ D)
    (hDodd : Odd (Nat.card D))
    (hIne : ∃ k : X, k ∈ peterfalviKSet D t ∧ k ≠ 1)
    (h43c : II1Lemma43cConclusion D t)
    (h96 : Corollary96Conclusion D E t)
    (hfirst :
      let K : Subgroup X := Subgroup.closure (peterfalviKSet D t)
      let R : Subgroup X := E ⊓ peterfalviV D t
      let F : Subgroup X := (fittingSubgroup R).map R.subtype
      ∀ x : X, x ∈ F → x ≠ 1 →
        ∀ k : X, k ∈ K → k * x = x * k → k = 1)
    (h911 : IG911iiNilpotentFrobeniusComplementCyclic (X := X)) :
    let R : Subgroup X := E ⊓ peterfalviV D t
    let F : Subgroup X := (fittingSubgroup R).map R.subtype
    IsCyclic F := by
  classical
  let K : Subgroup X := Subgroup.closure (peterfalviKSet D t)
  let V : Subgroup X := peterfalviV D t
  let R : Subgroup X := E ⊓ V
  let F : Subgroup X := (fittingSubgroup R).map R.subtype
  have hKset : (K : Set X) = peterfalviKSet D t := by
    simpa [K] using h43c.closure_eq_set
  have hKcomm : IsMulCommutative K :=
    lemma99_isMulCommutative_of_closure_eq_set hKset
  letI : IsMulCommutative K := hKcomm
  have hRleE : R ≤ E := inf_le_left
  have hFleR : F ≤ R := by
    simpa [F] using Subgroup.map_subtype_le (fittingSubgroup R)
  have hFleE : F ≤ E := hFleR.trans hRleE
  have hKleD : K ≤ D := by
    simpa [K] using h43c.closure_le
  have hKE : K ≤ E := by
    simpa [K] using h96.closure_le_derived.trans
      (Subgroup.map_subtype_le (derivedSubgroup E))
  have hKnormalD : (K.subgroupOf D).Normal := by
    simpa [K] using h43c.normal
  have hDnormK : D ≤ Subgroup.normalizer (K : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKleD).mp hKnormalD
  have hKnormalE : (K.subgroupOf E).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKE).mpr
      (hED.trans hDnormK)
  have hKdisjV : Disjoint K V := by
    rw [Subgroup.disjoint_def]
    intro x hxK hxV
    have hxD : x ∈ D := hKleD hxK
    let xD : D := ⟨x, hxD⟩
    have hxKV : xD ∈
        (K.subgroupOf D) ⊓ (V.subgroupOf D) := ⟨hxK, hxV⟩
    have hxbot : xD ∈ (⊥ : Subgroup D) := by
      rw [← h43c.isComplement'.disjoint.eq_bot]
      exact hxKV
    exact congrArg Subtype.val (by simpa using hxbot)
  have hKne : K ≠ ⊥ := by
    obtain ⟨k, hkI, hkne⟩ := hIne
    intro hbot
    have hkbot : k ∈ (⊥ : Subgroup X) := by
      rw [← hbot]
      exact Subgroup.subset_closure hkI
    exact hkne (by simpa using hkbot)
  have hRne : R ≠ ⊥ := by
    simpa [R, V] using h96.inf_fixed_ne_bot
  have hRodd : Odd (Nat.card R) :=
    hDodd.of_dvd_nat (Subgroup.card_dvd_of_le
      (hRleE.trans hED))
  have hRsolv : Group.IsSolvable R := odd_order_theorem R hRodd
  letI : Group.IsSolvable R := hRsolv
  have hFne : F ≠ ⊥ := by
    intro hFbot
    have hfitbot : fittingSubgroup R = ⊥ := by
      apply Subgroup.map_injective R.subtype_injective
      simpa [F] using hFbot
    have hRcard : Nat.card R = 1 :=
      (fitting_eq_bot_iff_card_eq_one_of_solvable R).mp hfitbot
    exact hRne ((Subgroup.card_eq_one (H := R)).mp hRcard)
  have hKsubNe : K.subgroupOf (K ⊔ F) ≠ ⊥ := by
    intro hbot
    exact hKne ((Subgroup.subgroupOf_eq_bot.mp hbot).eq_bot_of_le le_sup_left)
  have hFsubNe : F.subgroupOf (K ⊔ F) ≠ ⊥ := by
    intro hbot
    exact hFne ((Subgroup.subgroupOf_eq_bot.mp hbot).eq_bot_of_le le_sup_right)
  have hKnormalKF : (K.subgroupOf (K ⊔ F)).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
    exact (sup_le hKE hFleE).trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hKE).mp hKnormalE)
  have hKFcomp :
      (K.subgroupOf (K ⊔ F)).IsComplement' (F.subgroupOf (K ⊔ F)) := by
    letI : (K.subgroupOf (K ⊔ F)).Normal := hKnormalKF
    exact isComplement'_of_disjoint_sup_eq_top_of_normal
      (K.subgroupOf (K ⊔ F)) (F.subgroupOf (K ⊔ F))
      (by
        rw [Subgroup.disjoint_def]
        intro x hxK hxF
        apply Subtype.ext
        have hxbot : (x : X) ∈ (⊥ : Subgroup X) := by
          rw [← hKdisjV.eq_bot]
          exact ⟨hxK, hFleR hxF |>.2⟩
        simpa using hxbot)
      (by
        rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right]
        simp)
  have hKFrob : IsFrobeniusGroupWithKernelComplement
      (K.subgroupOf (K ⊔ F)) (F.subgroupOf (K ⊔ F)) := by
    apply (lemma_3_1 _ _ hKsubNe hFsubNe hKnormalKF hKFcomp).mpr
    intro z hzne
    rw [Subgroup.eq_bot_iff_forall]
    intro k hk
    apply Subtype.ext
    have hzF : (z : X) ∈ F := z.property
    have hzneX : (z : X) ≠ 1 := by
      intro hz
      exact hzne (Subtype.ext (Subtype.ext hz))
    have hkK : (k : X) ∈ K := hk.1
    have hcomm : (k : X) * (z : X) = (z : X) * (k : X) :=
      congrArg Subtype.val
        (Subgroup.mem_centralizer_singleton_iff.mp hk.2)
    have hfix := hfirst
    change ∀ y : X, y ∈ F → y ≠ 1 →
      ∀ q : X, q ∈ K → q * y = y * q → q = 1 at hfix
    exact hfix (z : X) hzF hzneX (k : X) hkK hcomm
  have hFodd : Odd (Nat.card F) :=
    hRodd.of_dvd_nat (Subgroup.card_dvd_of_le hFleR)
  have hFnil : Group.IsNilpotent F := by
    change Group.IsNilpotent (fittingSubgroupOf (G := X) R)
    exact fittingSubgroupOf_isNilpotent (G := X) R
  have hFcyclic : IsCyclic F :=
    h911 (K ⊔ F) K F le_sup_left le_sup_right hKFrob hFnil hFodd
  simpa [R, F] using hFcyclic

/-- Assemble both assertions of `(9F)` from the first fixed-point-free field.
The first field makes the Fitting subgroup cyclic through the Frobenius
argument, after which `lemma99_second_nineF` supplies the derived-subgroup
containment. -/
public theorem lemma99_nineF_of_first
    {X : Type u} [Group X] [Finite X]
    {D E : Subgroup X} {t : X}
    (hED : E ≤ D)
    (hDodd : Odd (Nat.card D))
    (hIne : ∃ k : X, k ∈ peterfalviKSet D t ∧ k ≠ 1)
    (h43c : II1Lemma43cConclusion D t)
    (h96 : Corollary96Conclusion D E t)
    (hfirst :
      let K : Subgroup X := Subgroup.closure (peterfalviKSet D t)
      let R : Subgroup X := E ⊓ peterfalviV D t
      let F : Subgroup X := (fittingSubgroup R).map R.subtype
      ∀ x : X, x ∈ F → x ≠ 1 →
        ∀ k : X, k ∈ K → k * x = x * k → k = 1)
    (h911 : IG911iiNilpotentFrobeniusComplementCyclic (X := X)) :
    Lemma99NineF D E t := by
  let R : Subgroup X := E ⊓ peterfalviV D t
  let F : Subgroup X := (fittingSubgroup R).map R.subtype
  have hFcyclic : IsCyclic F := by
    simpa [R, F] using
      (lemma99_fitting_cyclic_of_first_nineF
        (D := D) (E := E) (t := t)
        hED hDodd hIne h43c h96 hfirst h911)
  refine ⟨?_, ?_⟩
  · simpa [R, F] using hfirst
  · simpa [R, F] using
      (lemma99_second_nineF
        (D := D) (E := E) (t := t)
        hED hDodd h43c h96 (by simpa [R, F] using hFcyclic))

/-- Source Lemma 9.9.  Some nontrivial subgroup of `V`, normal in `V`, has
a nontrivial Peterfalvi centralizer. -/
public theorem lemma_9_9_of_corollary95
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
    (h95 : ∀ p : ℕ, Nat.Prime p →
      p ∣ Nat.card
        (((W ⊓ (M ⊓ rightConjugate M t) : Subgroup X) : Type u) ⧸
          derivedSubgroup
            ((W ⊓ (M ⊓ rightConjugate M t) : Subgroup X) : Type u)) →
      Lemma94AlternativeB (M ⊓ rightConjugate M t)
        (W ⊓ (M ⊓ rightConjugate M t)) t p)
    (h911 : IG911iiNilpotentFrobeniusComplementCyclic (X := X)) :
    let D : Subgroup X := M ⊓ rightConjugate M t
    let V : Subgroup X := peterfalviV D t
    ∃ Y : Subgroup X,
      Y ≤ V ∧ Y ≠ ⊥ ∧
        (Y.subgroupOf V).Normal ∧
        HasNontrivialPeterfalviCentralizer D t Y := by
  classical
  let D : Subgroup X := M ⊓ rightConjugate M t
  let E : Subgroup X := W ⊓ D
  let V : Subgroup X := peterfalviV D t
  change ∃ Y : Subgroup X,
    Y ≤ V ∧ Y ≠ ⊥ ∧
      (Y.subgroupOf V).Normal ∧
      HasNontrivialPeterfalviCentralizer D t Y
  by_contra hNoWitness
  have hNoNormal : ∀ Y : Subgroup X,
      Y ≤ V → Y ≠ ⊥ → (Y.subgroupOf V).Normal →
        ¬ HasNontrivialPeterfalviCentralizer D t Y := by
    intro Y hYV hYne hYnormal hYcentral
    apply hNoWitness
    exact ⟨Y, hYV, hYne, hYnormal, hYcentral⟩
  have hDodd : Odd (Nat.card D) := by
    simpa [D] using hM.inf_rightConjugate_card_odd htM
  have hDinv : rightConjugate D t = D := by
    simpa [D] using inf_rightConjugate_invariant_of_isInvolution M ht
  have hIne' : ∃ x : X, x ∈ peterfalviKSet D t ∧ x ≠ 1 := by
    simpa [D] using hIne
  have h43c : II1Lemma43cConclusion D t :=
    ii1Lemma43cNormalComplement D t hDodd ht hDinv hIne' hNoNormal
  have hED : E ≤ D := inf_le_right
  have hEN : (E.subgroupOf D).Normal := by
    simpa [D, E] using hW.inf_normal_in_right inf_le_left
  have h96' : Corollary96Conclusion D E t := by
    simpa [D, E] using h96
  have h98' : Lemma98Conclusion D E t := by
    simpa [D, E] using h98
  have hEne : E ≠ ⊥ := by
    intro hEbot
    apply h96'.inf_fixed_ne_bot
    simp [hEbot]
  have h95' : ∀ p : ℕ, Nat.Prime p →
      p ∣ Nat.card (E ⧸ derivedSubgroup E) →
      Lemma94AlternativeB D E t p := by
    intro p hp hpAb
    simpa [D, E] using h95 p hp (by simpa [D, E] using hpAb)
  have hfirst :
      let K : Subgroup X := Subgroup.closure (peterfalviKSet D t)
      let R : Subgroup X := E ⊓ peterfalviV D t
      let F : Subgroup X := (fittingSubgroup R).map R.subtype
      ∀ x : X, x ∈ F → x ≠ 1 →
        ∀ k : X, k ∈ K → k * x = x * k → k = 1 := by
    simpa [D, E, V] using
      (lemma99_first_nineF
        (M := M) (E := E) (t := t)
        hM ht htM d83 h84 (by simpa [D] using hED)
        (by simpa [D] using hEN) hEne
        (by simpa [D] using h43c) h97 h95'
        (by simpa [D, V] using hNoNormal))
  have h9F : Lemma99NineF D E t :=
    lemma99_nineF_of_first hED hDodd hIne' h43c h96' hfirst h911
  exact lemma99_false_of_nineF
    hED hDodd hIne' h43c h96' h98' h9F h911

/-- Source Lemma 9.9, with Corollary 9.5 obtained from its genuine
`[II1; 4.4]` and `[II1; 4.3(b)]` inputs. -/
public theorem lemma_9_9
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
    let D : Subgroup X := M ⊓ rightConjugate M t
    let V : Subgroup X := peterfalviV D t
    ∃ Y : Subgroup X,
      Y ≤ V ∧ Y ≠ ⊥ ∧
        (Y.subgroupOf V).Normal ∧
        HasNontrivialPeterfalviCentralizer D t Y := by
  apply lemma_9_9_of_corollary95
    hM ht htM d83 h84 hW hIne h96 h97 h98 ?_
      h911
  intro p hp hpAb
  letI : Fact p.Prime := ⟨hp⟩
  exact corollary_9_5_ambient_abelianization
    hM ht htM d83 h84 hW hpAb hIne h43b

end CFSG.BenderSuzuki
