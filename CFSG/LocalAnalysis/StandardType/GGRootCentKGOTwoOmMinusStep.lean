module

public import CFSG.LocalAnalysis.StandardType.GGRootCentKGOTwoOmMinusSemi
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsOmRestr
import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsOmMinus
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerOmegaFrame
import CFSG.LieType.Universal.SpinOmega.Range
import CFSG.LocalAnalysis.StandardType.GGRootCentralizerOmegaSpin
public import CFSG.RankThree.PartOne.KC.OrthogonalRegularCoverage
import CFSG.RankThree.OrthogonalInvolutions.Dickson
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightOrthPlusLevi
public import CFSG.LieType.Universal.Spin.Twisted.Frame
import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsOmegaRegular
import CFSG.ClassicalGroups.Orthogonal.Simple
import CFSG.ClassicalGroups.Orthogonal.CharTwo
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusExtraction

public section

namespace CFSG.StandardType.KGOm

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartTwo.Sec21
open Subgroup QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.SeitzReduction.OmegaPilot
  RootCentOmega
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.RankThree.OrthogonalInvolutions (omegaGroup commSpace mem_omegaGroup
  finrank_commSpace_reflection)
open CFSG.RankThree.PartOne.KCOrthogonal (SmallFixedException)
open CFSG.StandardType.RCSTOm
open CFSG.RankThree.PartOne.AUTSL CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open scoped MatrixGroups commutatorElement Pointwise

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} {b c : K}

theorem minusSemi_apply (hn : 1 ≤ n) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : ℕ)
    (y : Vm n K) (i : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) :
    minusSemi hn hirr k y i =
      if i = Sum.inr (Sum.inr 0) then
        y i ^ 2 ^ k + (tailSeq b c k).1 * y (Sum.inr (Sum.inr 1)) ^ 2 ^ k
      else if i = Sum.inr (Sum.inr 1) then (tailSeq b c k).2 * y i ^ 2 ^ k else y i ^ 2 ^ k := by
  rw [minusSemi, reindexVectorEquiv_symm_apply]
  have hb : b ≠ 0 := ne_zero_of_irreducible_tail b c hirr
  rw [frobPair_pow_apply (j := k)]
  have h0 : ((minusIndexEquiv n hn) i = tailZero n hn) ↔ i = Sum.inr (Sum.inr 0) := by
    rw [show tailZero n hn = minusIndexEquiv n hn (Sum.inr (Sum.inr 0)) from rfl]
    exact (minusIndexEquiv n hn).injective.eq_iff
  have h1 : ((minusIndexEquiv n hn) i = tailOne n hn) ↔ i = Sum.inr (Sum.inr 1) := by
    rw [show tailOne n hn = minusIndexEquiv n hn (Sum.inr (Sum.inr 1)) from rfl]
    exact (minusIndexEquiv n hn).injective.eq_iff
  have hv : ∀ j, (reindexVectorEquiv (minusIndexEquiv n hn)) y ((minusIndexEquiv n hn) j) = y j :=
    fun j => by rw [reindexVectorEquiv_apply, Equiv.symm_apply_apply]
  have hvt : (reindexVectorEquiv (minusIndexEquiv n hn)) y (tailOne n hn) =
      y (Sum.inr (Sum.inr 1)) := hv _
  simp only [h0, h1, hv, hvt]

theorem minusSemi_apply_tailZero (hn : 1 ≤ n) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : ℕ)
    (y : Vm n K) :
    minusSemi hn hirr k y (Sum.inr (Sum.inr 0)) =
      y (Sum.inr (Sum.inr 0)) ^ 2 ^ k +
        (tailSeq b c k).1 * y (Sum.inr (Sum.inr 1)) ^ 2 ^ k := by
  rw [minusSemi_apply]
  simp

theorem minusSemi_apply_tailOne (hn : 1 ≤ n) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : ℕ)
    (y : Vm n K) :
    minusSemi hn hirr k y (Sum.inr (Sum.inr 1)) =
      (tailSeq b c k).2 * y (Sum.inr (Sum.inr 1)) ^ 2 ^ k := by
  rw [minusSemi_apply]
  simp

theorem minusSemi_apply_other (hn : 1 ≤ n) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : ℕ)
    (y : Vm n K) {i : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2} (h0 : i ≠ Sum.inr (Sum.inr 0))
    (h1 : i ≠ Sum.inr (Sum.inr 1)) :
    minusSemi hn hirr k y i = y i ^ 2 ^ k := by
  rw [minusSemi_apply]
  simp [h0, h1]

theorem minusSemi_apply_inl (hn : 1 ≤ n) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : ℕ)
    (y : Vm n K) (m : Fin (n - 1)) :
    minusSemi hn hirr k y (Sum.inl m) = y (Sum.inl m) ^ 2 ^ k :=
  minusSemi_apply_other hn hirr k y (by simp) (by simp)

theorem minusSemi_apply_inr_inl (hn : 1 ≤ n) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : ℕ)
    (y : Vm n K) (m : Fin (n - 1)) :
    minusSemi hn hirr k y (Sum.inr (Sum.inl m)) = y (Sum.inr (Sum.inl m)) ^ 2 ^ k :=
  minusSemi_apply_other hn hirr k y (by simp) (by simp)

theorem minusSemi_add (hn : 1 ≤ n) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : ℕ)
    (y z : Vm n K) :
    minusSemi hn hirr k (y + z) = minusSemi hn hirr k y + minusSemi hn hirr k z := by
  funext i
  simp only [Pi.add_apply]
  rw [minusSemi_apply, minusSemi_apply, minusSemi_apply]
  simp only [Pi.add_apply]
  have hadd : ∀ a d : K, (a + d) ^ 2 ^ k = a ^ 2 ^ k + d ^ 2 ^ k :=
    fun a d => add_pow_char_pow a d 2 k
  by_cases h0 : i = Sum.inr (Sum.inr 0)
  · subst h0
    simp only [if_true]
    rw [hadd, hadd]
    ring
  · by_cases h1 : i = Sum.inr (Sum.inr 1)
    · subst h1
      simp only [h0, if_false, if_true]
      rw [hadd]
      ring
    · simp only [h0, h1, if_false]
      rw [hadd]

theorem minusSemi_smul (hn : 1 ≤ n) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : ℕ) (β : K)
    (y : Vm n K) : minusSemi hn hirr k (β • y) = β ^ 2 ^ k • minusSemi hn hirr k y := by
  funext i
  rw [show (β ^ 2 ^ k • minusSemi hn hirr k y) i = β ^ 2 ^ k * minusSemi hn hirr k y i
    from rfl]
  rw [minusSemi_apply, minusSemi_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases h0 : i = Sum.inr (Sum.inr 0)
  · subst h0
    simp only [if_true]
    rw [mul_pow, mul_pow]
    ring
  · by_cases h1 : i = Sum.inr (Sum.inr 1)
    · subst h1
      simp only [h0, if_false, if_true]
      rw [mul_pow]
      ring
    · simp only [h0, h1, if_false]
      rw [mul_pow]

theorem minusSemi_minusVec (hn : 1 ≤ n) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : ℕ)
    (m : Fin (n - 1)) (r : Bool) : minusSemi hn hirr k (minusVec n m r) = minusVec n m r := by
  have h2k : (2 : ℕ) ^ k ≠ 0 := by positivity
  funext i
  rw [minusSemi_apply]
  by_cases h0 : i = Sum.inr (Sum.inr 0)
  · subst h0
    simp only [if_true]
    cases r <;> simp [minusVec, eVec, fVec, Pi.single_apply, h2k]
  · by_cases h1 : i = Sum.inr (Sum.inr 1)
    · subst h1
      simp only [h0, if_false, if_true]
      cases r <;> simp [minusVec, eVec, fVec, Pi.single_apply, h2k]
    · simp only [h0, h1, if_false]
      cases r
      · rw [minusVec_false, fVec]
        by_cases h : i = Sum.inr (Sum.inl m)
        · subst h; simp
        · simp [h, h2k]
      · rw [minusVec_true, eVec]
        by_cases h : i = Sum.inl m
        · subst h; simp
        · simp [h, h2k]

private theorem frobPair_pow_quadMinus (hn : 1 ≤ n) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (k : ℕ) (v : Fin (2 * n) → K) :
    coordinateQuadMinus n K hn b c
        (coordinateSemilinearMap ((frobPair n hn b c
          (ne_zero_of_irreducible_tail b c hirr)) ^ k).val v) =
      ((frobeniusEquiv K 2) ^ k) (coordinateQuadMinus n K hn b c v) := by
  induction k with
  | zero =>
    rw [pow_zero]
    simp [coordinateSemilinearMap_one]
  | succ k ih =>
    have e1 : ((frobPair n hn b c (ne_zero_of_irreducible_tail b c hirr) ^ (k + 1) :
        similarityPairs (coordinateQuadMinus n K hn b c)).val) =
        (frobElt n hn b c (ne_zero_of_irreducible_tail b c hirr)) *
          (frobPair n hn b c (ne_zero_of_irreducible_tail b c hirr) ^ k).val := by
      rw [pow_succ', Subgroup.coe_mul]
      rfl
    rw [e1, coordinateSemilinearMap_mul, frobElt_apply, form_tailLin_sq, ih,
      frobeniusEquiv_pow_apply, frobeniusEquiv_pow_apply, ← pow_mul, pow_succ]

theorem minusSemi_quadMinus (hn : 1 ≤ n) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : ℕ)
    (y : Vm n K) : quadMinus n K b c (minusSemi hn hirr k y) = (quadMinus n K b c y) ^ 2 ^ k := by
  have h := frobPair_pow_quadMinus (n := n) (b := b) (c := c) hn hirr k
    (reindexVectorEquiv (minusIndexEquiv n hn) y)
  rw [minusSemi]
  rw [show quadMinus n K b c ((reindexVectorEquiv (minusIndexEquiv n hn)).symm
      (coordinateSemilinearMap ↑(frobPair n hn b c (ne_zero_of_irreducible_tail b c hirr) ^ k)
        ((reindexVectorEquiv (minusIndexEquiv n hn)) y)))
      = coordinateQuadMinus n K hn b c
        (coordinateSemilinearMap ↑(frobPair n hn b c (ne_zero_of_irreducible_tail b c hirr) ^ k)
          ((reindexVectorEquiv (minusIndexEquiv n hn)) y)) from rfl]
  rw [h, frobeniusEquiv_pow_apply]
  rw [show coordinateQuadMinus n K hn b c (reindexVectorEquiv (minusIndexEquiv n hn) y)
      = quadMinus n K b c y from reindexQuadraticForm_map _ _ _]

theorem minusSemi_polar (hn : 1 ≤ n) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : ℕ)
    (y z : Vm n K) :
    polar (quadMinus n K b c) (minusSemi hn hirr k y) (minusSemi hn hirr k z) =
      (polar (quadMinus n K b c) y z) ^ 2 ^ k := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hpol : ∀ x w : Vm n K, polar (quadMinus n K b c) x w =
      quadMinus n K b c (x + w) + quadMinus n K b c x + quadMinus n K b c w := by
    intro x w
    rw [show polar (quadMinus n K b c) x w = quadMinus n K b c (x + w) -
      quadMinus n K b c x - quadMinus n K b c w from rfl]
    rw [sub_eq_add_neg, sub_eq_add_neg, neg_eq_self_of_two_eq_zero h2,
      neg_eq_self_of_two_eq_zero h2]
  rw [hpol, hpol, ← minusSemi_add, minusSemi_quadMinus, minusSemi_quadMinus, minusSemi_quadMinus,
    add_pow_char_pow, add_pow_char_pow]

theorem minusSemi_surjective (hn : 1 ≤ n) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : ℕ) :
    Function.Surjective (minusSemi hn hirr k) := by
  intro y
  refine ⟨(reindexVectorEquiv (minusIndexEquiv n hn)).symm
    ((coordinateSemilinearMap ((frobPair n hn b c
      (ne_zero_of_irreducible_tail b c hirr)) ^ k).val).symm
        (reindexVectorEquiv (minusIndexEquiv n hn) y)), ?_⟩
  rw [minusSemi]
  simp only [LinearEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
    LinearEquiv.symm_apply_apply]

theorem minusSemi_eichler (hn : 1 ≤ n) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : ℕ)
    {u w y : Vm n K} (hu : quadMinus n K b c u = 0)
    (huw : polar (quadMinus n K b c) u w = 0) :
    minusSemi hn hirr k (eichler (quadMinus n K b c) u w y) =
      eichler (quadMinus n K b c) (minusSemi hn hirr k u) (minusSemi hn hirr k w)
        (minusSemi hn hirr k y) := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h2k : (2 : ℕ) ^ k ≠ 0 := by positivity
  have hu' : quadMinus n K b c (minusSemi hn hirr k u) = 0 := by
    rw [minusSemi_quadMinus, hu, zero_pow h2k]
  have huw' : polar (quadMinus n K b c) (minusSemi hn hirr k u) (minusSemi hn hirr k w) = 0 := by
    rw [minusSemi_polar, huw, zero_pow h2k]
  rw [eichler_apply hu huw, eichler_apply hu' huw', sub_eq_add_neg, sub_eq_add_neg,
    neg_eq_self_of_two_eq_zero h2, neg_eq_self_of_two_eq_zero h2,
    minusSemi_add, minusSemi_add, minusSemi_smul, minusSemi_smul,
    minusSemi_polar, minusSemi_polar, minusSemi_quadMinus, add_pow_char_pow, mul_pow]

@[expose] noncomputable def minusLevi {K : Type} [Field K] {n : ℕ} (b c : K) (i j : Fin (n - 1))
    (s t : Bool) : Subgroup (spinGroup (quadMinus n K b c)) :=
  (leviFix (elementaryGroup (quadMinus n K b c)) (framePair (minusFrame n b c).toHypFrame j t)
      (smulPair (framePair (minusFrame n b c).toHypFrame i s) one_ne_zero)).comap
      (spinAction (quadMinus n K b c)) ⊔
    (omFix (quadMinus n K b c) (framePair (minusFrame n b c).toHypFrame j t)
      (smulPair (framePair (minusFrame n b c).toHypFrame i s) one_ne_zero)).comap
      (spinAction (quadMinus n K b c))

theorem map_longRoot_of_minusSemi {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn : 1 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {φ : spinGroup (quadMinus n K b c) →* spinGroup (quadMinus n K b c)} {k : ℕ}
    (hφA : ∀ (z : spinGroup (quadMinus n K b c)) (y : Vm n K),
      spinAction (quadMinus n K b c) (φ z) (minusSemi (by omega) hirr k y) =
        minusSemi (by omega) hirr k (spinAction (quadMinus n K b c) z y))
    {i j : Fin (n - 1)} (hij : i ≠ j) (s t : Bool) (β : K) :
    φ ((minusFrame n b c).longRoot hij s t (.ofAdd β)) =
      (minusFrame n b c).longRoot hij s t (.ofAdd (β ^ 2 ^ k)) := by
  classical
  let F := minusFrame n b c
  let Q := quadMinus n K b c
  let u : Vm n K := minusVec n j t
  let w : Vm n K := β • minusVec n i s
  have hu : Q u = 0 := by
    simpa [Q, u] using quadMinus_minusVec (n := n) (b := b) (c := c) j t
  have huw : polar Q u w = 0 := by
    have h1 : polar Q u (minusVec n i s) = if j = i ∧ t = !s then 1 else 0 := by
      simpa [Q, u] using polar_minusVec_minusVec (n := n) (b := b) (c := c) j i t s
    simp only [w]
    rw [polar_smul_right_eq, h1]
    simp [hij.symm]
  have hAu : minusSemi hn hirr k u = u := by
    simpa [u] using minusSemi_minusVec (n := n) hn hirr k j t
  have hAw : minusSemi hn hirr k w = β ^ 2 ^ k • minusVec n i s := by
    simp only [w]
    rw [minusSemi_smul, minusSemi_minusVec]
  have hσk : spinAction Q (F.longRoot hij s t (.ofAdd β)) = eichler Q u w := by
    simpa [F, Q, u, w] using spinAction_longRoot_eq_eichler F.toHypFrame hij s t β
  refine RootCentOmega.spinAction_quadMinus_injective hirr ?_
  refine LinearEquiv.ext fun x => ?_
  obtain ⟨y, rfl⟩ := minusSemi_surjective hn hirr k x
  have h1 := hφA (F.longRoot hij s t (.ofAdd β)) y
  have h2 : spinAction Q (F.longRoot hij s t (.ofAdd (β ^ 2 ^ k))) (minusSemi hn hirr k y) =
      eichler Q u (β ^ 2 ^ k • minusVec n i s) (minusSemi hn hirr k y) := by
    rw [show spinAction Q (F.longRoot hij s t (.ofAdd (β ^ 2 ^ k))) =
        eichler Q u (β ^ 2 ^ k • minusVec n i s) from by
      simpa [F, Q, u] using spinAction_longRoot_eq_eichler F.toHypFrame hij s t (β ^ 2 ^ k)]
  rw [h1, hσk, minusSemi_eichler hn hirr k hu huw, hAu, hAw, h2]

theorem eq_one_of_commute_omFix {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {P₁ P₂ : HypPair Q} (hQ : (polarBilin Q).Nondegenerate)
    (hE : orthDerived Q ≤ elementaryGroup Q) (h₁₂ : P₁.Orth P₂)
    (h3 : 3 ≤ finrank K (wSub P₁ P₂))
    (hnexc : ¬ SmallFixedException (Q.restrict (wSub P₁ P₂)))
    {g : V ≃ₗ[K] V} (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hge1 : g P₁.e = P₁.e) (hgf1 : g P₁.f = P₁.f) (hge2 : g P₂.e = P₂.e)
    (hgf2 : g P₂.f = P₂.f) (hcomm : ∀ y ∈ omFix Q P₁ P₂, g * y = y * g) : g = 1 := by
  classical
  have hge1' : g⁻¹ P₁.e = P₁.e := by
    have h : g⁻¹ (g P₁.e) = P₁.e := by simp
    rwa [hge1] at h
  have hgf1' : g⁻¹ P₁.f = P₁.f := by
    have h : g⁻¹ (g P₁.f) = P₁.f := by simp
    rwa [hgf1] at h
  have hge2' : g⁻¹ P₂.e = P₂.e := by
    have h : g⁻¹ (g P₂.e) = P₂.e := by simp
    rwa [hge2] at h
  have hgf2' : g⁻¹ P₂.f = P₂.f := by
    have h : g⁻¹ (g P₂.f) = P₂.f := by simp
    rwa [hgf2] at h
  have hgW : ∀ x ∈ wSub P₁ P₂, g x ∈ wSub P₁ P₂ := by
    intro x hx
    rw [mem_wSub] at hx ⊢
    obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
    refine ⟨?_, ?_, ?_, ?_⟩
    · have h1 : polar Q P₁.e (g x) = polar Q (g⁻¹ P₁.e) x := by
        conv_lhs => rw [← LinearEquiv.apply_symm_apply g P₁.e]
        exact polar_map_of_mem hgO _ _
      rw [h1, hge1', hx1]
    · have h1 : polar Q P₁.f (g x) = polar Q (g⁻¹ P₁.f) x := by
        conv_lhs => rw [← LinearEquiv.apply_symm_apply g P₁.f]
        exact polar_map_of_mem hgO _ _
      rw [h1, hgf1', hx2]
    · have h1 : polar Q P₂.e (g x) = polar Q (g⁻¹ P₂.e) x := by
        conv_lhs => rw [← LinearEquiv.apply_symm_apply g P₂.e]
        exact polar_map_of_mem hgO _ _
      rw [h1, hge2', hx3]
    · have h1 : polar Q P₂.f (g x) = polar Q (g⁻¹ P₂.f) x := by
        conv_lhs => rw [← LinearEquiv.apply_symm_apply g P₂.f]
        exact polar_map_of_mem hgO _ _
      rw [h1, hgf2', hx4]
  have hgWinv : ∀ x ∈ wSub P₁ P₂, g⁻¹ x ∈ wSub P₁ P₂ := by
    intro x hx
    rw [mem_wSub] at hx ⊢
    obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
    refine ⟨?_, ?_, ?_, ?_⟩
    · have h1 : polar Q P₁.e (g⁻¹ x) = polar Q P₁.e x := by
        have h := polar_map_of_mem hgO (g⁻¹ P₁.e) (g⁻¹ x)
        rw [show g (g⁻¹ P₁.e) = P₁.e from LinearEquiv.apply_symm_apply g P₁.e,
          show g (g⁻¹ x) = x from LinearEquiv.apply_symm_apply g x, hge1'] at h
        exact h.symm
      rw [h1, hx1]
    · have h1 : polar Q P₁.f (g⁻¹ x) = polar Q P₁.f x := by
        have h := polar_map_of_mem hgO (g⁻¹ P₁.f) (g⁻¹ x)
        rw [show g (g⁻¹ P₁.f) = P₁.f from LinearEquiv.apply_symm_apply g P₁.f,
          show g (g⁻¹ x) = x from LinearEquiv.apply_symm_apply g x, hgf1'] at h
        exact h.symm
      rw [h1, hx2]
    · have h1 : polar Q P₂.e (g⁻¹ x) = polar Q P₂.e x := by
        have h := polar_map_of_mem hgO (g⁻¹ P₂.e) (g⁻¹ x)
        rw [show g (g⁻¹ P₂.e) = P₂.e from LinearEquiv.apply_symm_apply g P₂.e,
          show g (g⁻¹ x) = x from LinearEquiv.apply_symm_apply g x, hge2'] at h
        exact h.symm
      rw [h1, hx3]
    · have h1 : polar Q P₂.f (g⁻¹ x) = polar Q P₂.f x := by
        have h := polar_map_of_mem hgO (g⁻¹ P₂.f) (g⁻¹ x)
        rw [show g (g⁻¹ P₂.f) = P₂.f from LinearEquiv.apply_symm_apply g P₂.f,
          show g (g⁻¹ x) = x from LinearEquiv.apply_symm_apply g x, hgf2'] at h
        exact h.symm
      rw [h1, hx4]
  let z : wSub P₁ P₂ ≃ₗ[K] wSub P₁ P₂ :=
    CFSG.RankThree.PartOne.KCOrthogonal.restrictEquiv (wSub P₁ P₂) g hgW hgWinv
  have hzO : z ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.restrict (wSub P₁ P₂)) := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro w
    rw [QuadraticMap.restrict_apply, QuadraticMap.restrict_apply]
    change Q (g (w : V)) = Q (w : V)
    exact map_of_mem hgO (w : V)
  have hfix_uPart : ∀ v, g (uPart P₁ P₂ v) = uPart P₁ P₂ v := by
    intro v
    simp only [uPart, map_add, map_smul, hge1, hgf1, hge2, hgf2]
  have hextW : extW P₁ P₂ h₁₂ z = g := by
    refine LinearEquiv.ext fun v => ?_
    rw [extW_apply]
    have hz : (z ⟨v - uPart P₁ P₂ v, mem_wSub.mpr (inW_sub_uPart h₁₂ v)⟩ : V) =
        g (v - uPart P₁ P₂ v) :=
      CFSG.RankThree.PartOne.KCOrthogonal.coe_restrictEquiv (wSub P₁ P₂) g hgW hgWinv
        ⟨v - uPart P₁ P₂ v, mem_wSub.mpr (inW_sub_uPart h₁₂ v)⟩
    rw [hz, map_sub, hfix_uPart]
    abel
  have hextW_inj : Function.Injective (extW P₁ P₂ h₁₂) := by
    intro a b hab
    refine LinearEquiv.ext fun w => ?_
    have h := congrArg (fun e : V ≃ₗ[K] V => e (w : V)) hab
    simp only [extW_apply_w] at h
    exact Subtype.ext h
  have hzc : ∀ y ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup (Q.restrict (wSub P₁ P₂)),
      TauCeti.QuadraticMap.orthogonalGroup (Q.restrict (wSub P₁ P₂))⁆, z * y = y * z := by
    intro y hy
    have hyE : extW P₁ P₂ h₁₂ y ∈ elementaryGroup Q := hE (extW_mem_orthDerived h₁₂ hy)
    have hyom : extW P₁ P₂ h₁₂ y ∈ omFix Q P₁ P₂ := by
      refine mem_omFix.mpr ⟨hyE, ?_, ?_, ?_, ?_⟩
      · exact extW_apply_u h₁₂ y mem_spanU₄_e₁
      · exact extW_apply_u h₁₂ y mem_spanU₄_f₁
      · exact extW_apply_u h₁₂ y mem_spanU₄_e₂
      · exact extW_apply_u h₁₂ y mem_spanU₄_f₂
    apply hextW_inj
    rw [map_mul, map_mul, hextW]
    exact hcomm _ hyom
  have hz1 : z = 1 :=
    CFSG.StandardType.LayerCores.OrthRegular.eq_one_of_commute_orthDerived
      (W := wSub P₁ P₂) (Q := Q.restrict (wSub P₁ P₂)) (z := z)
      (nondegenerate_restrict_wSub hQ h₁₂) h3 hnexc hzO hzc
  rw [← hextW, hz1, map_one]

theorem eq_self_of_minusLevi_conj {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hn4 : 4 ≤ n)
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {φ : spinGroup (quadMinus n K b c) →* spinGroup (quadMinus n K b c)} {k : ℕ}
    (hφA : ∀ (z : spinGroup (quadMinus n K b c)) (y : Vm n K),
      spinAction (quadMinus n K b c) (φ z) (minusSemi (by omega) hirr k y) =
        minusSemi (by omega) hirr k (spinAction (quadMinus n K b c) z y))
    {i j : Fin (n - 1)} (hij : i ≠ j) (s t : Bool) {h : spinGroup (quadMinus n K b c)}
    (hh : h ∈ minusLevi b c i j s t)
    (hkey : ∀ z ∈ minusLevi b c i j s t, φ z ∈ minusLevi b c i j s t → h * φ z * h⁻¹ = z) :
    ∀ z, φ z = z := by
  have hn1 : 1 ≤ n := by omega
  classical
  let F := minusFrame n b c
  let Q := quadMinus n K b c
  let P₁ : HypPair Q := framePair F.toHypFrame j t
  let P₂ : HypPair Q := smulPair (framePair F.toHypFrame i s) one_ne_zero
  let L₁ := leviFix (elementaryGroup Q) P₁ P₂
  let L₂ := omFix Q P₁ P₂
  let σ := spinAction Q
  let A := minusSemi hn1 hirr k
  let z₀ : Vm n K := planeVec n planeOne
  let p : K := (tailSeq b c k).1
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hQnd : (polarBilin Q).Nondegenerate := by
    simpa [Q] using nondegenerate_polarBilin_quadMinus_of_finite n K hirr
  have h₁₂ : P₁.Orth P₂ := by
    simpa [P₁, P₂, F] using RCSTOm.orth₁₂ F.toHypFrame hij s t one_ne_zero
  have hrange : σ.range = elementaryGroup Q := by
    simpa [σ, Q] using range_spinAction_quadMinus hn4 hirr
  have hσ : Function.Injective σ := by
    simpa [σ, Q] using spinAction_quadMinus_injective (b := b) (c := c) hirr
  have hPL : minusLevi b c i j s t = L₁.comap σ ⊔ L₂.comap σ := rfl
  let kf : K → spinGroup Q := fun β => F.longRoot hij (!s) t (.ofAdd β)
  have hσk : ∀ β : K, σ (kf β) = eichler Q P₁.e (β • P₂.f) := by
    intro β
    simpa [kf, σ, Q, P₁, P₂, F, framePair, smulPair, inv_one, one_smul]
      using spinAction_longRoot_eq_eichler F.toHypFrame hij (!s) t β
  have hk_mem : ∀ β : K, kf β ∈ minusLevi b c i j s t := by
    intro β
    rw [hPL]
    refine Subgroup.mem_sup_left (Subgroup.mem_comap.mpr ?_)
    rw [hσk β]
    exact (eichler_mem_leviFix h₁₂ (eichler_mem_elementaryGroup Q) β).1
  have hk_φ : ∀ β : K, φ (kf β) = kf (β ^ 2 ^ k) := by
    intro β
    exact map_longRoot_of_minusSemi hn1 hirr hφA hij (!s) t β
  have hkey_b : ∀ β : K, h * kf (β ^ 2 ^ k) * h⁻¹ = kf β := by
    intro β
    have hφmem : φ (kf β) ∈ minusLevi b c i j s t := by
      rw [hk_φ β]
      exact hk_mem (β ^ 2 ^ k)
    have h1 := hkey (kf β) (hk_mem β) hφmem
    rwa [hk_φ β] at h1
  have hcommE : σ h * eichler Q P₁.e P₂.f = eichler Q P₁.e P₂.f * σ h := by
    have h1 : h * kf 1 * h⁻¹ = kf 1 := by simpa using hkey_b 1
    have h2' := congrArg σ h1
    rw [map_mul, map_mul, map_inv, hσk 1, one_smul] at h2'
    calc σ h * eichler Q P₁.e P₂.f
        = σ h * eichler Q P₁.e P₂.f * (σ h)⁻¹ * σ h := by group
      _ = eichler Q P₁.e P₂.f * σ h := by rw [h2']
  let N : Vm n K →ₗ[K] Vm n K := eichlerLin Q P₁.e P₂.f - LinearMap.id
  have hN_apply : ∀ y, N y = polar Q y P₁.e • P₂.f -
      (polar Q y P₂.f + Q P₂.f * polar Q y P₁.e) • P₁.e := by
    intro y
    simp only [N, LinearMap.sub_apply, eichlerLin_apply, LinearMap.id_apply]
    abel
  have hE_apply : ∀ y, eichler Q P₁.e P₂.f y = y + N y := by
    intro y
    rw [eichler_apply P₁.Q_e h₁₂.ef, hN_apply]
    abel
  have hNcomm : ∀ y, σ h (N y) = N (σ h y) := by
    intro y
    have h1 : σ h (eichler Q P₁.e P₂.f y) = eichler Q P₁.e P₂.f (σ h y) := by
      have h := congrArg (fun e => e y) hcommE
      simpa [LinearEquiv.mul_apply] using h
    rw [hE_apply, hE_apply, map_add] at h1
    exact add_left_cancel h1
  have hEb_apply : ∀ (β : K) (y : Vm n K),
      eichler Q P₁.e (β • P₂.f) y = y + β • N y := by
    intro β y
    have hQb : Q (β • P₂.f) = 0 := by
      rw [QuadraticMap.map_smul, P₂.Q_f, smul_zero]
    have huwb : polar Q P₁.e (β • P₂.f) = 0 := by
      rw [polar_smul_right_eq, h₁₂.ef, mul_zero]
    rw [eichler_apply P₁.Q_e huwb, hN_apply]
    simp only [polar_smul_right_eq, hQb, P₂.Q_f, mul_zero, zero_mul, add_zero, smul_sub,
      smul_smul]
    module
  have hcommb : ∀ β : K, σ h * eichler Q P₁.e (β • P₂.f) =
      eichler Q P₁.e (β • P₂.f) * σ h := by
    intro β
    refine LinearEquiv.ext fun x => ?_
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hEb_apply, hEb_apply, map_add, map_smul,
      hNcomm]
  have hβ : ∀ β : K, β ^ 2 ^ k = β := by
    intro β
    have h1 := congrArg σ (hkey_b β)
    rw [map_mul, map_mul, map_inv, hσk (β ^ 2 ^ k), hσk β] at h1
    have h2' : eichler Q P₁.e ((β ^ 2 ^ k) • P₂.f) = eichler Q P₁.e (β • P₂.f) := by
      have hb' := hcommb β
      calc eichler Q P₁.e ((β ^ 2 ^ k) • P₂.f)
          = (σ h)⁻¹ * (σ h * eichler Q P₁.e ((β ^ 2 ^ k) • P₂.f) * (σ h)⁻¹) * σ h := by
            group
        _ = (σ h)⁻¹ * eichler Q P₁.e (β • P₂.f) * σ h := by rw [h1]
        _ = eichler Q P₁.e (β • P₂.f) := by
              calc (σ h)⁻¹ * eichler Q P₁.e (β • P₂.f) * σ h
                  = (σ h)⁻¹ * (eichler Q P₁.e (β • P₂.f) * σ h) := by group
                _ = (σ h)⁻¹ * (σ h * eichler Q P₁.e (β • P₂.f)) := by rw [← hb']
                _ = eichler Q P₁.e (β • P₂.f) := by group
    have hNf : N P₁.f = P₂.f := by
      rw [hN_apply, P₁.polar_fe, h₁₂.ff, P₂.Q_f]
      simp
    have hA1 := hEb_apply (β ^ 2 ^ k) P₁.f
    have hB1 := hEb_apply β P₁.f
    rw [hNf] at hA1 hB1
    have h5 : eichler Q P₁.e ((β ^ 2 ^ k) • P₂.f) P₁.f =
        eichler Q P₁.e (β • P₂.f) P₁.f := by rw [h2']
    rw [hA1, hB1] at h5
    have h4 : (β ^ 2 ^ k) • P₂.f = β • P₂.f := add_left_cancel h5
    have hsub : (β ^ 2 ^ k - β) • P₂.f = 0 := by rw [sub_smul, h4, sub_self]
    rcases smul_eq_zero.mp hsub with hzero | hzero
    · exact sub_eq_zero.mp hzero
    · exact absurd hzero P₂.f_ne_zero
  have hs : (tailSeq b c k).2 = 1 := by
    have hbs := tailSeq_snd_mul (b := b) (c := c) k
    have hb : b ≠ 0 := ne_zero_of_irreducible_tail b c hirr
    rw [hβ b] at hbs
    refine mul_right_cancel₀ hb ?_
    rw [hbs, one_mul]
  have hA_apply : ∀ y : Vm n K, A y = y + (p * y (Sum.inr (Sum.inr 1))) • z₀ := by
    intro y
    funext x
    rcases x with m | m | u
    · rw [show A y (Sum.inl m) = minusSemi hn1 hirr k y (Sum.inl m) from rfl,
        minusSemi_apply_inl]
      simp [z₀, planeVec, hβ]
    · rw [show A y (Sum.inr (Sum.inl m)) = minusSemi hn1 hirr k y (Sum.inr (Sum.inl m)) from rfl,
        minusSemi_apply_inr_inl]
      simp [z₀, planeVec, hβ]
    · have hu : u = 0 ∨ u = 1 := by
        have hlt : u.val < 2 := u.isLt
        have h : u.val = 0 ∨ u.val = 1 := by omega
        rcases h with h | h
        · exact Or.inl (Fin.ext (by simpa using h))
        · exact Or.inr (Fin.ext (by simpa using h))
      rcases hu with h | h
      · subst h
        rw [show A y (Sum.inr (Sum.inr 0)) = minusSemi hn1 hirr k y (Sum.inr (Sum.inr 0)) from rfl,
          minusSemi_apply_tailZero, hβ, hβ]
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rw [show z₀ (Sum.inr (Sum.inr 0)) = 1 from rfl, mul_one]
      · subst h
        rw [show A y (Sum.inr (Sum.inr 1)) = minusSemi hn1 hirr k y (Sum.inr (Sum.inr 1)) from rfl,
          minusSemi_apply_tailOne, hβ]
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hs, one_mul]
        rw [show z₀ (Sum.inr (Sum.inr 1)) = 0 from rfl, mul_zero, add_zero]
  by_cases hp : p = 0
  · intro z
    have hAid : A = id := by
      funext y
      rw [hA_apply y, hp]
      simp
    apply hσ
    refine LinearEquiv.ext fun y => ?_
    have h1 := hφA z y
    simpa [A, hAid] using h1
  · exfalso
    have hAO : ∀ y : Vm n K, Q (A y) = Q y := by
      intro y
      rw [show A y = minusSemi hn1 hirr k y from rfl, minusSemi_quadMinus, hβ]
    have hz0Q : Q z₀ = 1 := by
      show quadMinus n K b c (planeVec n planeOne) = 1
      exact quadMinus_planeOne n b c
    let z₁ : Vm n K := Pi.single (Sum.inr (Sum.inr 1)) 1
    have hz1Q : Q z₁ = c := by
      rw [show Q = quadMinus n K b c from rfl]
      simp [z₁, quadMinus_apply, Pi.single_apply]
    have hz1z0 : polar Q z₁ z₀ = b := by
      rw [show Q = quadMinus n K b c from rfl, show z₀ = planeVec n planeOne from rfl,
        polar_quadMinus]
      simp [z₁, planeVec, planeOne, Pi.single_apply]
    have hp_eq : p = b := by
      have hzt : z₁ (Sum.inr (Sum.inr 1)) = 1 := by simp [z₁]
      have h1 : Q (A z₁) = Q z₁ := hAO z₁
      rw [hA_apply, hzt, mul_one, QuadraticMap.map_add (⇑Q), QuadraticMap.map_smul,
        smul_eq_mul, polar_smul_right_eq, hz1Q, hz0Q, hz1z0, mul_one] at h1
      have h2' : p ^ 2 + p * b = 0 := by linear_combination h1
      have hpb : p + b = 0 := (mul_eq_zero.mp (by linear_combination h2')).resolve_left hp
      have h3 : p = -b := eq_neg_of_add_eq_zero_left hpb
      rwa [neg_eq_self_of_two_eq_zero h2] at h3
    letI : Invertible (Q z₀) := invertibleOfNonzero (by rw [hz0Q]; exact one_ne_zero)
    let r : Vm n K ≃ₗ[K] Vm n K := TauCeti.QuadraticMap.reflection Q z₀
    have hpolar_z0 : ∀ y : Vm n K, polar Q z₀ y = b * y (Sum.inr (Sum.inr 1)) := by
      intro y
      rw [show Q = quadMinus n K b c from rfl, show z₀ = planeVec n planeOne from rfl,
        polar_quadMinus]
      have h0 : (planeVec n planeOne : Vm n K) (Sum.inr (Sum.inr 0)) = 1 := rfl
      have h1 : (planeVec n planeOne : Vm n K) (Sum.inr (Sum.inr 1)) = 0 := rfl
      have h2' : ∀ m : Fin (n - 1), (planeVec n planeOne : Vm n K) (Sum.inl m) = 0 :=
        fun m => rfl
      have h3 : ∀ m : Fin (n - 1), (planeVec n planeOne : Vm n K) (Sum.inr (Sum.inl m)) = 0 :=
        fun m => rfl
      simp only [h0, h1, h2', h3, mul_zero, mul_one, zero_mul, add_zero, zero_add,
        Finset.sum_const_zero]
      linear_combination y (Sum.inr (Sum.inr 0)) * h2
    have hr_apply : ∀ y, r y = y + polar Q z₀ y • z₀ := by
      intro y
      rw [show r = TauCeti.QuadraticMap.reflection Q z₀ from rfl,
        TauCeti.QuadraticMap.reflection_apply, invOf_eq_inv, hz0Q, inv_one, one_mul,
        sub_eq_add_neg, neg_eq_self_of_two_eq_zero h2]
    have hAr : ∀ y, A y = r y := by
      intro y
      rw [hA_apply y, hp_eq, hr_apply y, hpolar_z0 y]
    have hAe1 : A P₁.e = P₁.e := by
      simpa [A, P₁, F, framePair] using minusSemi_minusVec (n := n) hn1 hirr k j t
    have hAf1 : A P₁.f = P₁.f := by
      simpa [A, P₁, F, framePair] using minusSemi_minusVec (n := n) hn1 hirr k j (!t)
    have hAe2 : A P₂.e = P₂.e := by
      simpa [A, P₂, F, framePair, smulPair] using minusSemi_minusVec (n := n) hn1 hirr k i s
    have hAf2 : A P₂.f = P₂.f := by
      simpa [A, P₂, F, framePair, smulPair] using minusSemi_minusVec (n := n) hn1 hirr k i (!s)
    have hr_e1 : r P₁.e = P₁.e := by rw [← hAr P₁.e, hAe1]
    have hr_f1 : r P₁.f = P₁.f := by rw [← hAr P₁.f, hAf1]
    have hr_e2 : r P₂.e = P₂.e := by rw [← hAr P₂.e, hAe2]
    have hr_f2 : r P₂.f = P₂.f := by rw [← hAr P₂.f, hAf2]
    have hrinv : ∀ x, r x = x → r⁻¹ x = x := by
      intro x hx
      have h := LinearEquiv.symm_apply_apply r x
      rwa [hx] at h
    have hrO : r ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
      rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
      intro y
      rw [← hAr y]
      exact hAO y
    have hφL₂ : ∀ z : spinGroup Q, z ∈ L₂.comap σ → φ z ∈ L₂.comap σ := by
      intro z hz
      rw [Subgroup.mem_comap] at hz ⊢
      obtain ⟨-, hze1, hzf1, hze2, hzf2⟩ := mem_omFix.mp hz
      have hconj : ∀ y, σ (φ z) (r y) = r (σ z y) := by
        intro y
        have h : σ (φ z) (A y) = A (σ z y) := hφA z y
        rwa [hAr y, hAr (σ z y)] at h
      refine mem_omFix.mpr ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [← hrange]
        exact ⟨φ z, rfl⟩
      · have h := hconj P₁.e
        rw [hr_e1, hze1, hr_e1] at h
        exact h
      · have h := hconj P₁.f
        rw [hr_f1, hzf1, hr_f1] at h
        exact h
      · have h := hconj P₂.e
        rw [hr_e2, hze2, hr_e2] at h
        exact h
      · have h := hconj P₂.f
        rw [hr_f2, hzf2, hr_f2] at h
        exact h
    have hL₁cent : L₁.comap σ ≤ Subgroup.centralizer (L₂.comap σ : Set (spinGroup Q)) := by
      intro x hx
      have hx' : σ x ∈ L₁ := hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hy' : σ y ∈ L₂ := hy
      have hc := Subgroup.mem_centralizer_iff.mp (leviFix_le_centralizer_omFix h₁₂ hx') (σ y) hy'
      apply hσ
      simpa [map_mul] using hc
    have hL₁norm : L₁.comap σ ≤ Subgroup.normalizer (L₂.comap σ : Set (spinGroup Q)) :=
      hL₁cent.trans (Subgroup.centralizer_le_normalizer _)
    have hh' : h ∈ (L₁.comap σ ⊔ L₂.comap σ : Subgroup (spinGroup Q)) := hPL ▸ hh
    have hcoe := Subgroup.coe_mul_of_left_le_normalizer_right (L₁.comap σ) (L₂.comap σ) hL₁norm
    have hh'' : h ∈ (↑(L₁.comap σ) : Set (spinGroup Q)) * (↑(L₂.comap σ) : Set (spinGroup Q)) := by
      rw [← hcoe]
      exact hh'
    rw [Set.mem_mul] at hh''
    obtain ⟨h₁, hh₁, h₂, hh₂, hh_eq⟩ := hh''
    have hh₁' : σ h₁ ∈ L₁ := Subgroup.mem_comap.mp hh₁
    have hh₂' : σ h₂ ∈ L₂ := Subgroup.mem_comap.mp hh₂
    have hg₂comm : ∀ y ∈ omFix Q P₁ P₂, (σ h₂ * r) * y = y * (σ h₂ * r) := by
      intro y hy
      have hyE : y ∈ elementaryGroup Q := (mem_omFix.mp hy).1
      rw [← hrange] at hyE
      obtain ⟨z, hz⟩ := hyE
      have hzL₂ : z ∈ L₂.comap σ := by
        show σ z ∈ L₂
        rw [hz]
        exact hy
      have hzPL : z ∈ minusLevi b c i j s t := by
        rw [hPL]
        exact Subgroup.mem_sup_right hzL₂
      have hφzPL : φ z ∈ minusLevi b c i j s t := by
        rw [hPL]
        exact Subgroup.mem_sup_right (hφL₂ z hzL₂)
      have h1 := hkey z hzPL hφzPL
      have hφzL₂ : σ (φ z) ∈ L₂ := Subgroup.mem_comap.mp (hφL₂ z hzL₂)
      have hXmem : σ h₂ * σ (φ z) * (σ h₂)⁻¹ ∈ L₂ :=
        mul_mem (mul_mem hh₂' hφzL₂) (inv_mem hh₂')
      have h3 : σ h₁ * (σ h₂ * σ (φ z) * (σ h₂)⁻¹) * (σ h₁)⁻¹ = σ z := by
        have h1' : h₁ * h₂ * φ z * (h₁ * h₂)⁻¹ = z := by rw [hh_eq]; exact h1
        have h4 := congrArg σ h1'
        simp only [map_mul, map_inv] at h4
        calc σ h₁ * (σ h₂ * σ (φ z) * (σ h₂)⁻¹) * (σ h₁)⁻¹
            = σ h₁ * σ h₂ * σ (φ z) * (σ h₁ * σ h₂)⁻¹ := by group
          _ = σ z := h4
      have hXh₁ : σ h₁ * (σ h₂ * σ (φ z) * (σ h₂)⁻¹) =
          (σ h₂ * σ (φ z) * (σ h₂)⁻¹) * σ h₁ :=
        (Subgroup.mem_centralizer_iff.mp (leviFix_le_centralizer_omFix h₁₂ hh₁') _ hXmem).symm
      have hXeq : σ h₂ * σ (φ z) * (σ h₂)⁻¹ = σ z := by
        rw [← h3, hXh₁]
        group
      have hconj2 : ∀ y, σ (φ z) (r y) = r (σ z y) := by
        intro y
        have h : σ (φ z) (A y) = A (σ z y) := hφA z y
        rwa [hAr y, hAr (σ z y)] at h
      have hrconj : r * σ z * r⁻¹ = σ (φ z) := by
        refine LinearEquiv.ext fun x => ?_
        obtain ⟨y, rfl⟩ : ∃ y, r y = x := ⟨r⁻¹ x, LinearEquiv.apply_symm_apply r x⟩
        rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply,
          show r⁻¹ (r y) = y from LinearEquiv.symm_apply_apply r y, hconj2 y]
      have hXeq' : (σ h₂)⁻¹ * σ z * σ h₂ = σ (φ z) := by
        calc (σ h₂)⁻¹ * σ z * σ h₂
            = (σ h₂)⁻¹ * (σ h₂ * σ (φ z) * (σ h₂)⁻¹) * σ h₂ := by rw [hXeq]
          _ = σ (φ z) := by group
      have h5 : r * σ z * r⁻¹ = (σ h₂)⁻¹ * σ z * σ h₂ := by
        rw [hrconj, ← hXeq']
      have hfin : σ h₂ * r * σ z = σ z * (σ h₂ * r) := by
        calc σ h₂ * r * σ z = σ h₂ * (r * σ z * r⁻¹) * r := by group
          _ = σ h₂ * ((σ h₂)⁻¹ * σ z * σ h₂) * r := by rw [h5]
          _ = σ z * (σ h₂ * r) := by group
      rw [← hz]
      exact hfin
    have hg₂O : (σ h₂ * r) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
      mul_mem (elementaryGroup_le_orthogonalGroup Q (mem_omFix.mp hh₂').1) hrO
    have hg₂e1 : (σ h₂ * r) P₁.e = P₁.e := by
      rw [LinearEquiv.mul_apply, hr_e1, (mem_omFix.mp hh₂').2.1]
    have hg₂f1 : (σ h₂ * r) P₁.f = P₁.f := by
      rw [LinearEquiv.mul_apply, hr_f1, (mem_omFix.mp hh₂').2.2.1]
    have hg₂e2 : (σ h₂ * r) P₂.e = P₂.e := by
      rw [LinearEquiv.mul_apply, hr_e2, (mem_omFix.mp hh₂').2.2.2.1]
    have hg₂f2 : (σ h₂ * r) P₂.f = P₂.f := by
      rw [LinearEquiv.mul_apply, hr_f2, (mem_omFix.mp hh₂').2.2.2.2]
    have hdimW : 3 ≤ finrank K (wSub P₁ P₂) := by
      have h := RCSTOm.finrank_wSub_add_four (Q := Q) h₁₂
      rw [show finrank K (Vm n K) = 2 * n from RCSTOm.finrank_quadMinus hn1] at h
      omega
    have hnexc : ¬ SmallFixedException (Q.restrict (wSub P₁ P₂)) := by
      intro hS
      have hdim := RCSTOm.finrank_wSub_add_four (Q := Q) h₁₂
      rw [show finrank K (Vm n K) = 2 * n from RCSTOm.finrank_quadMinus hn1] at hdim
      rcases hS with ⟨h3', -⟩ | ⟨⟨h4', S, hSd, hS0⟩, -⟩
      · omega
      · have hn : n = 4 := by omega
        subst hn
        obtain ⟨u, hu, hu0⟩ := exists_restrict_ne_zero_minus (n := 4) (by omega) hirr h₁₂ S hSd
        exact hu0 (hS0 u hu)
    have hOE : orthDerived Q ≤ elementaryGroup Q := by
      rw [CFSG.RankThree.Classical2.orthDerived,
        commutator_orthogonalGroup_quadMinus hn4 hirr]
    have hg₂1 : σ h₂ * r = 1 :=
      eq_one_of_commute_omFix hQnd hOE h₁₂ hdimW hnexc hg₂O hg₂e1 hg₂f1 hg₂e2 hg₂f2 hg₂comm
    have hr_eq : r = (σ h₂)⁻¹ := by
      calc r = (σ h₂)⁻¹ * (σ h₂ * r) := by group
        _ = (σ h₂)⁻¹ * 1 := by rw [hg₂1]
        _ = (σ h₂)⁻¹ := by rw [mul_one]
    have hrE : r ∈ elementaryGroup Q := by
      rw [hr_eq]
      exact inv_mem (mem_omFix.mp hh₂').1
    have hrΩ : r ∈ omegaGroup Q hQnd := elementaryGroup_quadMinus_le_omegaGroup hirr hn4 hrE
    have heven : Even (finrank K (commSpace r)) := (mem_omegaGroup.mp hrΩ).2
    rw [show commSpace r = commSpace (TauCeti.QuadraticMap.reflection Q z₀) from rfl,
      finrank_commSpace_reflection hQnd z₀] at heven
    rcases heven with ⟨m, hm⟩
    omega

end CFSG.StandardType.KGOm

end
