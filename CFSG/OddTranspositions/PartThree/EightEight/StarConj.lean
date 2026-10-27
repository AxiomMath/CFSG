module

public import CFSG.OddTranspositions.PartThree.EightEight.StarBlocks

import CFSG.OddTranspositions.PartThree.EightEight.Eighteen
import CFSG.OddTranspositions.PartThree.EightEight.StarOrbit
import CFSG.OddTranspositions.PartThree.EightEight.ThirdCentralizer
import CFSG.OddTranspositions.PartThree.EightFive.Transitive
import CFSG.OddTranspositions.PartThree.HalphaCentralizer
import CFSG.OddTranspositions.SixSeven
import CFSG.OddTranspositions.SixSevenLocalStep
import CFSG.OddTranspositions.TheoremTwo.DiffBlock
import CFSG.CGT.T75E.Lemma26
import CFSG.CGT.Timmesfeld75.Sec3TenCaseA
import CFSG.CGT.Timmesfeld75.Sec4CaseIBasic
import CFSG.CGT.Timmesfeld75.Sec4CaseIIIFour
import CFSG.CGT.Timmesfeld75.Sec4CaseIJFamily
import CFSG.CGT.Timmesfeld75.Sec4CaseIJIdent
import CFSG.CGT.Timmesfeld75.Sec4CaseIPGroup
import CFSG.CGT.Timmesfeld75.Sec4CaseIPartition4
import CFSG.CGT.Timmesfeld75.Sec4Three
import CFSG.CGT.Timmesfeld75.Sec5FiveEng
import CFSG.CGT.Timmesfeld75.Step511Card
import CFSG.CGT.Timmesfeld75.Step57Reduction
import CFSG.Combinatorics.AperiodicCentralInvolution
import CFSG.Combinatorics.AperiodicFiveOfSix
import CFSG.Combinatorics.AperiodicOppositeComponents
import CFSG.Combinatorics.AperiodicSixteenGraphDistances
import CFSG.Combinatorics.OuterLayerPredecessors
import CFSG.GH74.Uniqueness.Bender.OddCentralizer
import CFSG.GH74.Uniqueness.Bender.Unitary
import CFSG.GroupTheory.CardSupInf
import CFSG.GroupTheory.PerfectLeOfPGroupQuotient
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
import CFSG.LocalAnalysis.ComponentClassification.Asc76BenderFacts
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3GoldschmidtFacts
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvUnitary
import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderAutE4Unitary
import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderONan
import CFSG.OddTranspositions.AlmostSimple
import CFSG.OddTranspositions.BlockAction2
import CFSG.OddTranspositions.CommutatorSize
import CFSG.OddTranspositions.Disconnected
import CFSG.OddTranspositions.O4PairTenThreeTranspositions
import CFSG.OddTranspositions.Reduction
import CFSG.OddTranspositions.WidthTwoNoProduct
import CFSG.OddTranspositions.WreathQuotient
import CFSG.RankThree.GF2n.Tim79aSec2
import CFSG.RankThree.GF2n.Tim79aSec23Inputs
import CFSG.RankThree.GF2n.Tim79aSec23NoSqE1
import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Defs

public section

namespace CFSG.OddTranspositions.PartThree.EightEight

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
open CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.QZ

variable {G : Type} [Group G] [Finite G] {D : Set G}

omit [Finite G] in
theorem conjOrbit_eq_of_mem {M : Subgroup G} {u v : G} (hv : v ∈ conjOrbit M u) :
    conjOrbit M v = conjOrbit M u := by
  obtain ⟨n, hn, rfl⟩ := hv
  ext w
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m * n, M.mul_mem hm hn, by group⟩
  · rintro ⟨m, hm, rfl⟩
    refine ⟨m * n⁻¹, M.mul_mem hm (M.inv_mem hn), ?_⟩
    group

omit [Finite G] in
theorem orderOf_conj_mul_mul_and_pow_eq {x w y k : G} {n : ℕ}
    (hk : k ∈ localGroup D ((x * y * w) ^ n)) :
    orderOf (k * x * k⁻¹ * (k * y * k⁻¹) * (k * w * k⁻¹)) = orderOf (x * y * w) ∧
      (k * x * k⁻¹ * (k * y * k⁻¹) * (k * w * k⁻¹)) ^ n = (x * y * w) ^ n := by
  have hprod : k * x * k⁻¹ * (k * y * k⁻¹) * (k * w * k⁻¹) =
      k * (x * y * w) * k⁻¹ := by
    group
  have hkz : Commute k ((x * y * w) ^ n) := commute_of_mem_localGroup hk
  have hzfix : k * (x * y * w) ^ n * k⁻¹ = (x * y * w) ^ n := by
    rw [hkz.eq]
    group
  constructor
  · rw [hprod]
    simpa [MulAut.conj_apply] using (MulAut.conj k).orderOf_eq (x * y * w)
  · rw [hprod, conj_pow, hzfix]

theorem pow_notMem_of_isTriangle (h86 : Lemma8_6) (h87 : Theorem8_7) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) (hO4 : ¬ O4PairData G D)
    (hF : FaithfulOnBlocks hC.alpha)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {x w y : G} (ht : IsTriangle D x w y) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) : (x * y * w) ^ n ∉ D := by
  intro hz
  obtain ⟨β, hβ, hxβ, hyβ, -, -⟩ :=
    exists_mem_blockClass_of_pow_mem hC hne ht hn hord hz
  exact (not_commute_of_mem_of_mem h86 h87 hC hrad hO4 hF hne hβ hxβ hyβ
    ht.2.2.2.1) ht.2.2.2.2.1

theorem exists_setOf_commute_mem_conjOrbit_eq (h86 : Lemma8_6) (h87 : Theorem8_7)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hO4 : ¬ O4PairData G D) (hF : FaithfulOnBlocks hC.alpha)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {x w y : G} (ht : IsTriangle D x w y) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) {a : G}
    (ha : a ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x) :
    ∃ a' ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x, a' ≠ a ∧ Commute a a' ∧
      {r | r ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x ∧ Commute r a} =
        {a, a', a * a' * (x * y * w) ^ n} := by
  obtain ⟨k, hk, rfl⟩ := ha
  refine ⟨k * y * k⁻¹, ?_, ?_, ?_, ?_⟩
  · exact conj_mem_conjOrbit hk (mem_conjOrbit_of_third_kind hC.setup ht hn hord).1
  · intro h
    apply ht.2.2.2.1
    have h' := congrArg (fun t => k⁻¹ * t * k) h
    calc x = k⁻¹ * (k * x * k⁻¹) * k := by group
      _ = k⁻¹ * (k * y * k⁻¹) * k := h'.symm
      _ = y := by group
  · exact ht.2.2.2.2.1.conj k
  · set z : G := (x * y * w) ^ n with hzdef
    have htri : IsTriangle D (k * x * k⁻¹) (k * w * k⁻¹) (k * y * k⁻¹) :=
      isTriangle_conj hC.setup.normal ht
    obtain ⟨hord', hpow'⟩ :=
      orderOf_conj_mul_mul_and_pow_eq (x := x) (w := w) (y := y) (k := k) (n := n) hk
    have hord'' : orderOf (k * x * k⁻¹ * (k * y * k⁻¹) * (k * w * k⁻¹)) = 2 * n :=
      hord'.trans hord
    have hpow'' : (k * x * k⁻¹ * (k * y * k⁻¹) * (k * w * k⁻¹)) ^ n = z := by
      simpa [z] using hpow'
    have hL := setOf_commute_mem_conjOrbit_eq h86 h87 hC hrad hO4 hF hne htri hn hord''
    have hxO : k * x * k⁻¹ ∈ conjOrbit (localGroup D z) x :=
      ⟨k, by simpa [z] using hk, rfl⟩
    have horb : conjOrbit (localGroup D z) (k * x * k⁻¹) = conjOrbit (localGroup D z) x :=
      conjOrbit_eq_of_mem (M := localGroup D z) (u := x) (v := k * x * k⁻¹) hxO
    rw [hpow'', horb] at hL
    simpa [z] using hL

theorem mul_mul_pow_ne_of_mem_conjOrbit (h86 : Lemma8_6) (h87 : Theorem8_7)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hO4 : ¬ O4PairData G D) (hF : FaithfulOnBlocks hC.alpha)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {x w y : G} (ht : IsTriangle D x w y) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) {a a' : G}
    (ha : a ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x)
    (ha' : a' ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x) :
    a * a' * (x * y * w) ^ n ≠ a ∧ a * a' * (x * y * w) ^ n ≠ a' := by
  let z : G := (x * y * w) ^ n
  have hzz : z * z = 1 := by
    simpa [z] using (IsTriangle.third_kind hC.setup.oddT hC.setup.normal ht hn hord).1
  have hzD : z ∉ D := by
    simpa [z] using pow_notMem_of_isTriangle h86 h87 hC hrad hO4 hF hne ht hn hord
  have hxc : x ∈ centSet D z := by
    have hzx : Commute z x :=
      (IsTriangle.third_kind hC.setup.oddT hC.setup.normal ht hn hord).2.2.1
    exact ⟨ht.1, by simpa [z] using hzx.symm⟩
  have hmemD : ∀ r ∈ conjOrbit (localGroup D z) x, r ∈ D := fun r hr =>
    (conjOrbit_subset_centSet hC.setup.normal hxc hr).1
  have haD : a ∈ D := hmemD a (by simpa [z] using ha)
  have ha'D : a' ∈ D := hmemD a' (by simpa [z] using ha')
  have hza : a * a' * z ≠ a := by
    intro h
    have h1 : a' * z = 1 := by
      have := congrArg (fun t => a⁻¹ * t) h
      simpa [mul_assoc] using this
    have h2 : a' = z := by
      calc a' = a' * (z * z) := by rw [hzz, mul_one]
        _ = (a' * z) * z := by group
        _ = z := by rw [h1, one_mul]
    exact hzD (by rwa [h2] at ha'D)
  have hza' : a * a' * z ≠ a' := by
    intro h
    have ha'2 : a' * a' = 1 := hC.setup.oddT.mul_self_eq_one ha'D
    have hzcomm : Commute a' z :=
      (conjOrbit_subset_centSet hC.setup.normal hxc (by simpa [z] using ha')).2
    have h1 : a * z = 1 := by
      have h' := congrArg (fun t => t * a') h
      calc a * z = a * (a' * a') * z := by rw [ha'2, mul_one]
        _ = a * a' * a' * z := by group
        _ = a * a' * z * a' := by
          rw [show a * a' * a' * z = a * (a' * (a' * z)) by group, hzcomm.eq]
          group
        _ = (a * a' * z) * a' := by group
        _ = a' * a' := h'
        _ = 1 := ha'2
    have h2 : a = z := by
      calc a = a * (z * z) := by rw [hzz, mul_one]
        _ = (a * z) * z := by group
        _ = z := by rw [h1, one_mul]
    exact hzD (by rwa [h2] at haD)
  exact ⟨by simpa [z] using hza, by simpa [z] using hza'⟩

theorem ncard_setOf_commute_mem_conjOrbit (h86 : Lemma8_6) (h87 : Theorem8_7)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hO4 : ¬ O4PairData G D) (hF : FaithfulOnBlocks hC.alpha)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {x w y : G} (ht : IsTriangle D x w y) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) {a : G}
    (ha : a ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x) :
    {r | r ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x ∧ Commute r a}.ncard = 3 := by
  obtain ⟨a', ha', hne', -, hset⟩ :=
    exists_setOf_commute_mem_conjOrbit_eq h86 h87 hC hrad hO4 hF hne ht hn hord ha
  rw [hset]
  let z : G := (x * y * w) ^ n
  have hne3 :=
    mul_mul_pow_ne_of_mem_conjOrbit h86 h87 hC hrad hO4 hF hne ht hn hord ha ha'
  have hza : a * a' * z ≠ a := by simpa [z] using hne3.1
  have hza' : a * a' * z ≠ a' := by simpa [z] using hne3.2
  have hnot : a ∉ ({a', a * a' * z} : Set G) := by
    intro h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h
    · exact hne' h.symm
    · exact hza h.symm
  have hnot' : a' ∉ ({a * a' * z} : Set G) := by
    intro h
    simp only [Set.mem_singleton_iff] at h
    exact hza' h.symm
  rw [Set.ncard_insert_of_notMem hnot, Set.ncard_insert_of_notMem hnot',
    Set.ncard_singleton]

theorem commute_iff_of_commute_of_mem_conjOrbit (h86 : Lemma8_6) (h87 : Theorem8_7)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hO4 : ¬ O4PairData G D) (hF : FaithfulOnBlocks hC.alpha)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {x w y : G} (ht : IsTriangle D x w y) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) {a b : G}
    (ha : a ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x)
    (hb : b ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x) (hab : Commute a b) {r : G}
    (hr : r ∈ centSet D ((x * y * w) ^ n)) : Commute r a ↔ Commute r b := by
  obtain ⟨k, hk, rfl⟩ := ha
  set z : G := (x * y * w) ^ n with hzdef
  have htri : IsTriangle D (k * x * k⁻¹) (k * w * k⁻¹) (k * y * k⁻¹) :=
    isTriangle_conj hC.setup.normal ht
  obtain ⟨hord', hpow'⟩ :=
    orderOf_conj_mul_mul_and_pow_eq (x := x) (w := w) (y := y) (k := k) (n := n) hk
  have hord'' : orderOf (k * x * k⁻¹ * (k * y * k⁻¹) * (k * w * k⁻¹)) = 2 * n :=
    hord'.trans hord
  have hpow'' : (k * x * k⁻¹ * (k * y * k⁻¹) * (k * w * k⁻¹)) ^ n = z := by
    simpa [z] using hpow'
  have hL := setOf_commute_mem_conjOrbit_eq h86 h87 hC hrad hO4 hF hne htri hn hord''
  have hxO : k * x * k⁻¹ ∈ conjOrbit (localGroup D z) x :=
    ⟨k, by simpa [z] using hk, rfl⟩
  have horb : conjOrbit (localGroup D z) (k * x * k⁻¹) = conjOrbit (localGroup D z) x :=
    conjOrbit_eq_of_mem (M := localGroup D z) (u := x) (v := k * x * k⁻¹) hxO
  rw [hpow'', horb] at hL
  have hb_set : b ∈ ({k * x * k⁻¹, k * y * k⁻¹, (k * x * k⁻¹) * (k * y * k⁻¹) * z} : Set G) := by
    rw [← hL]
    exact ⟨by simpa [z] using hb, by simpa using hab.symm⟩
  have hr' : r ∈ centSet D ((k * x * k⁻¹ * (k * y * k⁻¹) * (k * w * k⁻¹)) ^ n) := by
    rw [hpow'']
    simpa [z] using hr
  rcases hb_set with hba | hby | hbe
  · simp [hba]
  · have h27 := commute_iff_commute_of_mem_centSet hC.setup htri hn hord'' hr'
    simpa [hby] using h27.1
  · have h27 := commute_iff_commute_of_mem_centSet hC.setup htri hn hord'' hr'
    rw [hbe, ← hpow'']
    exact h27.2

theorem mul_mul_pow_mem_conjOrbit_and_commute (h86 : Lemma8_6) (h87 : Theorem8_7)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hO4 : ¬ O4PairData G D) (hF : FaithfulOnBlocks hC.alpha)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {x w y : G} (ht : IsTriangle D x w y) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) {a a' : G}
    (ha : a ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x)
    (ha' : a' ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x) (hne' : a' ≠ a)
    (hcomm : Commute a a') :
    a * a' * (x * y * w) ^ n ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x ∧
      Commute a (a * a' * (x * y * w) ^ n) := by
  let z : G := (x * y * w) ^ n
  have hthird := IsTriangle.third_kind hC.setup.oddT hC.setup.normal ht hn hord
  have hzz : z * z = 1 := by simpa [z] using hthird.1
  have hzx : Commute z x := by simpa [z] using hthird.2.2.1
  have hxc : x ∈ centSet D z := ⟨ht.1, hzx.symm⟩
  have hcent : ∀ r ∈ conjOrbit (localGroup D z) x, r ∈ centSet D z :=
    fun r hr => conjOrbit_subset_centSet hC.setup.normal hxc hr
  have ha_cent : a ∈ centSet D z := hcent a (by simpa [z] using ha)
  obtain ⟨a0, ha0, -, hcomm0, hset0⟩ :=
    exists_setOf_commute_mem_conjOrbit_eq h86 h87 hC hrad hO4 hF hne ht hn hord ha
  have hset0' : {r | r ∈ conjOrbit (localGroup D z) x ∧ Commute r a} =
      {a, a0, a * a0 * z} := by
    simpa [z] using hset0
  have ha'_set : a' ∈ ({a, a0, a * a0 * z} : Set G) := by
    rw [← hset0']
    exact ⟨by simpa [z] using ha', hcomm.symm⟩
  have hdata : a * a' * z ∈ conjOrbit (localGroup D z) x ∧ Commute a (a * a' * z) := by
    rcases ha'_set with h | h | h
    · exact absurd h hne'
    · have hmem : a * a0 * z ∈ conjOrbit (localGroup D z) x := by
        have h' : a * a0 * z ∈ ({a, a0, a * a0 * z} : Set G) := by simp
        rw [← hset0'] at h'
        exact h'.1
      refine ⟨by rwa [h], ?_⟩
      have hcomm_az : Commute a (a0 * z) := hcomm0.mul_right ha_cent.2
      rw [h]
      simpa [mul_assoc] using (Commute.refl a).mul_right hcomm_az
    · have haD : a ∈ D := (hcent a (by simpa [z] using ha)).1
      have ha2 : a * a = 1 := hC.setup.oddT.mul_self_eq_one haD
      have heq : a * a' * z = a0 := by
        rw [h]
        calc a * (a * a0 * z) * z = (a * a) * a0 * (z * z) := by group
          _ = a0 := by rw [ha2, hzz, one_mul, mul_one]
      refine ⟨by rw [heq]; exact ha0, by rw [heq]; exact hcomm0⟩
  simpa [z] using hdata

theorem isTriangle_of_mem_conjOrbit_of_not_commute (h86 : Lemma8_6) (h87 : Theorem8_7)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hO4 : ¬ O4PairData G D) (hF : FaithfulOnBlocks hC.alpha)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {x w y : G} (ht : IsTriangle D x w y) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) {a a' c : G}
    (ha : a ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x)
    (ha' : a' ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x)
    (hc : c ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x) (haa' : a ≠ a')
    (hcomm : Commute a a') (hac : ¬ Commute a c) : IsTriangle D a c a' := by
  let z : G := (x * y * w) ^ n
  have hthird := IsTriangle.third_kind hC.setup.oddT hC.setup.normal ht hn hord
  have hzx : Commute z x := by simpa [z] using hthird.2.2.1
  have hxc : x ∈ centSet D z := ⟨ht.1, hzx.symm⟩
  have hcent : ∀ r ∈ conjOrbit (localGroup D z) x, r ∈ centSet D z :=
    fun r hr => conjOrbit_subset_centSet hC.setup.normal hxc hr
  have hc_cent : c ∈ centSet D z := hcent c (by simpa [z] using hc)
  have hiff := commute_iff_of_commute_of_mem_conjOrbit h86 h87 hC hrad hO4 hF hne ht hn
    hord ha ha' hcomm hc_cent
  have hc_a : ¬ Commute c a := fun h => hac h.symm
  exact ⟨(hcent a (by simpa [z] using ha)).1, (hcent a' (by simpa [z] using ha')).1,
    (hcent c (by simpa [z] using hc)).1, haa', hcomm, hac,
    fun h => hc_a (hiff.mpr h.symm)⟩

theorem exists_orderOf_and_pow_eq_of_mul_eq (hD : IsOddTransp D) {z e c a a' : G}
    (he : e ∈ D) (hc : c ∈ D) (hzz : z * z = 1) (hz1 : z ≠ 1)
    (hze : Commute z e) (hzc : Commute z c) (hnec : ¬ Commute e c)
    (hfac : a * a' * c = z * (e * c)) :
    ∃ m : ℕ, Odd m ∧ 1 < m ∧ orderOf (a * a' * c) = 2 * m ∧
      (a * a' * c) ^ m = z := by
  let u : G := e * c
  let m : ℕ := orderOf u
  have hm_odd : Odd m := hD.odd_of_not_commute he hc hnec
  have hm1 : 1 < m := by
    have hpos : 0 < m := orderOf_pos u
    have hne1 : m ≠ 1 := by
      intro h1
      have h1' : u = 1 := orderOf_eq_one_iff.mp h1
      have hec_eq : e = c := hD.eq_of_mul_eq_one he h1'
      exact hnec (by simp [hec_eq])
    omega
  have hzu : Commute z u := hze.mul_right hzc
  have hzpow2 : z ^ 2 = 1 := by rw [pow_two]; exact hzz
  have hordz : orderOf z = 2 := orderOf_eq_prime hzpow2 hz1
  have hcop : Nat.Coprime (orderOf z) m := by
    rw [hordz]
    exact Nat.coprime_two_left.mpr hm_odd
  have hordzu : orderOf (z * u) = 2 * m := by
    have h := hzu.orderOf_mul_eq_mul_orderOf_of_coprime hcop
    rw [hordz] at h
    simpa [m] using h
  have hord : orderOf (a * a' * c) = 2 * m := by rw [hfac, hordzu]
  have hpowz : z ^ m = z := by
    obtain ⟨j, hj⟩ := hm_odd
    rw [hj, pow_succ, pow_mul, hzpow2, one_pow, one_mul]
  have hpowu : u ^ m = 1 := by simp [m]
  have hpow : (a * a' * c) ^ m = z := by
    rw [hfac, hzu.mul_pow m, hpowz, hpowu, mul_one]
  exact ⟨m, hm_odd, hm1, hord, hpow⟩

theorem isTriangle_and_pow_eq_of_mem_conjOrbit (h86 : Lemma8_6) (h87 : Theorem8_7)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hO4 : ¬ O4PairData G D) (hF : FaithfulOnBlocks hC.alpha)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {x w y : G} (ht : IsTriangle D x w y) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) {a a' c : G}
    (ha : a ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x)
    (ha' : a' ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x)
    (hc : c ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x) (haa' : a ≠ a')
    (hcomm : Commute a a') (hac : ¬ Commute a c) :
    IsTriangle D a c a' ∧ ∃ m : ℕ, Odd m ∧ 1 < m ∧ orderOf (a * a' * c) = 2 * m ∧
      (a * a' * c) ^ m = (x * y * w) ^ n := by
  classical
  let z : G := (x * y * w) ^ n
  have htri : IsTriangle D a c a' :=
    isTriangle_of_mem_conjOrbit_of_not_commute h86 h87 hC hrad hO4 hF hne ht hn hord
      ha ha' hc haa' hcomm hac
  let e : G := a * a' * z
  have hthird := IsTriangle.third_kind hC.setup.oddT hC.setup.normal ht hn hord
  have hzz : z * z = 1 := by simpa [z] using hthird.1
  have hz1 : z ≠ 1 := by simpa [z] using hthird.2.1
  have hzx : Commute z x := by simpa [z] using hthird.2.2.1
  have hxc : x ∈ centSet D z := ⟨ht.1, hzx.symm⟩
  have hcent : ∀ r ∈ conjOrbit (localGroup D z) x, r ∈ centSet D z :=
    fun r hr => conjOrbit_subset_centSet hC.setup.normal hxc hr
  have hcD : c ∈ D := (hcent c (by simpa [z] using hc)).1
  have hc_cent : c ∈ centSet D z := hcent c (by simpa [z] using hc)
  have he_data :=
    mul_mul_pow_mem_conjOrbit_and_commute h86 h87 hC hrad hO4 hF hne ht hn hord ha ha'
      haa'.symm hcomm
  have he : e ∈ conjOrbit (localGroup D z) x := by simpa [e, z] using he_data.1
  have hcomm_ae : Commute a e := by simpa [e, z] using he_data.2
  have heD : e ∈ D := (hcent e he).1
  have hc_a : ¬ Commute c a := fun h => hac h.symm
  have hiff_ae := commute_iff_of_commute_of_mem_conjOrbit h86 h87 hC hrad hO4 hF hne ht hn
    hord ha he hcomm_ae hc_cent
  have hce : ¬ Commute c e := fun h => hc_a (hiff_ae.mpr h)
  have hec : ¬ Commute e c := fun h => hce h.symm
  have hza : Commute z a := (hcent a (by simpa [z] using ha)).2.symm
  have hza' : Commute z a' := (hcent a' (by simpa [z] using ha')).2.symm
  have hzaa' : Commute z (a * a') := hza.mul_right hza'
  have hfac : a * a' * c = z * (e * c) := by
    dsimp [e]
    calc a * a' * c = (a * a') * (z * z) * c := by rw [hzz, mul_one]
      _ = ((a * a') * z) * z * c := by group
      _ = (z * (a * a')) * z * c := by rw [hzaa'.eq]
      _ = z * ((a * a') * z * c) := by group
  obtain ⟨m, hm_odd, hm1, hord, hpow⟩ :=
    exists_orderOf_and_pow_eq_of_mul_eq hC.setup.oddT heD hcD hzz hz1
      (hcent e he).2.symm hc_cent.2.symm hec hfac
  exact ⟨htri, m, hm_odd, hm1, hord, by simpa [z] using hpow⟩

end CFSG.OddTranspositions.PartThree.EightEight

end
