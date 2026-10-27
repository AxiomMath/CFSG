module

public import CFSG.Timmesfeld.Bridge.Asc72Basic

import CFSG.OddTranspositions.WidthOne
import CFSG.GroupTheory.ABGLocalTools.Constraint
import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureInvertedHullOddCore
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore
public import Certificates.Certificate43
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureConjugation
import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureInvertedHullData
import CFSG.StronglyEmbedded.ParityCriterion
import CFSG.Timmesfeld.Bridge.Asc72Width

public section

namespace CFSG.OddTranspositions.PartThree.EightEight

open CFSG.Timmesfeld.Bridge.Asc72

@[expose] def commProd {X : Type*} [Group X] (E : Set X) : Subgroup X :=
  Subgroup.closure {g | ∃ x ∈ E, ∃ y ∈ E, Commute x y ∧ x * y = g}

theorem mul_mem_commProd {X : Type*} [Group X] {E : Set X} {x y : X} (hx : x ∈ E)
    (hy : y ∈ E) (hxy : Commute x y) : x * y ∈ commProd E :=
  Subgroup.subset_closure ⟨x, hx, y, hy, hxy, rfl⟩

theorem commProd_normal {X : Type*} [Group X] {E : Set X}
    (hN : CFSG.Timmesfeld.Connectivity.IsNormalSet E) : (commProd E).Normal := by
  refine Subgroup.Normal.mk fun n hn g => ?_
  have hgen : ∀ s ∈ {g | ∃ x ∈ E, ∃ y ∈ E, Commute x y ∧ x * y = g},
      g * s * g⁻¹ ∈ {g | ∃ x ∈ E, ∃ y ∈ E, Commute x y ∧ x * y = g} := by
    rintro _ ⟨x, hx, y, hy, hc, rfl⟩
    exact ⟨g * x * g⁻¹, hN g x hx, g * y * g⁻¹, hN g y hy, hc.conj g, by group⟩
  have hmap : (commProd E).map (MulAut.conj g).toMonoidHom ≤ commProd E := by
    rw [commProd, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨s, hs, rfl⟩
    simpa [MulAut.conj_apply] using Subgroup.subset_closure (hgen s hs)
  simpa [MulAut.conj_apply] using
    hmap (Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hn)

theorem mk_eq_mk_of_commute_of_commProd_le {X : Type*} [Group X] [Finite X] {E : Set X}
    (hD : IsOddTransp E) {N : Subgroup X} [N.Normal] (hN : commProd E ≤ N) {x y : X}
    (hx : x ∈ E) (hy : y ∈ E)
    (hxy : Commute (QuotientGroup.mk' N x) (QuotientGroup.mk' N y)) :
    QuotientGroup.mk' N x = QuotientGroup.mk' N y := by
  let a := QuotientGroup.mk' N x
  let b := QuotientGroup.mk' N y
  have ha : a * a = 1 := by
    rw [show a * a = QuotientGroup.mk' N (x * x) by rw [map_mul],
      hD.mul_self_eq_one hx, map_one]
  have hb : b * b = 1 := by
    rw [show b * b = QuotientGroup.mk' N (y * y) by rw [map_mul],
      hD.mul_self_eq_one hy, map_one]
  have hab : a * b = 1 := by
    by_cases hc : Commute x y
    · have hmem : x * y ∈ N := hN (mul_mem_commProd hx hy hc)
      rw [show a * b = QuotientGroup.mk' N (x * y) by rw [map_mul],
        QuotientGroup.mk'_apply]
      exact (QuotientGroup.eq_one_iff (N := N) (x * y)).mpr hmem
    · have hodd : Odd (orderOf (x * y)) := hD.odd_of_not_commute hx hy hc
      have hsq : (a * b) ^ 2 = 1 := by
        rw [hxy.mul_pow, pow_two a, pow_two b, ha, hb, one_mul]
      have hodd' : Odd (orderOf (a * b)) := by
        rw [show a * b = QuotientGroup.mk' N (x * y) by rw [map_mul]]
        exact Odd.of_dvd_nat hodd (orderOf_map_dvd _ _)
      have hdvd : orderOf (a * b) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact orderOf_eq_one_iff.mp h
      · rw [h] at hodd'
        exact absurd hodd' (by decide)
  calc a = a * 1 := (mul_one a).symm
    _ = a * (b * b) := by rw [hb]
    _ = (a * b) * b := by rw [mul_assoc]
    _ = b := by rw [hab, one_mul]

end CFSG.OddTranspositions.PartThree.EightEight
