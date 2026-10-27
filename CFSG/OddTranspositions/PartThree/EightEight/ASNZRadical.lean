module

public import CFSG.Foundations.Basic
public import CFSG.GroupTheory.PCore.Defs
public import CFSG.Timmesfeld.Bridge.Asc72Basic
public import CFSG.Timmesfeld.Bridge.OddLocalDefs

import CFSG.GroupTheory.ABGLocalTools.Constraint
import CFSG.OddTranspositions.PartThree.EightEight.KOneRadical
import CFSG.OddTranspositions.PartTwoSec6
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1OpenA7M22Lemma
import CFSG.Timmesfeld.Bridge.Asc72ElemCompQuot
import CFSG.Timmesfeld.Bridge.OddLocalRootCore
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.Timmesfeld.Bridge.Asc72Triangle
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore
public import Certificates.Certificate43
import CFSG.CGT.Timmesfeld75.Statements
import CFSG.CGT.Timmesfeld75.Targets
import CFSG.LocalAnalysis.ComponentClassification.Asc76BenderFacts
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3GoldschmidtFacts
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvUnitary
import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderAutE4Unitary
import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderONan

public section

namespace CFSG.OddTranspositions.PartThree.EightEight

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72

variable {X : Type} [Group X] {E : Set X}

theorem pCore_two_le_center_of_commSet (hS : Setup X E) {s : X} (hs : s ∈ E)
    (hD : ∀ a ∈ commSet E s, ∃ b ∈ commSet E s, ¬ Commute a b) :
    CFSG.pCore 2 X ≤ Subgroup.center X := by
  classical
  intro q hqO
  by_contra hqcent
  obtain ⟨a, ha, hqa⟩ : ∃ a ∈ E, ¬ Commute q a := by
    by_contra h
    push Not at h
    exact hqcent (CFSG.Timmesfeld.Bridge.OddLocal.mem_center_of_commute_gen hS.gen h)
  obtain ⟨hcomm, hbE, hbne, habO⟩ :=
    commute_conj_and_mul_mem_pCore_of_not_commute hS hqO ha hqa
  have hN := CFSG.pCore_normal (p := 2) (G := X)
  obtain ⟨g, hg⟩ := isConj_iff.mp (hS.isConj ha hs)
  set x' : X := g * (q * a * q⁻¹) * g⁻¹ with hx'
  have hsx' : Commute s x' := by
    rw [← hg]
    exact hcomm.conj g
  have hx's : x' ≠ s := by
    intro h
    apply hbne
    rw [hx', ← hg] at h
    simpa [mul_assoc] using congrArg (fun t => g⁻¹ * t * g) h
  have hx'Δ : x' ∈ commSet E s := ⟨hS.conj_mem g hbE, hsx'.symm, hx's⟩
  have hsx'O : s * x' ∈ CFSG.pCore 2 X := by
    have h := hN.conj_mem _ habO g
    have heq : g * (a * (q * a * q⁻¹)) * g⁻¹ = s * x' := by
      rw [hx', ← hg]
      group
    rwa [heq] at h
  obtain ⟨b, hbΔ, hx'b⟩ := hD x' hx'Δ
  have hbinv : b⁻¹ = b := hS.oddT.inv_eq hbΔ.1
  have hs2 : s * s = 1 := hS.oddT.mul_self_eq_one hs
  have hsq : (x' * b) ^ 2 ∈ CFSG.pCore 2 X := by
    have h := (CFSG.pCore 2 X).mul_mem hsx'O (hN.conj_mem _ hsx'O b)
    have heq : s * x' * (b * (s * x') * b⁻¹) = (x' * b) ^ 2 := by
      rw [hbinv]
      calc s * x' * (b * (s * x') * b) = s * x' * (b * s * x' * b) := by group
        _ = s * x' * (s * b * x' * b) := by rw [hbΔ.2.1.eq]
        _ = s * (x' * s) * b * x' * b := by group
        _ = s * (s * x') * b * x' * b := by rw [hsx'.eq]
        _ = s * s * x' * b * x' * b := by group
        _ = (x' * b) ^ 2 := by rw [hs2, one_mul, pow_two]; group
    rwa [heq] at h
  have hodd : Odd (orderOf (x' * b)) := hS.oddT.odd_of_not_commute hx'Δ.1 hbΔ.1 hx'b
  have h1 : (x' * b) ^ 2 = 1 :=
    CFSG.RankThree.PartTwo.Sec15.eq_one_of_mem_of_odd_orderOf'
      (CFSG.pCore_isPGroup (p := 2) (G := X)) hsq (hodd.of_dvd_nat (orderOf_pow_dvd 2))
  have h2 : orderOf (x' * b) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h1) with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  exact hx'b (by rw [hS.oddT.eq_of_mul_eq_one hx'Δ.1 (orderOf_eq_one_iff.mp h2)])

theorem normal_le_center_of_commSet (hS : Setup X E) {s τ : X} (hs : s ∈ E)
    (hτ : τ ∈ Subgroup.center X) (hsτ : s * τ ∈ Subgroup.closure (commSet E s))
    {N : Subgroup X} (hN : N.Normal) (hNo : Odd (Nat.card N)) :
    N ≤ Subgroup.center X := by
  have hsinv : s⁻¹ = s := hS.oddT.inv_eq hs
  have hNs : ∀ n ∈ N, Commute n s := by
    intro n hn
    have hwE : n * s * n⁻¹ ∈ E := hS.conj_mem n hs
    have hn' : n * s * n⁻¹ * s⁻¹ ∈ N := by
      have h := N.mul_mem hn (hN.conj_mem n⁻¹ (N.inv_mem hn) s)
      rwa [show n * (s * n⁻¹ * s⁻¹) = n * s * n⁻¹ * s⁻¹ by group] at h
    have hcw : commSet E (n * s * n⁻¹) = commSet E s :=
      commSet_eq_of_mem_mul_normal hS.oddT hN hNo hs hwE hn' (by group)
    have hle : Subgroup.closure (commSet E s) ≤ Subgroup.centralizer {n * s * n⁻¹} := by
      rw [← hcw]
      exact (Subgroup.closure_le _).mpr fun e he =>
        Subgroup.mem_centralizer_singleton_iff.mpr he.2.1.eq
    have hsτw : Commute (s * τ) (n * s * n⁻¹) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hle hsτ)
    have hτw : Commute τ⁻¹ (n * s * n⁻¹) :=
      (show Commute τ (n * s * n⁻¹) from (Subgroup.mem_center_iff.mp hτ _).symm).inv_left
    have hsw : Commute s (n * s * n⁻¹) := by
      simpa using hsτw.mul_left hτw
    have hswN : s * (n * s * n⁻¹) ∈ N := by
      have h := N.mul_mem (hN.conj_mem n hn s) (N.inv_mem hn)
      rwa [hsinv, show s * n * s * n⁻¹ = s * (n * s * n⁻¹) by group] at h
    have hsq : (s * (n * s * n⁻¹)) ^ 2 = 1 := by
      rw [pow_two, hsw.symm.mul_mul_mul_comm, hS.oddT.mul_self_eq_one hs,
        hS.oddT.mul_self_eq_one hwE, one_mul]
    have h1 : orderOf (s * (n * s * n⁻¹)) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hsq) with h | h
      · exact h
      · exact absurd (h ▸ Subgroup.orderOf_dvd_natCard N hswN)
          (Nat.not_even_iff_odd.mpr hNo ∘ even_iff_two_dvd.mpr)
    have hw : s = n * s * n⁻¹ := hS.oddT.eq_of_mul_eq_one hs (orderOf_eq_one_iff.mp h1)
    calc n * s = n * s * n⁻¹ * n := by group
      _ = s * n := by rw [← hw]
  intro n hn
  refine CFSG.Timmesfeld.Bridge.OddLocal.mem_center_of_commute_gen hS.gen fun e he => ?_
  obtain ⟨g, rfl⟩ := isConj_iff.mp (hS.isConj hs he)
  have h := (hNs _ (by simpa using hN.conj_mem n hn g⁻¹)).conj g
  simpa [mul_assoc] using h

theorem solvableRadical_eq_center_of_commSet [Finite X] (hS : Setup X E) {s τ : X} (hs : s ∈ E)
    (hτ : τ ∈ Subgroup.center X) (hsτ : s * τ ∈ Subgroup.closure (commSet E s))
    (hD : ∀ a ∈ commSet E s, ∃ b ∈ commSet E s, ¬ Commute a b) :
    CFSG.solvableRadical X = Subgroup.center X :=
  le_antisymm (otg2_solvableRadical_le_center (pCore_two_le_center_of_commSet hS hs hD)
    (normal_le_center_of_commSet hS hs hτ hsτ (CFSG.oddCore_normal X)
      CFSG.ABGLocalTools.odd_card_oddCore)) otg2_center_le_solvableRadical

end CFSG.OddTranspositions.PartThree.EightEight

end
