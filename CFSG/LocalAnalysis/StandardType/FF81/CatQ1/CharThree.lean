module

public import CFSG.Open.StatedDefs
import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersLie
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.OrderReductions.OddInversion
import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
import CFSG.GroupTheory.LocalCores.Fitting
import CFSG.LieType.Chevalley.RootCommutator
import CFSG.LieType.Steinberg.Classical.SpinFrame
import CFSG.LieType.Steinberg.Exceptional.E6E7
import CFSG.LieType.Steinberg.Families
import CFSG.LieType.Steinberg.G2
import CFSG.LieType.Universal.Spin.Generation
import CFSG.LieType.Universal.Spin.OddCT
import CFSG.LieType.Universal.Spin.PlusCT
import CFSG.LieType.Universal.Spin.Structure
import CFSG.LieType.Universal.SpinOmega
import CFSG.LieType.Universal.Unitary
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
import CFSG.LocalAnalysis.SectionRank.SporadicCover
import CFSG.Sporadic.M23.M23Group
import CFSG.Sporadic.Th.F2Spec
import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.StandardType.FF81.CatQ1

open CFSG.Open
open CFSG.EvenSmallLie.CatalogOrders

private theorem lieMin_le_of_admissible {t : StatedLieTag} {n p f : ℕ}
    (h : StatedLieAdmissible t n p f) : lieMin t ≤ n := by
  cases t <;> simp only [StatedLieAdmissible, lieMin] at h ⊢ <;> omega

theorem twentySeven_dvd_card_of_charThree {K : Type} [Group K] {t : StatedLieTag} {n f : ℕ}
    (h : StatedClassicalModel K t n 3 f) (hn : t = .PSL → 3 ≤ n) : 27 ∣ Nat.card K := by
  have hcard : Nat.card K = lieOrd t n (3 ^ f) := card_eq_lieOrd_of_classical h
  have hmin : lieMin t ≤ n := lieMin_le_of_admissible h.1
  have hf : 1 ≤ f := h.1.2.1
  have hexp : 3 ≤ lieExp t n := by
    cases t
    ·
      have hn3 : 3 ≤ n := hn rfl
      simp only [lieExp]
      rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
      have h2 : 2 ≤ n - 1 := by omega
      have h6 : 2 * 3 ≤ (n - 1) * n := Nat.mul_le_mul h2 hn3
      omega
    ·
      have hn3 : 3 ≤ n := h.1.2.2.1
      simp only [lieExp]
      rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
      have h2 : 2 ≤ n - 1 := by omega
      have h6 : 2 * 3 ≤ (n - 1) * n := Nat.mul_le_mul h2 hn3
      omega
    ·
      have hn2 : 2 ≤ n := h.1.2.2.1
      simp only [lieExp]
      have h4 : 2 * 2 ≤ n * n := Nat.mul_le_mul hn2 hn2
      omega
    ·
      have hn3 : 3 ≤ n := h.1.2.2.1
      simp only [lieExp]
      have h9 : 3 * 3 ≤ n * n := Nat.mul_le_mul hn3 hn3
      omega
    ·
      have hn4 : 4 ≤ n := h.1.2.2
      simp only [lieExp]
      have h3 : 3 ≤ n - 1 := by omega
      have h12 : 4 * 3 ≤ n * (n - 1) := Nat.mul_le_mul hn4 h3
      omega
    ·
      have hn4 : 4 ≤ n := h.1.2.2
      simp only [lieExp]
      have h3 : 3 ≤ n - 1 := by omega
      have h12 : 4 * 3 ≤ n * (n - 1) := Nat.mul_le_mul hn4 h3
      omega
    all_goals exfalso; exact h.2
  have hdvd : (3 ^ f) ^ lieExp t n ∣ Nat.card K := by
    rw [hcard]
    exact pow_lieExp_dvd hmin (3 ^ f)
  have hpow : 3 ^ (f * lieExp t n) = (3 ^ f) ^ lieExp t n := by rw [pow_mul]
  have hmul : 3 ≤ f * lieExp t n := by
    have := Nat.mul_le_mul hf hexp
    omega
  have h27 : 3 ^ 3 ∣ 3 ^ (f * lieExp t n) := Nat.pow_dvd_pow 3 hmul
  rw [show (3 : ℕ) ^ 3 = 27 by norm_num, hpow] at h27
  exact h27.trans hdvd

end CFSG.StandardType.FF81.CatQ1
