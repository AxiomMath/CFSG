module

public import CFSG.Adapters.QiuzhenLegacy.Compat.G7.FittingQCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_17iii
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ComponentLayerPerfect
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalizerEqOfNontrivialNormalInCoatom
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

public section

namespace CFSG.Walter

open GorensteinWalter

universe u

variable {G : Type u} [Group G] [Finite G]

private theorem card_primesOfOrder_le_one_of_forall_eq {H : Subgroup G} {p : ℕ}
    (h : ∀ r ∈ primesOfOrder H, r = p) : Nat.card (primesOfOrder H) ≤ 1 := by
  have hset : primesOfOrder H = ↑((Nat.card H).primeFactors) := by
    ext r
    simp [primesOfOrder]
  change (primesOfOrder H).ncard ≤ 1
  exact (Set.ncard_le_one (hs := by rw [hset]; exact Finset.finite_toSet _)).mpr
    fun a ha b hb => (h a ha).trans (h b hb).symm

private theorem eq_of_mem_primesOfOrder_of_isPGroup {H : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hH : IsPGroup p H) {r : ℕ} (hr : r ∈ primesOfOrder H) : r = p := by
  have : Fact p.Prime := ⟨hp⟩
  have hrpf : r ∈ (Nat.card H).primeFactors := hr
  have hrprime : r.Prime := Nat.prime_of_mem_primeFactors hrpf
  obtain ⟨n, hcard⟩ := IsPGroup.iff_card.mp hH
  have hrdvd : r ∣ p ^ n := hcard ▸ Nat.dvd_of_mem_primeFactors hrpf
  exact (Nat.prime_dvd_prime_iff_eq hrprime hp).mp (hrprime.dvd_of_dvd_pow hrdvd)

theorem pResidualOf_generalizedFittingSubgroupOf_ne_bot (A B : Subgroup G)
    (hpi : 2 ≤ Nat.card (primesOfOrder (generalizedFittingSubgroupOf A)) ∨
      2 ≤ Nat.card (primesOfOrder (generalizedFittingSubgroupOf B)))
    (hE : Nat.card (componentLayerOf B) ≤ Nat.card (componentLayerOf A))
    (hO : ∀ q : ℕ, q.Prime → q ∉ primesOfOrder (_root_.CFSG.fittingSubgroupOf A) →
      qCoreOf B q = ⊥)
    {p : ℕ} (hp : p.Prime) :
    pResidualOf (generalizedFittingSubgroupOf A) p ≠ ⊥ := by
  intro hRes
  have hPA : IsPGroup p (generalizedFittingSubgroupOf A) :=
    isPGroup_of_pResidualOf_eq_bot _ p hp hRes
  have hEA : componentLayerOf A = ⊥ := componentLayerOf_eq_bot_of_isPGroup A hp hPA
  have hEB : componentLayerOf B = ⊥ :=
    Subgroup.eq_bot_of_card_le _ (by simpa [hEA] using hE)
  have hFA : ∀ r ∈ primesOfOrder (_root_.CFSG.fittingSubgroupOf A), r = p := fun r hr =>
    eq_of_mem_primesOfOrder_of_isPGroup hp hPA
      (primesOfOrder_subset_of_le (le_sup_left : _root_.CFSG.fittingSubgroupOf A ≤
        generalizedFittingSubgroupOf A) hr)
  have hFB : ∀ r ∈ primesOfOrder (generalizedFittingSubgroupOf B), r = p := by
    intro r hr
    have hrF : r ∈ primesOfOrder (_root_.CFSG.fittingSubgroupOf B) := by
      show r ∈ primesOfOrder (CFSG.GorensteinWalter.fittingSubgroupOf B)
      simpa [generalizedFittingSubgroupOf, hEB] using hr
    have hrprime : r.Prime := Nat.prime_of_mem_primeFactors hrF
    refine hFA r (by_contra fun hrA => ?_)
    exact fstar_qCoreOf_fitting_ne_bot_of_mem_primesOfOrder B r hrprime hrF
      (le_bot_iff.mp ((qCoreOf_fittingSubgroupOf_le_qCoreOf B r hrprime).trans
        (hO r hrprime hrA).le))
  have h1 := card_primesOfOrder_le_one_of_forall_eq
    (fun r hr => eq_of_mem_primesOfOrder_of_isPGroup hp hPA hr)
  have h2 := card_primesOfOrder_le_one_of_forall_eq hFB
  omega

theorem fittingSubgroupOf_le_of_pResidualOf_ne_bot
    (hsimple : IsSimpleGroup G)
    (A : Subgroup G) (hA : IsCoatom A)
    (S : Subgroup G)
    (hSF : S ≤ generalizedFittingSubgroupOf A)
    (hSsub : (S.subgroupOf (generalizedFittingSubgroupOf A)).IsSubnormal)
    (hCS : generalizedFittingSubgroupOf A ⊓ Subgroup.centralizer (S : Set G) ≤ S)
    {B : Subgroup G} (hSB : S ≤ B)
    (hres : ∀ p : ℕ, p.Prime → p ∈ primesOfOrder (_root_.CFSG.fittingSubgroupOf A) →
      pResidualOf (generalizedFittingSubgroupOf A) p ≠ ⊥)
    (hO : ∀ q : ℕ, q.Prime → q ∉ primesOfOrder (_root_.CFSG.fittingSubgroupOf A) →
      qCoreOf B q = ⊥) :
    _root_.CFSG.fittingSubgroupOf B ≤ A := by
  rw [show _root_.CFSG.fittingSubgroupOf B = CFSG.GorensteinWalter.fittingSubgroupOf B from rfl,
    fittingSubgroupOf_eq_iSup_qCoreOf B]
  refine iSup_le fun q => ?_
  have hq : q.1.1.Prime := Nat.prime_of_mem_primeFactors q.1.2
  by_cases hqA : q.1.1 ∈ primesOfOrder (_root_.CFSG.fittingSubgroupOf A)
  · have hRA := pResidualOf_generalizedFitting_isNormalIn A q.1.1
    have hN := normalizer_eq_of_nontrivial_normal_in_coatom hsimple hA hRA.1
      (hres _ hq hqA)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hRA.1).mpr (le_normalizer_of_isNormalIn hRA))
    calc qCoreOf B q.1.1
        ≤ Subgroup.centralizer (pResidualOf (generalizedFittingSubgroupOf A) q.1.1 : Set G) :=
          Subgroup.commutator_eq_bot_iff_le_centralizer.mp
            (bender1970_1_7_ii_commutator_pResidual hsimple A hA S hSF hSsub hCS hSB _ hq hqA)
      _ ≤ Subgroup.normalizer (pResidualOf (generalizedFittingSubgroupOf A) q.1.1 : Set G) :=
          Subgroup.centralizer_le_normalizer _
      _ = A := hN
  · rw [hO _ hq hqA]
    exact bot_le

theorem fittingSubgroupOf_le_centralizer_componentLayerOf
    (hsimple : IsSimpleGroup G)
    (A : Subgroup G) (hA : IsCoatom A)
    (S : Subgroup G)
    (hSF : S ≤ generalizedFittingSubgroupOf A)
    (hSsub : (S.subgroupOf (generalizedFittingSubgroupOf A)).IsSubnormal)
    (hCS : generalizedFittingSubgroupOf A ⊓ Subgroup.centralizer (S : Set G) ≤ S)
    {B : Subgroup G} (hSB : S ≤ B)
    (hO : ∀ q : ℕ, q.Prime → q ∉ primesOfOrder (_root_.CFSG.fittingSubgroupOf A) →
      qCoreOf B q = ⊥) :
    _root_.CFSG.fittingSubgroupOf B ≤ Subgroup.centralizer (componentLayerOf A : Set G) := by
  rw [show _root_.CFSG.fittingSubgroupOf B = CFSG.GorensteinWalter.fittingSubgroupOf B from rfl,
    fittingSubgroupOf_eq_iSup_qCoreOf B]
  refine iSup_le fun q => ?_
  have hq : q.1.1.Prime := Nat.prime_of_mem_primeFactors q.1.2
  by_cases hqA : q.1.1 ∈ primesOfOrder (_root_.CFSG.fittingSubgroupOf A)
  · have hER : componentLayerOf A ≤ pResidualOf (generalizedFittingSubgroupOf A) q.1.1 :=
      perfect_le_pResidualOf_local _ _ _ hq
        (le_sup_right : componentLayerOf A ≤ generalizedFittingSubgroupOf A)
        (componentLayerOf_isPerfect A)
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (bender1970_1_7_ii_commutator_pResidual hsimple A hA S hSF hSsub hCS hSB _ hq hqA)).trans
      (Subgroup.centralizer_le hER)
  · rw [hO _ hq hqA]
    exact bot_le

end CFSG.Walter
