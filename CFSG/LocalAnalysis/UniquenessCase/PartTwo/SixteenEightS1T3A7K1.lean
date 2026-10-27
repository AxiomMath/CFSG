module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralTwoCoverTransfer
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup
open scoped Pointwise commutatorElement

private theorem s16t3_commutatorElement_pow_eq_one {G : Type*} [Group G] (x y : G)
    (hc : ⁅x, y⁆ ∈ center G) {k : ℕ} (hk : x ^ k ∈ center G) : ⁅x, y⁆ ^ k = 1 := by
  have hcomm : Commute x ⁅x, y⁆ := Subgroup.mem_center_iff.1 hc x
  rw [hcomm.commutatorElement_pow_left, commutatorElement_eq_one_iff_mul_comm]
  exact (Subgroup.mem_center_iff.1 hk y).symm

private theorem s16t3_central_pElement {E : Type*} [Group E] [Finite E] {p : ℕ} [hp : Fact p.Prime]
    (hperf : commutator E = ⊤) (Z : Subgroup E) [Z.Normal] (hZ : Z ≤ center E)
    {z : E} (hzZ : z ∈ Z) {n : ℕ} (hz : z ^ p ^ n = 1) :
    (¬ p ^ 2 ∣ Nat.card (E ⧸ Z) → z = 1) ∧ (¬ p ^ 3 ∣ Nat.card (E ⧸ Z) → z ^ p = 1) := by
  classical
  have hpg : IsPGroup p (zpowers z) := by
    rintro ⟨g, m, rfl⟩
    refine ⟨n, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz, one_zpow]
  obtain ⟨P, hzP⟩ := hpg.exists_le_sylow
  have hzP' : z ∈ (P : Subgroup E) := hzP (mem_zpowers z)
  have hzc := CFSG.ProperTwoGeneratedCore.CentralTwoCover.mem_commutator_of_mem_center_of_perfect
    hperf P (hZ hzZ) hzP'
  let f : (P : Subgroup E) →* E ⧸ Z := (QuotientGroup.mk' Z).comp (P : Subgroup E).subtype
  have hpR : IsPGroup p f.range :=
    P.isPGroup'.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  obtain ⟨k, hk⟩ := hpR.exists_card_eq
  have hdvd : p ^ k ∣ Nat.card (E ⧸ Z) := hk ▸ Subgroup.card_subgroup_dvd_card _
  have hker : f.rangeRestrict.ker ≤ center (P : Subgroup E) := by
    intro x hx
    rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker] at hx
    have hxZ : (x : E) ∈ Z := (QuotientGroup.eq_one_iff _).1 hx
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.1 (hZ hxZ) g)
  have hcyc1 : IsCyclic f.range → z = 1 := by
    intro hcyc
    have hPab := commutative_of_cyclic_center_quotient f.rangeRestrict hker
    have hbot : commutator (P : Subgroup E) = ⊥ := by
      rw [_root_.commutator, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a _ b _
      exact hPab b a
    rw [hbot, Subgroup.mem_bot] at hzc
    exact congrArg Subtype.val hzc
  have hk1cyc : k ≤ 1 → IsCyclic f.range := fun hk1 =>
    isCyclic_of_card_dvd_prime (p := p) (hk ▸ by simpa using pow_dvd_pow p hk1)
  refine ⟨fun h2 => hcyc1 (hk1cyc ?_), fun h3 => ?_⟩
  · by_contra hk1
    exact h2 ((pow_dvd_pow p (by omega : 2 ≤ k)).trans hdvd)
  have hk2 : k ≤ 2 := by
    by_contra hk2
    exact h3 ((pow_dvd_pow p (by omega : 3 ≤ k)).trans hdvd)
  by_cases hcyc : IsCyclic f.range
  · rw [hcyc1 hcyc, one_pow]
  have hk2' : k = 2 := by
    by_contra hne
    exact hcyc (hk1cyc (by omega))
  rw [hk2'] at hk
  have hexp : Monoid.exponent f.range = p :=
    (not_isCyclic_iff_exponent_eq_prime hp.out hk).1 hcyc
  have hRab := IsPGroup.commutative_of_card_eq_prime_sq (p := p) hk
  have hpowc : ∀ x : (P : Subgroup E), x ^ p ∈ center (P : Subgroup E) := by
    intro x
    apply hker
    rw [MonoidHom.mem_ker, map_pow]
    have h := Monoid.pow_exponent_eq_one (f.rangeRestrict x)
    rwa [hexp] at h
  have hcommc : ∀ x y : (P : Subgroup E), ⁅x, y⁆ ∈ center (P : Subgroup E) := by
    intro x y
    apply hker
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_def, hRab (f.rangeRestrict x),
      mul_inv_cancel_right, mul_inv_cancel]
  have hP' : ∀ c ∈ commutator (P : Subgroup E), c ∈ center (P : Subgroup E) ∧ c ^ p = 1 := by
    intro c hc
    rw [commutator_eq_closure] at hc
    induction hc using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨a, b, rfl⟩ := hx
      exact ⟨hcommc a b, s16t3_commutatorElement_pow_eq_one a b (hcommc a b) (hpowc a)⟩
    | one => exact ⟨Subgroup.one_mem _, one_pow p⟩
    | mul x y _ _ hx hy =>
      refine ⟨Subgroup.mul_mem _ hx.1 hy.1, ?_⟩
      have hxy : Commute x y := (Subgroup.mem_center_iff.1 hx.1 y).symm
      rw [hxy.mul_pow, hx.2, hy.2, one_mul]
    | inv x _ hx => exact ⟨Subgroup.inv_mem _ hx.1, by rw [inv_pow, hx.2, inv_one]⟩
  exact congrArg Subtype.val (hP' _ hzc).2

private theorem s16t3_eq_one_of_pElement_of_two {Y : Type*} [Group Y] {O : Subgroup Y}
    (hO : IsPGroup 2 ↥O) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {y : Y} (hyO : y ∈ O) {n : ℕ}
    (hy : y ^ p ^ n = 1) : y = 1 := by
  obtain ⟨k, hk⟩ := hO ⟨y, hyO⟩
  have hk' : y ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hcop : Nat.Coprime (p ^ n) (2 ^ k) :=
    Nat.Coprime.pow n k ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  rw [← orderOf_eq_one_iff]
  exact Nat.dvd_one.1 (hcop.gcd_eq_one ▸ Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hy)
    (orderOf_dvd_of_pow_eq_one hk'))

theorem s16t3_kernel_pElement {Y : Type*} [Group Y] [Finite Y] (hperf : commutator Y = ⊤)
    (N O : Subgroup Y) [N.Normal] [O.Normal] (hO : IsPGroup 2 ↥O) (hON : O ≤ N)
    (hcent : N.map (QuotientGroup.mk' O) ≤ center (Y ⧸ O))
    {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {x : Y} (hxN : x ∈ N) {n : ℕ}
    (hx : x ^ p ^ n = 1) :
    (¬ p ^ 2 ∣ Nat.card (Y ⧸ N) → x = 1) ∧ (¬ p ^ 3 ∣ Nat.card (Y ⧸ N) → x ^ p = 1) := by
  have hperf' : commutator (Y ⧸ O) = ⊤ := by
    have h := map_commutator_eq (f := QuotientGroup.mk' O)
    rw [hperf, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective O),
      MonoidHom.range_eq_top.2 (QuotientGroup.mk'_surjective O)] at h
    rw [_root_.commutator, ← h]
  haveI : (N.map (QuotientGroup.mk' O)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective O)
  have hcard : Nat.card ((Y ⧸ O) ⧸ N.map (QuotientGroup.mk' O)) = Nat.card (Y ⧸ N) :=
    Nat.card_congr (QuotientGroup.quotientQuotientEquivQuotient O N hON).toEquiv
  have hzZ : (x : Y ⧸ O) ∈ N.map (QuotientGroup.mk' O) := Subgroup.mem_map_of_mem _ hxN
  have hz : (x : Y ⧸ O) ^ p ^ n = 1 := by rw [← QuotientGroup.mk_pow, hx, QuotientGroup.mk_one]
  obtain ⟨h1, h2⟩ := s16t3_central_pElement hperf' _ hcent hzZ hz
  rw [hcard] at h1 h2
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hxO : x ∈ O := (QuotientGroup.eq_one_iff x).1 (h1 h)
    exact s16t3_eq_one_of_pElement_of_two hO hp.out hp2 hxO hx
  · have hxO : x ^ p ∈ O := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]; exact h2 h
    refine s16t3_eq_one_of_pElement_of_two hO hp.out hp2 hxO (n := n) ?_
    rw [← pow_mul, mul_comm, pow_mul, hx, one_pow]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
