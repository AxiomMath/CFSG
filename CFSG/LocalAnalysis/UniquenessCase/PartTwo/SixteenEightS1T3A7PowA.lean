module

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
public import Mathlib.GroupTheory.Transfer
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

theorem s16t3_pow_three_of_central {Q : Type*} [Group Q] [Finite Q] (Z : Subgroup Q) [Z.Normal]
    (hZc : Z ≤ center Q) (hZ3 : ∀ z ∈ Z, ∀ n : ℕ, z ^ 3 ^ n = 1 → z ^ 3 = 1)
    (hperf : commutator (Q ⧸ Z) = ⊤) (h9 : ¬ 9 ∣ Nat.card (Q ⧸ Z)) {u : Q} {n : ℕ}
    (hu : u ^ 3 ^ n = 1) : u ^ 3 = 1 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hu3Z : u ^ 3 ∈ Z := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    set ū : Q ⧸ Z := (u : Q ⧸ Z)
    have h1 : ū ^ 3 ^ n = 1 := by rw [← QuotientGroup.mk_pow, hu, QuotientGroup.mk_one]
    obtain ⟨k, hk, hok⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one h1)
    have hdvd : orderOf ū ∣ Nat.card (Q ⧸ Z) := orderOf_dvd_natCard ū
    have hk1 : k ≤ 1 := by
      by_contra hk1
      exact h9 ((pow_dvd_pow 3 (by omega : 2 ≤ k)).trans (hok ▸ hdvd))
    rw [← orderOf_dvd_iff_pow_eq_one, hok]
    simpa using pow_dvd_pow 3 hk1
  have hpg : IsPGroup 3 (zpowers u) := by
    rintro ⟨g, m, rfl⟩
    refine ⟨n, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu, one_zpow]
  obtain ⟨P, huP⟩ := hpg.exists_le_sylow
  have huP' : u ∈ (P : Subgroup Q) := huP (mem_zpowers u)
  let f : (P : Subgroup Q) →* Q ⧸ Z := (QuotientGroup.mk' Z).comp (P : Subgroup Q).subtype
  have hcyc : IsCyclic f.range := by
    have hp3 : IsPGroup 3 f.range := P.isPGroup'.of_surjective f.rangeRestrict
      f.rangeRestrict_surjective
    obtain ⟨k, hk⟩ := hp3.exists_card_eq
    have hdvd : Nat.card f.range ∣ Nat.card (Q ⧸ Z) := Subgroup.card_subgroup_dvd_card _
    have hk1 : k ≤ 1 := by
      by_contra hk1
      exact h9 ((pow_dvd_pow 3 (by omega : 2 ≤ k)).trans (hk ▸ hdvd))
    exact isCyclic_of_card_dvd_prime (p := 3) (hk ▸ by simpa using pow_dvd_pow 3 hk1)
  have hker : f.rangeRestrict.ker ≤ center (P : Subgroup Q) := by
    intro x hx
    rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker] at hx
    have hxZ : (x : Q) ∈ Z := (QuotientGroup.eq_one_iff _).1 hx
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.1 (hZc hxZ) g)
  have hPab : ∀ a b : (P : Subgroup Q), a * b = b * a :=
    commutative_of_cyclic_center_quotient f.rangeRestrict hker
  haveI : (P : Subgroup Q).FiniteIndex := Subgroup.finiteIndex_of_finite
  let ϕ : (P : Subgroup Q) →* Abelianization (P : Subgroup Q) := Abelianization.of
  have hϕinj : Function.Injective ϕ := by
    rw [← MonoidHom.ker_eq_bot_iff, Abelianization.ker_of, _root_.commutator,
      Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a _ b _
    exact hPab b a
  have hkey : ∀ z ∈ Z, ∀ (k : ℕ) (g₀ : Q), g₀⁻¹ * z ^ k * g₀ ∈ (P : Subgroup Q) →
      g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro z hz k g₀ _
    have hzk : z ^ k ∈ center Q := Subgroup.pow_mem _ (hZc hz) k
    rw [mul_assoc, ← (Subgroup.mem_center_iff.1 hzk g₀), ← mul_assoc, inv_mul_cancel, one_mul]
  have hmap : (commutator Q).map (QuotientGroup.mk' Z) = ⊤ := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.2 (QuotientGroup.mk'_surjective Z),
      ← _root_.commutator, hperf]
  obtain ⟨c, hc, hcu⟩ : ∃ c ∈ commutator Q, (QuotientGroup.mk' Z) c = (u : Q ⧸ Z) := by
    have : (u : Q ⧸ Z) ∈ (commutator Q).map (QuotientGroup.mk' Z) := hmap ▸ Subgroup.mem_top _
    exact this
  set z' := c⁻¹ * u with hz'
  have hz'Z : z' ∈ Z := by
    rw [hz', ← QuotientGroup.eq]; exact hcu
  have hVc : ϕ.transfer c = 1 := Abelianization.commutator_subset_ker (ϕ.transfer) hc
  have hVu : ϕ.transfer u = ϕ.transfer z' := by
    rw [hz', map_mul, map_inv, hVc, inv_one, one_mul]
  have hz'P : z' ^ (P : Subgroup Q).index ∈ (P : Subgroup Q) :=
    MonoidHom.transfer_eq_pow_aux z' (hkey z' hz'Z)
  rw [MonoidHom.transfer_eq_pow ϕ z' (hkey z' hz'Z)] at hVu
  have hz3 : (z' ^ (P : Subgroup Q).index) ^ 3 = 1 := by
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨_, hz'P⟩
    exact hZ3 _ (Subgroup.pow_mem _ hz'Z _) k (congrArg Subtype.val hk)
  have hVu3 : ϕ.transfer (u ^ 3) = 1 := by
    rw [map_pow, hVu, ← map_pow]
    have : (⟨z' ^ (P : Subgroup Q).index, hz'P⟩ : (P : Subgroup Q)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hz3)
    rw [this, map_one]
  have hu3P : (u ^ 3) ^ (P : Subgroup Q).index ∈ (P : Subgroup Q) :=
    MonoidHom.transfer_eq_pow_aux (u ^ 3) (hkey _ hu3Z)
  rw [MonoidHom.transfer_eq_pow ϕ (u ^ 3) (hkey _ hu3Z)] at hVu3
  have hidx : (u ^ 3) ^ (P : Subgroup Q).index = 1 :=
    congrArg Subtype.val (hϕinj (hVu3.trans (map_one ϕ).symm))
  have h3n : (u ^ 3) ^ 3 ^ n = 1 := by rw [← pow_mul, mul_comm, pow_mul, hu, one_pow]
  have hcop : Nat.Coprime (3 ^ n) (P : Subgroup Q).index :=
    Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 P.not_dvd_index)
  rw [← orderOf_eq_one_iff]
  exact Nat.dvd_one.1 (hcop.gcd_eq_one ▸ Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3n)
    (orderOf_dvd_of_pow_eq_one hidx))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
