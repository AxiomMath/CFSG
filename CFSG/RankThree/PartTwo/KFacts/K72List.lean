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
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.RankThree.PartTwo.KFacts

theorem exists_mem_centralizer_orderOf_eq {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {A L : Subgroup G} (hA : IsPGroup p A)
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) (hpL : p ∣ Nat.card L) :
    ∃ x ∈ L ⊓ Subgroup.centralizer (A : Set G), orderOf x = p := by
  let φ : A →* MulAut L := L.normalizerMonoidHom.comp (Subgroup.inclusion hAN)
  let _ : MulAction A L := MulAction.compHom L φ
  have hfix := hA.card_modEq_card_fixedPoints L
  set C := L ⊓ Subgroup.centralizer (A : Set G) with hC
  have hmem : ∀ l : L, l ∈ MulAction.fixedPoints A L ↔ (l : G) ∈ C := by
    intro l
    constructor
    · intro hl
      refine ⟨l.2, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
      have h1 : ((⟨g, hg⟩ : A) • l : L) = l := hl ⟨g, hg⟩
      have h2 : g * l * g⁻¹ = l := congrArg Subtype.val h1
      calc g * l = g * l * g⁻¹ * g := by group
        _ = l * g := by rw [h2]
    · intro hl a
      apply Subtype.ext
      show (a : G) * l * (a : G)⁻¹ = l
      rw [Subgroup.mem_centralizer_iff.mp hl.2 a a.2, mul_inv_cancel_right]
  have hcard : Nat.card (MulAction.fixedPoints A L) = Nat.card C :=
    Nat.card_congr ⟨fun l => ⟨l.1, (hmem l.1).mp l.2⟩,
      fun g => ⟨⟨g.1, g.2.1⟩, (hmem ⟨g.1, g.2.1⟩).mpr g.2⟩, fun _ => rfl, fun _ => rfl⟩
  have hpC : p ∣ Nat.card C := by
    rw [← hcard]
    exact Nat.modEq_zero_iff_dvd.mp (hfix.symm.trans (Nat.modEq_zero_iff_dvd.mpr hpL))
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpC
  exact ⟨x, x.2, by rw [Subgroup.orderOf_coe, hx]⟩

theorem card_le_of_isCyclic_sylow {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (hX : ∀ Q : Sylow p X, IsCyclic Q) {E : Subgroup X} (hE : ∀ x ∈ E, x ^ p = 1) :
    Nat.card E ≤ p := by
  have hEp : IsPGroup p E := fun x => ⟨1, Subtype.ext (by simpa using hE x x.2)⟩
  obtain ⟨Q, hEQ⟩ := hEp.exists_le_sylow
  have := hX Q
  have hEc : IsCyclic E :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hEQ).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hEQ).surjective
  obtain ⟨g, hg⟩ := hEc.exists_generator
  rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
  have hg1 : g ^ p = 1 := Subtype.ext (by simpa using hE g g.2)
  exact Nat.le_of_dvd (Fact.out : p.Prime).pos (orderOf_dvd_of_pow_eq_one hg1)

theorem eq_one_of_mem_center_of_isCyclic_sylow {X : Type*} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] (hperf : commutator X = ⊤) (hX : ∀ Q : Sylow p X, IsCyclic Q) {z : X}
    (hz : z ∈ Subgroup.center X) (hzp : z ^ p = 1) : z = 1 := by
  by_contra hz1
  have hord : orderOf z = p := orderOf_eq_prime hzp hz1
  have hzP : IsPGroup p (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  obtain ⟨Q, hzQ⟩ := hzP.exists_le_sylow
  have := hX Q
  let _ : CommGroup Q := IsCyclic.commGroup
  have key : ∀ (k : ℕ) (g₀ : X), g₀⁻¹ * z ^ k * g₀ ∈ (Q : Subgroup X) →
      g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    have hzk := Subgroup.mem_center_iff.mp (Subgroup.pow_mem _ hz k) g₀
    rw [mul_assoc, ← hzk, ← mul_assoc, inv_mul_cancel, one_mul]
  have h1 := MonoidHom.transfer_eq_pow (MonoidHom.id Q) z key
  have h2 : MonoidHom.transfer (MonoidHom.id Q) z = 1 := by
    have hz' : z ∈ commutator X := by
      rw [hperf]
      exact Subgroup.mem_top z
    exact Abelianization.commutator_subset_ker _ hz'
  rw [h2] at h1
  have h3 : z ^ (Q : Subgroup X).index = 1 := by
    have := congrArg Subtype.val h1
    simpa using this.symm
  apply Q.not_dvd_index
  have h4 := orderOf_dvd_of_pow_eq_one h3
  rwa [hord] at h4

theorem exists_orderOf_eq_three_psl2 (K : Type*) [Field K] :
    ∃ x : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K, orderOf x = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let M : Matrix.SpecialLinearGroup (Fin 2) K := ⟨!![0, -1; 1, -1], by simp [Matrix.det_fin_two]⟩
  have hM3 : M ^ 3 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
    show (!![0, -1; 1, -1] : Matrix (Fin 2) (Fin 2) K) ^ 3 = 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two]
  have hM1 : (M : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) ≠ 1 := by
    intro h
    rw [QuotientGroup.eq_one_iff, Matrix.SpecialLinearGroup.mem_center_iff] at h
    obtain ⟨r, -, hr⟩ := h
    have := congrArg (fun A : Matrix (Fin 2) (Fin 2) K => A 0 1) hr
    simp [M] at this
  refine ⟨M, orderOf_eq_prime ?_ hM1⟩
  rw [← QuotientGroup.mk_pow, hM3, QuotientGroup.mk_one]

theorem three_dvd_card_psl2 (K : Type*) [Field K] [Finite K] :
    3 ∣ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) := by
  obtain ⟨x, hx⟩ := exists_orderOf_eq_three_psl2 K
  rw [← hx]
  exact orderOf_dvd_natCard x

theorem three_ne_zero_galoisField {p : ℕ} [Fact p.Prime] (hp : p ≠ 3) (n : ℕ) :
    (3 : GaloisField p n) ≠ 0 := by
  intro h
  have h1 : ((3 : ℕ) : GaloisField p n) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff (GaloisField p n) p] at h1
  exact hp ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_three).mp h1)

end CFSG.RankThree.PartTwo.KFacts
