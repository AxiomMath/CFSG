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
public import Mathlib.GroupTheory.GroupAction.CardCommute
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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

namespace CFSG.RankThree.PartTwo.Sec8.HeringBMem

theorem eight_dvd_card_of_free {M Ω : Type*} [Group M] [Fintype Ω] [DecidableEq Ω]
    (ρ : M →* Equiv.Perm Ω) {Q : Subgroup M} (hQ : Nat.card Q = 8) {z : M}
    (hq : ∀ x ∈ Q, x ≠ 1 → x = z ∨ x ^ 2 = z)
    (S : Finset Ω) (hS : ∀ q ∈ Q, ∀ ω ∈ S, ρ q ω ∈ S) (hfree : ∀ ω ∈ S, ρ z ω ≠ ω) :
    8 ∣ S.card := by
  classical
  letI act : MulAction Q S :=
    { smul := fun g s => ⟨ρ (g : M) (s : Ω), hS (g : M) g.2 s s.2⟩
      one_smul := fun s => Subtype.ext (by
        show ρ ((1 : Q) : M) (s : Ω) = (s : Ω)
        simp)
      mul_smul := fun g h s => Subtype.ext (by
        show ρ ((g * h : Q) : M) (s : Ω) = ρ (g : M) (ρ (h : M) (s : Ω))
        simp [Equiv.Perm.mul_apply]) }
  have hfixed : ∀ (s : S) (g : Q), g • s = s → g = 1 := by
    intro s g hg
    by_contra hg1
    have hgM : (g : M) ≠ 1 := fun h => hg1 (Subtype.ext h)
    have hfix : ρ (g : M) (s : Ω) = s := congrArg Subtype.val hg
    rcases hq (g : M) g.2 hgM with h | h
    · apply hfree (s : Ω) s.2
      rw [← h]
      exact hfix
    · apply hfree (s : Ω) s.2
      rw [← h, pow_two, map_mul, Equiv.Perm.mul_apply, hfix, hfix]
  have hQfin : Finite Q := Nat.finite_of_card_ne_zero (by rw [hQ]; norm_num)
  letI : Fintype Q := Fintype.ofFinite Q
  have hQcard : Fintype.card Q = 8 := by rw [← Nat.card_eq_fintype_card, hQ]
  letI : ∀ s : S, Fintype (MulAction.stabilizer Q s) := fun s => Fintype.ofFinite _
  letI : Fintype (Quotient (MulAction.orbitRel Q S)) := Fintype.ofFinite _
  have hstab : ∀ s : S, Fintype.card (MulAction.stabilizer Q s) = 1 := by
    intro s
    rw [← Nat.card_eq_fintype_card, Subgroup.card_eq_one]
    ext g
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_bot]
    exact ⟨hfixed s g, fun h => by rw [h, one_smul]⟩
  have key := MulAction.card_eq_sum_card_group_div_card_stabilizer Q S
  have hterm : ∀ ω : Quotient (MulAction.orbitRel Q S),
      Fintype.card Q / Fintype.card (MulAction.stabilizer Q ω.out) = 8 := by
    intro ω
    rw [hstab ω.out, hQcard, Nat.div_one]
  rw [Fintype.card_coe] at key
  rw [key]
  simp only [hterm, Finset.sum_const, smul_eq_mul]
  exact dvd_mul_left _ _

theorem quat_z_central {M : Type*} [Group M] {Q : Subgroup M} (hQ : Nat.card Q = 8) {z : M}
    (hzQ : z ∈ Q) (hz1 : z ≠ 1) (hq : ∀ x ∈ Q, x ≠ 1 → x = z ∨ x ^ 2 = z) :
    z ^ 2 = 1 ∧ ∀ x ∈ Q, x * z = z * x := by
  have h8 : ∀ g ∈ Q, g ^ 8 = 1 := by
    intro g hg
    have h := pow_card_eq_one' (G := ↥Q) (x := (⟨g, hg⟩ : Q))
    rw [hQ] at h
    simpa using congrArg Subtype.val h
  have hz8 : z ^ 8 = 1 := h8 z hzQ
  have hz2 : z ^ 2 = 1 := by
    by_contra hne
    rcases hq (z ^ 2) (pow_mem hzQ 2) hne with h | h
    ·
      apply hz1
      have h' : z * z = z * 1 := by rw [mul_one, ← pow_two, h]
      exact mul_left_cancel h'
    ·
      have h4 : z ^ 3 * z = 1 * z :=
        calc z ^ 3 * z = (z ^ 2) ^ 2 := by group
          _ = z := h
          _ = 1 * z := (one_mul z).symm
      have h3 : z ^ 3 = 1 := mul_right_cancel h4
      have h28 : z ^ 2 = z ^ 8 :=
        calc z ^ 2 = (z ^ 3) ^ 2 * z ^ 2 := by rw [h3, one_pow, one_mul]
          _ = z ^ 8 := by group
      exact hne (h28.trans hz8)
  refine ⟨hz2, fun x hx => ?_⟩
  have hwQ : x * z * x⁻¹ ∈ Q := mul_mem (mul_mem hx hzQ) (inv_mem hx)
  have hw1 : x * z * x⁻¹ ≠ 1 := by
    intro h
    rw [mul_inv_eq_one] at h
    exact hz1 (mul_left_cancel (h.trans (mul_one x).symm))
  have hw2 : (x * z * x⁻¹) ^ 2 = 1 := by
    calc (x * z * x⁻¹) ^ 2 = x * z ^ 2 * x⁻¹ := by simp [pow_two, mul_assoc]
      _ = 1 := by rw [hz2]; simp
  rcases hq _ hwQ hw1 with h | h
  · calc x * z = x * z * x⁻¹ * x := by simp
      _ = z * x := by rw [h]
  · exact absurd (h.symm.trans hw2) hz1

theorem fixed_of_card_lt_eight {M Ω : Type*} [Group M] [Fintype Ω] [DecidableEq Ω]
    (ρ : M →* Equiv.Perm Ω) {Q : Subgroup M} (hQ : Nat.card Q = 8) {z : M}
    (hzQ : z ∈ Q) (hq : ∀ x ∈ Q, x ≠ 1 → x = z ∨ x ^ 2 = z) (hz1 : z ≠ 1)
    (S : Finset Ω) (hS : ∀ q ∈ Q, ∀ ω ∈ S, ρ q ω ∈ S) (hcard : S.card < 8) :
    ∀ ω ∈ S, ρ z ω = ω := by
  have hcomm : ∀ x ∈ Q, x * z = z * x := (quat_z_central hQ hzQ hz1 hq).2
  let T : Finset Ω := S.filter (fun ω => ρ z ω ≠ ω)
  have hmemT : ∀ ω, ω ∈ T ↔ ω ∈ S ∧ ρ z ω ≠ ω := fun ω => Finset.mem_filter
  have hTS : ∀ q ∈ Q, ∀ ω ∈ T, ρ q ω ∈ T := by
    intro q hqQ ω hω
    obtain ⟨hωS, hωz⟩ := (hmemT ω).mp hω
    rw [hmemT]
    refine ⟨hS q hqQ ω hωS, fun h => hωz ?_⟩
    have h1 : ρ (q * z) = ρ (z * q) := by rw [hcomm q hqQ]
    have h2 : ρ q * ρ z = ρ z * ρ q := by rw [← map_mul, ← map_mul, h1]
    have h3 : ρ q (ρ z ω) = ρ z (ρ q ω) := by
      have h4 := congrArg (fun σ : Equiv.Perm Ω => σ ω) h2
      simpa [Equiv.Perm.mul_apply] using h4
    apply (ρ q).injective
    rw [h3]
    exact h
  have hfreeT : ∀ ω ∈ T, ρ z ω ≠ ω := fun ω hω => ((hmemT ω).mp hω).2
  have hdvd : 8 ∣ T.card := eight_dvd_card_of_free ρ hQ hq T hTS hfreeT
  have hTlt : T.card < 8 := lt_of_le_of_lt (Finset.card_filter_le _ _) hcard
  have hTe : T = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_dvd_of_lt hdvd hTlt)
  intro ω hω
  by_contra hne
  have hωT : ω ∈ T := (hmemT ω).mpr ⟨hω, hne⟩
  rw [hTe] at hωT
  exact Finset.notMem_empty ω hωT

end CFSG.RankThree.PartTwo.Sec8.HeringBMem
