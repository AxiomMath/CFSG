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
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.GroupTheory.GroupAction.Primitive
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
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

namespace CFSG

namespace M23

open scoped Pointwise

theorem isSimpleGroup_of_preprimitive_of_sylow_normal_generator
    {G X : Type*} [Group G] [Fintype G] [Fintype X]
    [MulAction G X] [FaithfulSMul G X] [MulAction.IsPreprimitive G X]
    (p : ℕ) [Fact p.Prime] (hX : Fintype.card X = p)
    (c : G) (hc : orderOf c = p)
    (hpG : (Nat.card G).factorization p = 1)
    (hgen : ∀ (N : Subgroup G) [N.Normal], c ∈ N → N = ⊤) :
    IsSimpleGroup G := by
  classical
  have hc_ne : c ≠ 1 := by
    intro h
    apply (Fact.out : p.Prime).ne_one
    calc
      p = orderOf c := hc.symm
      _ = 1 := by simp [h]
  let : Nontrivial G := ⟨⟨c, 1, hc_ne⟩⟩
  rw [isSimpleGroup_iff]
  refine ⟨inferInstance, ?_⟩
  intro N hN
  by_cases hNbot : N = ⊥
  · exact Or.inl hNbot
  · right
    let : N.Normal := hN
    let : Nontrivial N := N.nontrivial_iff_ne_bot.mpr hNbot
    have hfixed : MulAction.fixedPoints N X ≠ Set.univ := by
      intro hfixed
      obtain ⟨n, m, hnm⟩ := exists_pair_ne N
      apply hnm
      apply Subtype.ext
      apply FaithfulSMul.eq_of_smul_eq_smul (M := G) (α := X)
      intro x
      have hx : x ∈ MulAction.fixedPoints N X := by
        rw [hfixed]
        exact Set.mem_univ x
      change ∀ k : N, k • x = x at hx
      simpa only [Subgroup.smul_def] using (hx n).trans (hx m).symm
    let : MulAction.IsPretransitive N X :=
      MulAction.IsQuasiPreprimitive.isPretransitive_of_normal hfixed
    let : Nonempty X := Fintype.card_pos_iff.mp (by
      rw [hX]
      exact (Fact.out : p.Prime).pos)
    let x : X := Classical.choice (inferInstance : Nonempty X)
    have horbit : Fintype.card (MulAction.orbit N x) = p := by
      rw [MulAction.orbit_eq_univ]
      simpa using hX
    have hpN : p ∣ Fintype.card N := by
      refine ⟨Fintype.card (MulAction.stabilizer N x), ?_⟩
      rw [← horbit]
      exact (MulAction.card_orbit_mul_card_stabilizer_eq_card_group N x).symm
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card p hpN
    have hycard :
        Nat.card (Subgroup.zpowers (y : G)) =
          p ^ (Nat.card G).factorization p := by
      calc
        Nat.card (Subgroup.zpowers (y : G)) = orderOf (y : G) := Nat.card_zpowers _
        _ = orderOf y := Subgroup.orderOf_coe y
        _ = p := hy
        _ = p ^ (Nat.card G).factorization p := by rw [hpG, pow_one]
    have hccard :
        Nat.card (Subgroup.zpowers c) =
          p ^ (Nat.card G).factorization p := by
      calc
        Nat.card (Subgroup.zpowers c) = orderOf c := Nat.card_zpowers _
        _ = p := hc
        _ = p ^ (Nat.card G).factorization p := by rw [hpG, pow_one]
    let Py : Sylow p G := Sylow.ofCard (Subgroup.zpowers (y : G)) hycard
    let Pc : Sylow p G := Sylow.ofCard (Subgroup.zpowers c) hccard
    have hPyN : (Py : Subgroup G) ≤ N := by
      change Subgroup.zpowers (y : G) ≤ N
      exact Subgroup.zpowers_le.mpr y.property
    have hcPc : c ∈ (Pc : Subgroup G) := by
      change c ∈ Subgroup.zpowers c
      exact Subgroup.mem_zpowers c
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Py Pc
    have hconjPyN : ((g • Py : Sylow p G) : Subgroup G) ≤ N := by
      rw [Sylow.coe_subgroup_smul]
      calc
        MulAut.conj g • (Py : Subgroup G) ≤ MulAut.conj g • N :=
          smul_le_smul_left _ hPyN
        _ = N := Subgroup.Normal.conj_smul_eq_self g N
    apply hgen N
    apply hconjPyN
    rw [hg]
    exact hcPc

end M23

end CFSG
