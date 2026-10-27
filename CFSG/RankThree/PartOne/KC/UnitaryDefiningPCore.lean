module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
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
public import Mathlib.Order.CompletePartialOrder
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

namespace CFSG.RankThree.PartOne.KCUnitaryDefining

theorem conj_apply_mulAut {G : Type*} [Group G] (s : MulAut G) (x : G) :
    MulAut.conj (s x) = s * MulAut.conj x * s⁻¹ := by
  ext y
  simp only [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv, MulAut.apply_inv_self]

theorem eq_bot_of_pointwise_centralizer_of_pCore {T : Type*} [Group T] [Finite T]
    (hinj : Function.Injective (MulAut.conj : T →* MulAut T)) {p : ℕ} (hp : p.Prime) {x : T}
    (U : Subgroup T) (hUC : U ≤ Subgroup.centralizer ({x} : Set T)) (hUp : ∀ z ∈ U, z ^ p = 1)
    (hUnorm : ∀ c ∈ Subgroup.centralizer ({x} : Set T), ∀ z ∈ U, c * z * c⁻¹ ∈ U)
    (hpt : ∀ α : MulAut T, (∀ z ∈ U, α z = z) → ∃ z ∈ U, α = MulAut.conj z)
    (B : Subgroup (MulAut T)) (hB : (MulAut.conj : T →* MulAut T).range ≤ B)
    (S : Subgroup (MulAut T)) (hSC : S ≤ B ⊓ Subgroup.centralizer {MulAut.conj x})
    (hSn : (S.subgroupOf (B ⊓ Subgroup.centralizer {MulAut.conj x})).Normal)
    (hSp : ¬ p ∣ Nat.card S) : S = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  set C := Subgroup.centralizer ({x} : Set T) with hC
  set P₀ := (CFSG.pCore p C).map C.subtype with hP₀
  set W := P₀.map (MulAut.conj : T →* MulAut T) with hW
  set L := B ⊓ Subgroup.centralizer {MulAut.conj x} with hL
  have hUP₀ : U ≤ P₀ := by
    have hnorm : (U.subgroupOf C).Normal := ⟨fun n hn c => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      exact hUnorm c c.2 n hn⟩
    have hpg : IsPGroup p (U.subgroupOf C) := fun z => ⟨1, by
      have h := hUp _ (Subgroup.mem_subgroupOf.mp z.2)
      apply Subtype.ext
      apply Subtype.ext
      simpa using h⟩
    have hle : U.subgroupOf C ≤ CFSG.pCore p C := le_sSup ⟨hnorm, hpg⟩
    intro z hz
    exact ⟨⟨z, hUC hz⟩, hle (Subgroup.mem_subgroupOf.mpr hz), rfl⟩
  have hWp : IsPGroup p W := ((CFSG.pCore_isPGroup).map C.subtype).map _
  have hfix : ∀ s ∈ L, s x = x := by
    intro s hs
    apply hinj
    rw [conj_apply_mulAut, Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hs).2,
      mul_inv_cancel_right]
  have hres : ∀ t : MulAut T, t x = x → ∀ c ∈ C, t c ∈ C := by
    intro t ht c hc
    rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
    rw [← ht, ← map_mul, ← map_mul, hc]
  have hP₀inv : ∀ s ∈ L, ∀ y ∈ P₀, s y ∈ P₀ := by
    intro s hs y hy
    have hs1 := hfix s hs
    have hs2 : s⁻¹ x = x := by
      change s.symm x = x
      rw [MulEquiv.symm_apply_eq, hs1]
    let φ : C ≃* C :=
      { toFun := fun c => ⟨s c, hres s hs1 c c.2⟩
        invFun := fun c => ⟨s⁻¹ c, hres s⁻¹ hs2 c c.2⟩
        left_inv := fun c => Subtype.ext (by simp)
        right_inv := fun c => Subtype.ext (by simp)
        map_mul' := fun c c' => Subtype.ext (map_mul s (c : T) c') }
    obtain ⟨c, hc, rfl⟩ := hy
    have hφc : φ c ∈ CFSG.pCore p C := by
      rw [← CFSG.pCore_map_iso p φ]
      exact Subgroup.mem_map_of_mem _ hc
    exact ⟨φ c, hφc, rfl⟩
  have hWL : W ≤ L := by
    rintro _ ⟨y, hy, rfl⟩
    have hyC : y ∈ C := by
      obtain ⟨c, -, rfl⟩ := hy
      exact c.2
    refine Subgroup.mem_inf.2 ⟨hB ⟨y, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.1 hyC]
  have hWnorm : ∀ s ∈ L, ∀ w ∈ W, s * w * s⁻¹ ∈ W := by
    rintro s hs _ ⟨y, hy, rfl⟩
    exact ⟨s y, hP₀inv s hs y hy, conj_apply_mulAut s y⟩
  have hSnorm : ∀ y ∈ L, ∀ s ∈ S, y * s * y⁻¹ ∈ S := by
    intro y hy s hs
    exact Subgroup.mem_subgroupOf.1
      (hSn.conj_mem ⟨s, hSC hs⟩ (Subgroup.mem_subgroupOf.2 hs) ⟨y, hy⟩)
  have hdisj : Disjoint S W := by
    apply Subgroup.disjoint_of_coprime_natCard
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 hWp
    rw [hm]
    exact Nat.Coprime.pow_right m ((Nat.Prime.coprime_iff_not_dvd hp).2 hSp).symm
  have hcomm : ∀ s ∈ S, ∀ w ∈ W, s * w = w * s := by
    intro s hs w hw
    have h1 : s * w * s⁻¹ * w⁻¹ ∈ W := W.mul_mem (hWnorm s (hSC hs) w hw) (W.inv_mem hw)
    have h2 : s * w * s⁻¹ * w⁻¹ ∈ S := by
      have := S.mul_mem hs (hSnorm w (hWL hw) s⁻¹ (S.inv_mem hs))
      rwa [← mul_assoc, ← mul_assoc] at this
    have h3 := Subgroup.disjoint_def.1 hdisj h2 h1
    calc s * w = s * w * s⁻¹ * w⁻¹ * (w * s) := by group
      _ = w * s := by rw [h3, one_mul]
  have hSW : S ≤ W := by
    intro s hs
    have hpt' : ∀ z ∈ U, s z = z := by
      intro z hz
      apply hinj
      rw [conj_apply_mulAut, hcomm s hs _ ⟨z, hUP₀ hz, rfl⟩, mul_inv_cancel_right]
    obtain ⟨z, hz, rfl⟩ := hpt s hpt'
    exact ⟨z, hUP₀ hz, rfl⟩
  exact hdisj.eq_bot_of_le hSW

end CFSG.RankThree.PartOne.KCUnitaryDefining
