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
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Sporadic.LySchreier

variable {G X : Type*} [Group G] [MulAction G X]

@[expose] def levelStab (K : Subgroup G) (b : ℕ → X) (i : ℕ) : Subgroup G :=
  K ⊓ ⨅ l : Fin i, MulAction.stabilizer G (b l)

theorem mem_levelStab {K : Subgroup G} {b : ℕ → X} {i : ℕ} {g : G} :
    g ∈ levelStab K b i ↔ g ∈ K ∧ ∀ l < i, g • b l = b l := by
  simp only [levelStab, Subgroup.mem_inf, Subgroup.mem_iInf, MulAction.mem_stabilizer_iff]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1, fun l hl => h2 ⟨l, hl⟩⟩, fun ⟨h1, h2⟩ => ⟨h1, fun l => h2 l l.2⟩⟩

theorem levelStab_zero (K : Subgroup G) (b : ℕ → X) : levelStab K b 0 = K := by
  ext g
  simp [mem_levelStab]

@[expose] def levelStabEquiv (K : Subgroup G) (b : ℕ → X) (i : ℕ) :
    levelStab K b (i + 1) ≃ MulAction.stabilizer (levelStab K b i) (b i) where
  toFun g := ⟨⟨g.1, mem_levelStab.2 ⟨(mem_levelStab.1 g.2).1,
      fun l hl => (mem_levelStab.1 g.2).2 l (by omega)⟩⟩,
    MulAction.mem_stabilizer_iff.2 ((mem_levelStab.1 g.2).2 i (by omega))⟩
  invFun g := ⟨g.1.1, mem_levelStab.2 ⟨(mem_levelStab.1 g.1.2).1, fun l hl => by
      rcases Nat.lt_succ_iff_lt_or_eq.1 hl with h | h
      · exact (mem_levelStab.1 g.1.2).2 l h
      · subst h
        exact MulAction.mem_stabilizer_iff.1 g.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_mul_card_levelStab_succ_le [Finite G] (K : Subgroup G) (b : ℕ → X) (i : ℕ)
    (O : Finset X) (hO : ∀ y ∈ O, ∃ g ∈ levelStab K b i, g • b i = y) :
    O.card * Nat.card (levelStab K b (i + 1)) ≤ Nat.card (levelStab K b i) := by
  set L := levelStab K b i
  rw [← Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup L (b i)), Nat.card_prod,
    Nat.card_congr (levelStabEquiv K b i)]
  apply Nat.mul_le_mul_right
  have hsub : (O : Set X) ⊆ MulAction.orbit L (b i) := by
    intro y hy
    obtain ⟨g, hg, rfl⟩ := hO y hy
    exact ⟨⟨g, hg⟩, rfl⟩
  have hfin : (MulAction.orbit L (b i)).Finite := Set.finite_range _
  calc O.card = Nat.card (O : Set X) := by simp
    _ ≤ Nat.card (MulAction.orbit L (b i)) := Nat.card_mono hfin hsub

theorem prod_card_le_card_of_witnesses [Finite G] (K : Subgroup G) (b : ℕ → X) (m : ℕ)
    (O : ℕ → Finset X)
    (hO : ∀ i < m, ∀ y ∈ O i, ∃ g ∈ K, (∀ l < i, g • b l = b l) ∧ g • b i = y) :
    ∏ i ∈ Finset.range m, (O i).card ≤ Nat.card K := by
  have key : ∀ d i, i + d = m →
      (∏ l ∈ Finset.Ico i m, (O l).card) * Nat.card (levelStab K b m) ≤
        Nat.card (levelStab K b i) := by
    intro d
    induction d with
    | zero =>
      intro i hi
      subst hi
      simp
    | succ d ih =>
      intro i hi
      have hlt : i < m := by omega
      rw [Finset.prod_eq_prod_Ico_succ_bot hlt, mul_assoc]
      calc (O i).card * ((∏ l ∈ Finset.Ico (i + 1) m, (O l).card) *
            Nat.card (levelStab K b m)) ≤ (O i).card * Nat.card (levelStab K b (i + 1)) :=
            Nat.mul_le_mul_left _ (ih (i + 1) (by omega))
        _ ≤ Nat.card (levelStab K b i) := by
            apply card_mul_card_levelStab_succ_le
            intro y hy
            obtain ⟨g, hgK, hgfix, hgy⟩ := hO i hlt y hy
            exact ⟨g, mem_levelStab.2 ⟨hgK, hgfix⟩, hgy⟩
  have h := key m 0 (zero_add m)
  rw [levelStab_zero, ← Finset.range_eq_Ico] at h
  exact le_trans (Nat.le_mul_of_pos_right _ Nat.card_pos) h

end CFSG.Sporadic.LySchreier
