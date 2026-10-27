module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Diam
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
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Monster.B.TwoA.Amalgam

theorem exists_bilin_eq_zero_eq_one {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {B : LinearMap.BilinForm (ZMod 2) V} (hB : ∀ x, (∀ w, B x w = 0) → x = 0) {x y : V}
    (hx : x ≠ 0) (hxy : x ≠ y) : ∃ w, B y w = 0 ∧ B x w = 1 := by
  have h01 : ∀ t : ZMod 2, t ≠ 0 → t = 1 := by decide
  have hne : ∀ z : V, z ≠ 0 → ∃ w, B z w = 1 := fun z hz => by
    by_contra h
    push Not at h
    exact hz (hB z fun w => by
      by_contra h'
      exact h w (h01 _ h'))
  obtain ⟨w₁, h₁⟩ := hne x hx
  obtain ⟨w₂, h₂⟩ := hne (x - y) (sub_ne_zero.2 hxy)
  rw [LinearMap.BilinForm.sub_left] at h₂
  have key : ∀ p q r s : ZMod 2, p = 1 → r - s = 1 →
      (q = 0 ∧ p = 1) ∨ (s = 0 ∧ r = 1) ∨ (q + s = 0 ∧ p + r = 1) := by decide
  rcases key _ (B y w₁) _ (B y w₂) h₁ h₂ with h | h | h
  · exact ⟨w₁, h⟩
  · exact ⟨w₂, h⟩
  · exact ⟨w₁ + w₂, by
      rw [LinearMap.BilinForm.add_right, LinearMap.BilinForm.add_right]
      exact h⟩

theorem ncard_preimage_of_fiber {α β : Type*} [Finite α] [Finite β] {ψ : β → α} {m : ℕ}
    (hfib : ∀ x, (ψ ⁻¹' {x}).ncard = m) (S : Set α) : (ψ ⁻¹' S).ncard = m * S.ncard := by
  classical
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  rw [Set.ncard_eq_toFinset_card' (ψ ⁻¹' S), Set.ncard_eq_toFinset_card' S,
    Finset.card_eq_sum_card_fiberwise (f := ψ) (t := S.toFinset) (fun x hx => by
      simpa using hx)]
  rw [Finset.sum_congr rfl fun b hb => (show ((ψ ⁻¹' S).toFinset.filter fun a => ψ a = b).card
      = m by
    rw [← hfib b, Set.ncard_eq_toFinset_card']
    congr 1
    ext a
    simp only [Finset.mem_filter, Set.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨h ▸ (by simpa using hb), h⟩)]
  rw [Finset.sum_const, smul_eq_mul, mul_comm]

theorem twoClique_extension {α β : Type*} [Finite α] [Finite β] {H : SimpleGraph α}
    {G : SimpleGraph β} {ψ : β → α} (hfib : ∀ x, (ψ ⁻¹' {x}).ncard = 2)
    (hadj : ∀ v w, v ≠ w → (G.Adj v w ↔ ψ v = ψ w ∨ H.Adj (ψ v) (ψ w)))
    {k μ : ℕ} (hk : ∀ x, (H.neighborSet x).ncard = k)
    (hμ : ∀ x y, x ≠ y → ¬ H.Adj x y → (H.commonNeighbors x y).ncard = μ) (hμ0 : μ ≠ 0)
    {x₀ y₀ : α} (hxy₀ : x₀ ≠ y₀) (hnadj₀ : ¬ H.Adj x₀ y₀) :
    (∀ v, (G.neighborSet v).ncard = 2 * k + 1) ∧ G.Connected ∧ G.diam = 2 ∧
      ∀ v w, v ≠ w → ¬ G.Adj v w → (G.commonNeighbors v w).ncard = 2 * μ := by
  have hadj' : ∀ v w, G.Adj v w ↔ v ≠ w ∧ (ψ v = ψ w ∨ H.Adj (ψ v) (ψ w)) := fun v w =>
    ⟨fun h => ⟨G.ne_of_adj h, (hadj v w (G.ne_of_adj h)).1 h⟩, fun h => (hadj v w h.1).2 h.2⟩
  have hcommon : ∀ v w, v ≠ w → ¬ G.Adj v w →
      G.commonNeighbors v w = ψ ⁻¹' H.commonNeighbors (ψ v) (ψ w) := by
    intro v w hvw hnadj
    have hne : ψ v ≠ ψ w := fun h => hnadj ((hadj v w hvw).2 (Or.inl h))
    have hna : ¬ H.Adj (ψ v) (ψ w) := fun h => hnadj ((hadj v w hvw).2 (Or.inr h))
    ext u
    simp only [SimpleGraph.mem_commonNeighbors, Set.mem_preimage]
    constructor
    · rintro ⟨hvu, hwu⟩
      rw [hadj'] at hvu hwu
      rcases hvu.2 with h1 | h1 <;> rcases hwu.2 with h2 | h2
      · exact absurd (h1.trans h2.symm) hne
      · rw [← h1] at h2
        exact absurd h2.symm hna
      · rw [← h2] at h1
        exact absurd h1 hna
      · exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨(hadj' v u).2 ⟨fun e => ?_, Or.inr h1⟩, (hadj' w u).2 ⟨fun e => ?_, Or.inr h2⟩⟩
      · rw [e] at h1
        exact H.ne_of_adj h1 rfl
      · rw [e] at h2
        exact H.ne_of_adj h2 rfl
  have hcard_common : ∀ v w, v ≠ w → ¬ G.Adj v w → (G.commonNeighbors v w).ncard = 2 * μ := by
    intro v w hvw hnadj
    have hne : ψ v ≠ ψ w := fun h => hnadj ((hadj v w hvw).2 (Or.inl h))
    have hna : ¬ H.Adj (ψ v) (ψ w) := fun h => hnadj ((hadj v w hvw).2 (Or.inr h))
    rw [hcommon v w hvw hnadj, ncard_preimage_of_fiber hfib, hμ _ _ hne hna]
  have hnbr : ∀ v, G.neighborSet v = (ψ ⁻¹' {ψ v} \ {v}) ∪ ψ ⁻¹' H.neighborSet (ψ v) := by
    intro v
    ext u
    simp only [SimpleGraph.mem_neighborSet, Set.mem_union, Set.mem_sdiff, Set.mem_preimage,
      Set.mem_singleton_iff]
    rw [hadj']
    constructor
    · rintro ⟨hvu, h | h⟩
      · exact Or.inl ⟨h.symm, fun e => hvu e.symm⟩
      · exact Or.inr h
    · rintro (⟨h1, h2⟩ | h)
      · exact ⟨fun e => h2 e.symm, Or.inl h1.symm⟩
      · refine ⟨fun e => ?_, Or.inr h⟩
        rw [e] at h
        exact H.ne_of_adj h rfl
  have hdeg : ∀ v, (G.neighborSet v).ncard = 2 * k + 1 := by
    intro v
    rw [hnbr, Set.ncard_union_eq _ (Set.toFinite _) (Set.toFinite _),
      Set.ncard_sdiff_singleton_of_mem (by rfl : v ∈ ψ ⁻¹' {ψ v}), hfib,
      ncard_preimage_of_fiber hfib, hk]
    · omega
    · rw [Set.disjoint_left]
      rintro u ⟨hu, -⟩ hu'
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hu
      simp only [Set.mem_preimage, SimpleGraph.mem_neighborSet] at hu'
      rw [hu] at hu'
      exact H.ne_of_adj hu' rfl
  have hfibne : ∀ x, (ψ ⁻¹' {x}).Nonempty := fun x =>
    Set.nonempty_of_ncard_ne_zero (by rw [hfib]; norm_num)
  obtain ⟨u₀, hu₀⟩ := hfibne x₀
  obtain ⟨v₀, hv₀⟩ := hfibne y₀
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hu₀ hv₀
  have huv₀ : u₀ ≠ v₀ := fun e => hxy₀ (by rw [← hu₀, ← hv₀, e])
  have hnuv₀ : ¬ G.Adj u₀ v₀ := by
    rw [hadj']
    rintro ⟨-, h | h⟩
    · exact hxy₀ (by rw [← hu₀, ← hv₀, h])
    · rw [hu₀, hv₀] at h
      exact hnadj₀ h
  have hediam : G.ediam = 2 := by
    apply le_antisymm
    · rw [SimpleGraph.ediam_le_iff]
      intro u v
      by_contra hc
      push Not at hc
      obtain ⟨hn, ha, he⟩ := SimpleGraph.two_lt_edist_iff.mp hc
      have h := hcard_common u v hn ha
      rw [he, Set.ncard_empty] at h
      omega
    · have h2 : G.edist u₀ v₀ = 2 := SimpleGraph.edist_eq_two_iff.2 ⟨huv₀, hnuv₀,
        Set.nonempty_of_ncard_ne_zero (by rw [hcard_common u₀ v₀ huv₀ hnuv₀]; omega)⟩
      rw [← h2]
      exact SimpleGraph.edist_le_ediam
  have : Nonempty β := ⟨u₀⟩
  refine ⟨hdeg, SimpleGraph.connected_of_ediam_ne_top (by rw [hediam]; simp), ?_, hcard_common⟩
  simp [SimpleGraph.diam, hediam]

end CFSG.Monster.B.TwoA.Amalgam
