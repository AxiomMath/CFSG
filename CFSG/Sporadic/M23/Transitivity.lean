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
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
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

namespace M23.FourTransitivity

abbrev X := Fin 23

variable {G : Type*} [Group G] [MulAction G X]

abbrev K1 (G : Type*) [Group G] [MulAction G X] : Subgroup G :=
  MulAction.stabilizer G (0 : X)
abbrev K2 (G : Type*) [Group G] [MulAction G X] : Subgroup (K1 G) :=
  MulAction.stabilizer (K1 G) (1 : X)
abbrev K3 (G : Type*) [Group G] [MulAction G X] : Subgroup (K2 G) :=
  MulAction.stabilizer (K2 G) (2 : X)

@[expose] def lift1 (g : K1 G) : G := g
@[expose] def lift2 (g : K2 G) : G := g.1.1
@[expose] def lift3 (g : K3 G) : G := g.1.1.1

@[simp] lemma lift1_smul (g : K1 G) (x : X) : lift1 g • x = g • x := rfl
@[simp] lemma lift2_smul (g : K2 G) (x : X) : lift2 g • x = g • x := rfl
@[simp] lemma lift3_smul (g : K3 G) (x : X) : lift3 g • x = g • x := rfl

private lemma lift1_fix0 (g : K1 G) : lift1 g • (0 : X) = 0 := g.property
private lemma lift2_fix0 (g : K2 G) : lift2 g • (0 : X) = 0 := g.1.property
private lemma lift2_fix1 (g : K2 G) : lift2 g • (1 : X) = 1 := g.property
private lemma lift3_fix0 (g : K3 G) : lift3 g • (0 : X) = 0 := g.1.1.property
private lemma lift3_fix1 (g : K3 G) : lift3 g • (1 : X) = 1 := g.1.property
private lemma lift3_fix2 (g : K3 G) : lift3 g • (2 : X) = 2 := g.property

private lemma exists_maps_base_four
    (t0 : X → G)
    (t1 : X → K1 G)
    (t2 : X → K2 G)
    (t3 : X → K3 G)
    (ht0 : ∀ x, t0 x • (0 : X) = x)
    (ht1 : ∀ x, x ≠ 0 → t1 x • (1 : X) = x)
    (ht2 : ∀ x, x ≠ 0 → x ≠ 1 → t2 x • (2 : X) = x)
    (ht3 : ∀ x, x ≠ 0 → x ≠ 1 → x ≠ 2 → t3 x • (3 : X) = x)
    (e : Fin 4 ↪ X) :
    ∃ g : G, ∀ i : Fin 4, g • (i.castLE (by omega : 4 ≤ 23)) = e i := by
  let q0 : G := t0 (e 0)
  let x1 : X := q0⁻¹ • e 1
  have hx1 : x1 ≠ 0 := by
    intro h
    have h' := congrArg (fun z : X ↦ q0 • z) h
    have heq : e 1 = e 0 := by simpa [x1, q0, ht0] using h'
    exact (by omega : (1 : Fin 4) ≠ 0) (e.injective heq)
  let q1 : K1 G := t1 x1
  let r1 : G := q0 * lift1 q1
  have hr10 : r1 • (0 : X) = e 0 := by
    simp only [r1, mul_smul]
    rw [lift1_fix0, ht0]
  have hr11 : r1 • (1 : X) = e 1 := by
    simp only [r1, mul_smul]
    rw [show lift1 q1 • (1 : X) = x1 by exact ht1 x1 hx1]
    simp [x1]
  let x2 : X := r1⁻¹ • e 2
  have hx20 : x2 ≠ 0 := by
    intro h
    have h' := congrArg (fun z : X ↦ r1 • z) h
    have heq : e 2 = e 0 := by simpa [x2, hr10] using h'
    exact (by omega : (2 : Fin 4) ≠ 0) (e.injective heq)
  have hx21 : x2 ≠ 1 := by
    intro h
    have h' := congrArg (fun z : X ↦ r1 • z) h
    have heq : e 2 = e 1 := by simpa [x2, hr11] using h'
    exact (by omega : (2 : Fin 4) ≠ 1) (e.injective heq)
  let q2 : K2 G := t2 x2
  let r2 : G := r1 * lift2 q2
  have hr20 : r2 • (0 : X) = e 0 := by
    simp only [r2, mul_smul]
    rw [lift2_fix0, hr10]
  have hr21 : r2 • (1 : X) = e 1 := by
    simp only [r2, mul_smul]
    rw [lift2_fix1, hr11]
  have hr22 : r2 • (2 : X) = e 2 := by
    simp only [r2, mul_smul]
    rw [show lift2 q2 • (2 : X) = x2 by exact ht2 x2 hx20 hx21]
    simp [x2]
  let x3 : X := r2⁻¹ • e 3
  have hx30 : x3 ≠ 0 := by
    intro h
    have h' := congrArg (fun z : X ↦ r2 • z) h
    have heq : e 3 = e 0 := by simpa [x3, hr20] using h'
    exact (by omega : (3 : Fin 4) ≠ 0) (e.injective heq)
  have hx31 : x3 ≠ 1 := by
    intro h
    have h' := congrArg (fun z : X ↦ r2 • z) h
    have heq : e 3 = e 1 := by simpa [x3, hr21] using h'
    exact (by omega : (3 : Fin 4) ≠ 1) (e.injective heq)
  have hx32 : x3 ≠ 2 := by
    intro h
    have h' := congrArg (fun z : X ↦ r2 • z) h
    have heq : e 3 = e 2 := by simpa [x3, hr22] using h'
    exact (by omega : (3 : Fin 4) ≠ 2) (e.injective heq)
  let q3 : K3 G := t3 x3
  let r3 : G := r2 * lift3 q3
  refine ⟨r3, ?_⟩
  intro i
  fin_cases i
  · change r3 • (0 : X) = e 0
    simp only [r3, mul_smul]
    rw [lift3_fix0, hr20]
  · change r3 • (1 : X) = e 1
    simp only [r3, mul_smul]
    rw [lift3_fix1, hr21]
  · change r3 • (2 : X) = e 2
    simp only [r3, mul_smul]
    rw [lift3_fix2, hr22]
  · change r3 • (3 : X) = e 3
    simp only [r3, mul_smul]
    rw [show lift3 q3 • (3 : X) = x3 by exact ht3 x3 hx30 hx31 hx32]
    simp [x3]

theorem four_pretransitive_of_transversals
    (t0 : X → G)
    (t1 : X → K1 G)
    (t2 : X → K2 G)
    (t3 : X → K3 G)
    (ht0 : ∀ x, t0 x • (0 : X) = x)
    (ht1 : ∀ x, x ≠ 0 → t1 x • (1 : X) = x)
    (ht2 : ∀ x, x ≠ 0 → x ≠ 1 → t2 x • (2 : X) = x)
    (ht3 : ∀ x, x ≠ 0 → x ≠ 1 → x ≠ 2 → t3 x • (3 : X) = x) :
    MulAction.IsMultiplyPretransitive G X 4 := by
  rw [MulAction.isMultiplyPretransitive_iff]
  intro e f
  obtain ⟨ge, hge⟩ := exists_maps_base_four t0 t1 t2 t3 ht0 ht1 ht2 ht3 e
  obtain ⟨gf, hgf⟩ := exists_maps_base_four t0 t1 t2 t3 ht0 ht1 ht2 ht3 f
  refine ⟨gf * ge⁻¹, ?_⟩
  apply Function.Embedding.ext
  intro i
  change (gf * ge⁻¹) • e i = f i
  rw [mul_smul]
  have hei := hge i
  have hfi := hgf i
  have hei' := congrArg (fun z : X ↦ ge⁻¹ • z) hei
  rw [smul_smul] at hei'
  simpa [hfi] using (congrArg (fun z : X ↦ gf • z) hei').symm

end M23.FourTransitivity

end CFSG
