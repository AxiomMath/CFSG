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
public import Certificates.Data.Schreier

public section

namespace CFSG

namespace M23

open scoped Pointwise

theorem closure_stabilizer_eq_top_of_schreier
    {G X : Type*} [Group G] [MulAction G X]
    {m n : ℕ} (S : Fin m → G)
    (hS : Subgroup.closure (Set.range S) = ⊤)
    (p : X) (t : X → G)
    (htp : t p = 1)
    (ht : ∀ x ∈ MulAction.orbit G p, t x • p = x)
    (T : Fin n → MulAction.stabilizer G p)
    (hsch : ∀ x ∈ MulAction.orbit G p, ∀ i,
      (t (S i • x))⁻¹ * S i * t x ∈
        Subgroup.map (MulAction.stabilizer G p).subtype
          (Subgroup.closure (Set.range T))) :
    Subgroup.closure (Set.range T) = ⊤ := by
  let K : Subgroup G :=
    Subgroup.map (MulAction.stabilizer G p).subtype
      (Subgroup.closure (Set.range T))
  have orbit_smul (g : G) {x : X} (hx : x ∈ MulAction.orbit G p) :
      g • x ∈ MulAction.orbit G p := by
    rcases hx with ⟨h, rfl⟩
    exact ⟨g * h, by simp only [mul_smul]⟩
  have hall (g : G) : ∀ x ∈ MulAction.orbit G p,
      (t (g • x))⁻¹ * g * t x ∈ K := by
    have hg : g ∈ Subgroup.closure (Set.range S) := by
      rw [hS]
      trivial
    exact Subgroup.closure_induction
      (p := fun g _ => ∀ x ∈ MulAction.orbit G p,
        (t (g • x))⁻¹ * g * t x ∈ K)
      (fun g hg x hx => by
        obtain ⟨i, rfl⟩ := hg
        exact hsch x hx i)
      (by
        intro x hx
        simpa using K.one_mem)
      (fun g h _ _ hg hh x hx => by
        have hhx := hh x hx
        have hgx := hg (h • x) (orbit_smul h hx)
        have := K.mul_mem hgx hhx
        convert this using 1 <;> simp only [mul_smul] <;> group)
      (fun g _ hg x hx => by
        have hy : g⁻¹ • x ∈ MulAction.orbit G p := orbit_smul g⁻¹ hx
        have hgy := hg (g⁻¹ • x) hy
        have := K.inv_mem hgy
        convert this using 1 <;>
          simp only [smul_smul, mul_inv_cancel, one_smul, mul_inv_rev, inv_inv] <;>
          group)
      hg
  apply top_unique
  intro y hy
  have hyfix : (y : G) • p = p := y.property
  have hyK : (y : G) ∈ K := by
    have := hall (y : G) p ⟨1, by simp⟩
    simpa only [hyfix, htp, inv_one, mul_one, one_mul] using this
  rcases hyK with ⟨z, hz, hzy⟩
  have heq : z = y := by
    apply Subtype.ext
    exact hzy
  simpa [heq] using hz

theorem stabilizer_subsingleton_of_schreier
    {G X : Type*} [Group G] [MulAction G X]
    {m : ℕ} (S : Fin m → G)
    (hS : Subgroup.closure (Set.range S) = ⊤)
    (p : X) (t : X → G)
    (htp : t p = 1)
    (ht : ∀ x ∈ MulAction.orbit G p, t x • p = x)
    (hsch : ∀ x ∈ MulAction.orbit G p, ∀ i,
      (t (S i • x))⁻¹ * S i * t x = 1) :
    Subsingleton (MulAction.stabilizer G p) := by
  let T : Fin 0 → MulAction.stabilizer G p := Fin.elim0
  have hsch' : ∀ x ∈ MulAction.orbit G p, ∀ i,
      (t (S i • x))⁻¹ * S i * t x ∈
        Subgroup.map (MulAction.stabilizer G p).subtype
          (Subgroup.closure (Set.range T)) := by
    intro x hx i
    rw [hsch x hx i]
    exact Subgroup.one_mem _
  have htop : Subgroup.closure (Set.range T) = ⊤ :=
    closure_stabilizer_eq_top_of_schreier S hS p t htp ht T hsch'
  refine ⟨fun x y ↦ ?_⟩
  have hx : x ∈ Subgroup.closure (Set.range T) := by rw [htop]; trivial
  have hy : y ∈ Subgroup.closure (Set.range T) := by rw [htop]; trivial
  rw [Set.range_eq_empty T, Subgroup.closure_empty] at hx hy
  exact (Subgroup.mem_bot.mp hx).trans (Subgroup.mem_bot.mp hy).symm

end M23

end CFSG
