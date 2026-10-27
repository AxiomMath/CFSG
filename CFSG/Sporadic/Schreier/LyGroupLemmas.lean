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

namespace CFSG.Sporadic.LySchreier

section Fixed

variable {G X : Type*} [Group G] [MulAction G X] [Finite G]

theorem centralizer_eq_of_transitive (z : G) (C : Subgroup G)
    (hC : C ≤ Subgroup.centralizer {z}) (F : Finset X)
    (hF : ∀ x, x ∈ F ↔ z • x = x) (x₀ : X) (hx₀ : x₀ ∈ F)
    (m : ℕ) (hstab : Nat.card ↥(Subgroup.centralizer {z} ⊓ MulAction.stabilizer G x₀) ≤ m)
    (hcard : F.card * m ≤ Nat.card C) :
    C = Subgroup.centralizer {z} ∧ Nat.card C = F.card * m := by
  set Z := Subgroup.centralizer ({z} : Set G)
  have hZF : ∀ g ∈ Z, ∀ x ∈ F, g • x ∈ F := by
    intro g hg x hx
    rw [hF] at hx ⊢
    have hgz : g * z = z * g := Subgroup.mem_centralizer_singleton_iff.1 hg
    rw [← mul_smul, ← hgz, mul_smul, hx]
  have horbit : Nat.card (MulAction.orbit Z x₀) ≤ F.card := by
    have hsub : MulAction.orbit Z x₀ ⊆ (F : Set X) := by
      rintro _ ⟨g, rfl⟩
      exact hZF g g.2 x₀ hx₀
    calc Nat.card (MulAction.orbit Z x₀) ≤ Nat.card (F : Set X) :=
          Nat.card_mono (Set.toFinite _) hsub
      _ = F.card := by simp
  have hstab' : Nat.card (MulAction.stabilizer Z x₀) ≤ m := by
    refine le_trans (le_of_eq ?_) hstab
    refine Nat.card_congr
      { toFun := fun g => ⟨g.1.1, g.1.2, g.2⟩
        invFun := fun g => ⟨⟨g.1, g.2.1⟩, g.2.2⟩
        left_inv := fun g => rfl
        right_inv := fun g => rfl }
  have hZcard : Nat.card Z ≤ F.card * m := by
    rw [← Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup Z x₀), Nat.card_prod]
    exact Nat.mul_le_mul horbit hstab'
  have hle : Nat.card Z ≤ Nat.card C := le_trans hZcard hcard
  have heq : C = Z := Subgroup.eq_of_le_of_card_ge hC hle
  refine ⟨heq, le_antisymm ?_ hcard⟩
  rw [heq]
  exact hZcard

end Fixed

theorem conj_eq_of_odd_order {G : Type*} [Group G] {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    {k : ℕ} (hk : (a * b) ^ (2 * k + 1) = 1) : (a * b) ^ k * a * ((a * b) ^ k)⁻¹ = b := by
  set c := a * b with hc
  have hbcb : b * c * b = c⁻¹ := by
    rw [hc, mul_inv_rev, inv_eq_of_mul_eq_one_right ha, inv_eq_of_mul_eq_one_right hb]
    calc b * (a * b) * b = b * a * (b * b) := by group
      _ = b * a := by rw [hb, mul_one]
  have key : ∀ n : ℕ, b * c ^ n * b = (c ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => simp [hb]
    | succ n ih =>
      calc b * c ^ (n + 1) * b = b * c ^ n * 1 * c * b := by rw [pow_succ]; group
        _ = b * c ^ n * (b * b) * c * b := by rw [hb]
        _ = (b * c ^ n * b) * (b * c * b) := by group
        _ = (c ^ (n + 1))⁻¹ := by rw [ih, hbcb, ← mul_inv_rev, ← pow_succ']
  have ha' : a = c * b := by rw [hc, mul_assoc, hb, mul_one]
  calc c ^ k * a * (c ^ k)⁻¹ = c ^ k * c * (b * (c ^ k)⁻¹) := by rw [ha']; group
    _ = c ^ k * c * (b * (b * c ^ k * b)) := by rw [key]
    _ = c ^ k * c * ((b * b) * c ^ k * b) := by group
    _ = c ^ (2 * k + 1) * b := by
        rw [hb, one_mul, ← mul_assoc, ← pow_succ, ← pow_add]
        ring_nf
    _ = b := by rw [hk, one_mul]

theorem eq_one_of_trivial_on_quotient {C : Type*} [Group C] (Z : Subgroup C)
    (hZ : Z ≤ Subgroup.center C) (hperf : commutator C = ⊤) (β : MulAut C)
    (hβ : ∀ c : C, c⁻¹ * β c ∈ Z) : β = 1 := by
  have hcomm : ∀ x ∈ Z, ∀ g : C, g * x = x * g := fun x hx g =>
    Subgroup.mem_center_iff.1 (hZ hx) g
  let δ : C →* Z :=
    { toFun := fun c => ⟨c⁻¹ * β c, hβ c⟩
      map_one' := by simp
      map_mul' := fun c d => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, map_mul, mul_inv_rev]
        have h := hcomm _ (hβ c) d⁻¹
        calc d⁻¹ * c⁻¹ * (β c * β d) = d⁻¹ * (c⁻¹ * β c) * β d := by group
          _ = (c⁻¹ * β c) * d⁻¹ * β d := by rw [h]
          _ = c⁻¹ * β c * (d⁻¹ * β d) := by group }
  have hab : ∀ x y : Z, x * y = y * x := fun x y =>
    Subtype.ext (hcomm _ y.2 _)
  have hker : commutator C ≤ δ.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    rw [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv,
      hab (δ g₁) (δ g₂)]
    group
  ext c
  have hc : c ∈ δ.ker := hker (hperf ▸ Subgroup.mem_top c)
  rw [MonoidHom.mem_ker] at hc
  have := congrArg Subtype.val hc
  simp only [δ, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_one] at this
  rw [MulAut.one_apply]
  exact (inv_mul_eq_one.1 this).symm

theorem perm_eq_of_commute {X ι : Type*} (gens : ι → Equiv.Perm X) (r : X → X)
    (w : X → List ι) (hw : ∀ x, ((w x).map gens).prod (r x) = x) (σ : Equiv.Perm X)
    (hσ : ∀ i, σ * gens i = gens i * σ) (x : X) :
    σ x = ((w x).map gens).prod (σ (r x)) := by
  have hcomm : ∀ L : List ι, σ * (L.map gens).prod = (L.map gens).prod * σ := by
    intro L
    induction L with
    | nil => simp
    | cons i L ih =>
      rw [List.map_cons, List.prod_cons, ← mul_assoc, hσ i, mul_assoc, ih, ← mul_assoc]
  conv_lhs => rw [← hw x]
  rw [← Equiv.Perm.mul_apply, hcomm, Equiv.Perm.mul_apply]

end CFSG.Sporadic.LySchreier
