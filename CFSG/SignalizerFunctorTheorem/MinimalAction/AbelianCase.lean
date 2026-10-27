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

namespace CFSG.SignalizerFunctorTheorem.MinimalAction

theorem eq_zero_of_mem_commutator_of_fixed
    {V : Type*} [AddCommGroup V] [Finite V] {p : ℕ} (hV : ∃ k : ℕ, Nat.card V = p ^ k)
    {Γ : Type*} [Group Γ] [Finite Γ] (φ : Γ →* AddMonoid.End V) {Q : Subgroup Γ}
    (hQ : Nat.Coprime p (Nat.card Q)) {w : V}
    (hw : w ∈ AddSubgroup.closure {u : V | ∃ b ∈ Q, ∃ v : V, u = φ b v - v})
    (hfix : ∀ b ∈ Q, φ b w = w) : w = 0 := by
  obtain ⟨k, hk⟩ := hV
  have := Fintype.ofFinite Q
  have := Fintype.ofFinite V
  let T : V →+ V :=
    { toFun := fun v => ∑ b : Q, φ b v
      map_zero' := by simp
      map_add' := fun x y => by simp [Finset.sum_add_distrib] }
  have hT : ∀ v, T v = ∑ b : Q, φ b v := fun v => rfl
  have hker : AddSubgroup.closure {u : V | ∃ b ∈ Q, ∃ v : V, u = φ b v - v} ≤ T.ker := by
    rw [AddSubgroup.closure_le]
    rintro u ⟨b₀, hb₀, v, rfl⟩
    rw [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub, hT, hT, sub_eq_zero]
    exact Fintype.sum_equiv (Equiv.mulRight ⟨b₀, hb₀⟩) _ _ (fun b => by simp [map_mul])
  have hTw : T w = 0 := hker hw
  have h1 : Nat.card Q • w = 0 := by
    rw [← hTw, hT, Nat.card_eq_fintype_card]
    have : ∀ b : Q, φ b w = w := fun b => hfix b b.2
    simp [this]
  have h2 : p ^ k • w = 0 := by
    rw [← hk, Nat.card_eq_fintype_card]
    exact card_nsmul_eq_zero
  exact AddMonoid.addOrderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (hQ.pow_left k) (addOrderOf_dvd_of_nsmul_eq_zero h2)
      (addOrderOf_dvd_of_nsmul_eq_zero h1))

theorem abelian_case {V : Type*} [AddCommGroup V] [Finite V] {p : ℕ} (hp : p.Prime)
    (hV : ∃ k : ℕ, Nat.card V = p ^ k)
    {Γ : Type*} [Group Γ] [Finite Γ] (φ : Γ →* AddMonoid.End V) {P Q : Subgroup Γ}
    (hP : IsPGroup p P) (hQ : Nat.Coprime p (Nat.card Q))
    (hPQ : P ≤ Subgroup.normalizer (Q : Set Γ))
    (hfix : ∀ v : V, (∀ a ∈ P, φ a v = v) → ∀ b ∈ Q, φ b v = v) :
    ∀ b ∈ Q, ∀ v : V, φ b v = v := by
  have : Fact p.Prime := ⟨hp⟩
  set W : AddSubgroup V := AddSubgroup.closure {u : V | ∃ b ∈ Q, ∃ v : V, u = φ b v - v}
  have hmem : ∀ b ∈ Q, ∀ v : V, φ b v - v ∈ W := fun b hb v =>
    AddSubgroup.subset_closure ⟨b, hb, v, rfl⟩
  have hinv : ∀ a ∈ P, ∀ w ∈ W, φ a w ∈ W := by
    intro a ha w hw
    induction hw using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨b, hb, v, rfl⟩ := hx
      have h1 : φ (a * b * a⁻¹) * φ a = φ a * φ b := by
        rw [← map_mul, ← map_mul, mul_assoc, inv_mul_cancel, mul_one]
      have h2 : φ a (φ b v - v) = φ (a * b * a⁻¹) (φ a v) - φ a v := by
        rw [map_sub]
        exact congrArg (· - φ a v) (DFunLike.congr_fun h1 v).symm
      rw [h2]
      exact hmem _ ((Subgroup.mem_normalizer_iff.mp (hPQ ha) b).mp hb) _
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | neg x _ hx => rw [map_neg]; exact neg_mem hx
  let _ : MulAction P W :=
    { smul := fun a w => ⟨φ a w, hinv a a.2 w w.2⟩
      one_smul := fun w => Subtype.ext (by
        show φ ((1 : P) : Γ) (w : V) = w
        simp)
      mul_smul := fun a a' w => Subtype.ext (by
        show φ ((a * a' : P) : Γ) (w : V) = φ a (φ a' w)
        simp [map_mul]) }
  have hsmul : ∀ (a : P) (w : W), ((a • w : W) : V) = φ a w := fun _ _ => rfl
  have hfixed : ∀ w : MulAction.fixedPoints P W, ((w : W) : V) = 0 := by
    intro w
    have hw : ∀ a ∈ P, φ a ((w : W) : V) = ((w : W) : V) := fun a ha =>
      congrArg Subtype.val (w.2 ⟨a, ha⟩)
    exact eq_zero_of_mem_commutator_of_fixed hV φ hQ (w : W).2 (hfix _ hw)
  have hcard : Nat.card (MulAction.fixedPoints P W) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun x y => ?_⟩, ⟨⟨0, ?_⟩⟩⟩
    · exact Subtype.ext (Subtype.ext ((hfixed x).trans (hfixed y).symm))
    · exact fun a => Subtype.ext (by simp [hsmul])
  obtain ⟨k, hk⟩ := hV
  have hmod := hP.card_modEq_card_fixedPoints W
  rw [hcard] at hmod
  have hdvd : Nat.card W ∣ p ^ k := by
    rw [← hk]
    exact AddSubgroup.card_addSubgroup_dvd_card W
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  have hj0 : j = 0 := by
    by_contra hne
    exact hp.not_dvd_one ((hmod.dvd_iff dvd_rfl).mp (hj ▸ dvd_pow_self p hne))
  have hWbot : W = ⊥ := AddSubgroup.card_eq_one.mp (by rw [hj, hj0, pow_zero])
  intro b hb v
  have h := hmem b hb v
  rw [hWbot, AddSubgroup.mem_bot, sub_eq_zero] at h
  exact h

end CFSG.SignalizerFunctorTheorem.MinimalAction
