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

namespace CFSG.RankThree.PartOne.KE

theorem commutator_le_ker_of_mul_comm {G Q : Type*} [Group G] [Group Q] (f : G →* Q)
    (hQ : ∀ a b : Q, a * b = b * a) : commutator G ≤ f.ker := by
  rw [commutator_def, Subgroup.commutator_le]
  intro g₁ _ g₂ _
  rw [MonoidHom.mem_ker, map_commutatorElement]
  exact Commute.commutator_eq (hQ _ _)

theorem mul_comm_of_card_le_three {Q : Type*} [Group Q] (h0 : 0 < Nat.card Q)
    (h3 : Nat.card Q ≤ 3) (a b : Q) : a * b = b * a := by
  have : Finite Q := Nat.finite_of_card_ne_zero h0.ne'
  rcases (show Nat.card Q = 1 ∨ Nat.card Q = 2 ∨ Nat.card Q = 3 by omega) with h | h | h
  · have : Subsingleton Q := Finite.card_le_one_iff_subsingleton.1 h.le
    exact Subsingleton.elim _ _
  · have : Fact (Nat.Prime (Nat.card Q)) := ⟨by rw [h]; exact Nat.prime_two⟩
    have := isCyclic_of_prime_card (α := Q) (p := Nat.card Q) rfl
    exact (IsCyclic.commGroup : CommGroup Q).mul_comm a b
  · have : Fact (Nat.Prime (Nat.card Q)) := ⟨by rw [h]; exact Nat.prime_three⟩
    have := isCyclic_of_prime_card (α := Q) (p := Nat.card Q) rfl
    exact (IsCyclic.commGroup : CommGroup Q).mul_comm a b

theorem commutator_eq_top_iff {X : Type*} [Group X] (P : Subgroup X) :
    commutator P = ⊤ ↔ ⁅P, P⁆ = P := by
  have h2 : (⊤ : Subgroup P).map P.subtype = P := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have h1 : ⁅(⊤ : Subgroup P).map P.subtype, (⊤ : Subgroup P).map P.subtype⁆ =
      Subgroup.map P.subtype ⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ :=
    (Subgroup.map_commutator (⊤ : Subgroup P) (⊤ : Subgroup P) P.subtype).symm
  rw [h2] at h1
  constructor
  · intro h
    rw [h1, ← commutator_def, h, h2]
  · intro h
    rw [h] at h1
    have h3 : Subgroup.map P.subtype (commutator P) = Subgroup.map P.subtype ⊤ := by
      rw [h2, commutator_def, ← h1]
    exact Subgroup.map_injective P.subtype_injective h3

theorem le_of_perfect_of_index_le_three {X : Type*} [Group X] (N : Subgroup X) [N.Normal]
    (hN0 : 0 < N.index) (hN3 : N.index ≤ 3) (P : Subgroup X) (hP : ⁅P, P⁆ = P) : P ≤ N := by
  have hcard : Nat.card (X ⧸ N) = N.index := rfl
  have hcomm : ∀ a b : X ⧸ N, a * b = b * a :=
    mul_comm_of_card_le_three (by rw [hcard]; exact hN0) (by rw [hcard]; exact hN3)
  have hle : commutator X ≤ (QuotientGroup.mk' N).ker := commutator_le_ker_of_mul_comm _ hcomm
  have hPc : P ≤ commutator X := by
    calc P = ⁅P, P⁆ := hP.symm
      _ ≤ ⁅(⊤ : Subgroup X), ⊤⁆ := Subgroup.commutator_mono le_top le_top
      _ = commutator X := (commutator_def X).symm
  intro x hx
  have h := hle (hPc hx)
  rwa [QuotientGroup.ker_mk'] at h

theorem solvable_normal_centralizes_of_perfect {D : Type*} [Group D] (P : Subgroup D)
    [P.Normal] (hperf : ⁅P, P⁆ = P)
    (hsol : ∀ N : Subgroup D, N ≤ P → (∀ x ∈ P, ∀ n ∈ N, x * n * x⁻¹ ∈ N) →
      Group.IsSolvable N → ∀ n ∈ N, ∀ x ∈ P, n * x = x * n)
    (V : Subgroup D) [hVn : V.Normal] [hV : Group.IsSolvable V] :
    ∀ v ∈ V, ∀ x ∈ P, v * x = x * v := by
  have hVPnorm : ∀ x ∈ P, ∀ n ∈ V ⊓ P, x * n * x⁻¹ ∈ V ⊓ P := fun x _ n hn =>
    ⟨hVn.conj_mem n hn.1 x, (inferInstance : P.Normal).conj_mem n hn.2 x⟩
  have hVPsol : Group.IsSolvable (V ⊓ P : Subgroup D) :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion (inf_le_left : V ⊓ P ≤ V))
      (Subgroup.inclusion_injective _)
  have hcentral := hsol (V ⊓ P) inf_le_right hVPnorm hVPsol
  have hVc : ∀ v ∈ V, ∀ x ∈ P, v * x = x * v := by
    intro v hv
    have hmem : ∀ x : P, (v * x * v⁻¹ * (x : D)⁻¹) ∈ V ⊓ P := fun x => by
      refine ⟨?_, ?_⟩
      · have h1 : (x : D) * v⁻¹ * (x : D)⁻¹ ∈ V := hVn.conj_mem v⁻¹ (V.inv_mem hv) x
        have : v * x * v⁻¹ * (x : D)⁻¹ = v * ((x : D) * v⁻¹ * (x : D)⁻¹) := by group
        rw [this]
        exact V.mul_mem hv h1
      · have h1 : v * x * v⁻¹ ∈ P := (inferInstance : P.Normal).conj_mem x x.2 v
        exact P.mul_mem h1 (P.inv_mem x.2)
    have hxw : ∀ x y : P, (x : D)⁻¹ * (v * y * v⁻¹ * (y : D)⁻¹) =
        (v * y * v⁻¹ * (y : D)⁻¹) * (x : D)⁻¹ := fun x y => by
      have h := hcentral _ (hmem y) (x : D) x.2
      calc (x : D)⁻¹ * (v * y * v⁻¹ * (y : D)⁻¹)
          = (x : D)⁻¹ * ((v * y * v⁻¹ * (y : D)⁻¹) * x) * (x : D)⁻¹ := by group
        _ = (x : D)⁻¹ * (x * (v * y * v⁻¹ * (y : D)⁻¹)) * (x : D)⁻¹ := by rw [h]
        _ = (v * y * v⁻¹ * (y : D)⁻¹) * (x : D)⁻¹ := by group
    let φ : P →* Subgroup.center P :=
      { toFun := fun x => ⟨⟨v * x * v⁻¹ * (x : D)⁻¹, (hmem x).2⟩, by
          rw [Subgroup.mem_center_iff]
          intro g
          exact Subtype.ext (hcentral _ (hmem x) (g : D) g.2).symm⟩
        map_one' := by
          apply Subtype.ext
          apply Subtype.ext
          simp
        map_mul' := fun x y => by
          apply Subtype.ext
          apply Subtype.ext
          change v * ((x : D) * (y : D)) * v⁻¹ * ((x : D) * (y : D))⁻¹ =
            (v * x * v⁻¹ * (x : D)⁻¹) * (v * y * v⁻¹ * (y : D)⁻¹)
          calc v * ((x : D) * (y : D)) * v⁻¹ * ((x : D) * (y : D))⁻¹
              = (v * x * v⁻¹) * (v * y * v⁻¹ * (y : D)⁻¹) * (x : D)⁻¹ := by group
            _ = (v * x * v⁻¹) * ((x : D)⁻¹ * (v * y * v⁻¹ * (y : D)⁻¹)) := by rw [mul_assoc,
                ← hxw x y]
            _ = (v * x * v⁻¹ * (x : D)⁻¹) * (v * y * v⁻¹ * (y : D)⁻¹) := by group }
    have hker : commutator P ≤ φ.ker := commutator_le_ker_of_mul_comm φ fun a b =>
      Subtype.ext (Subgroup.mem_center_iff.1 b.2 (a : P))
    rw [(commutator_eq_top_iff P).2 hperf] at hker
    intro x hx
    have h1 : φ ⟨x, hx⟩ = 1 := MonoidHom.mem_ker.1 (hker (Subgroup.mem_top _))
    have h2 := congrArg (fun z : Subgroup.center P => ((z : P) : D)) h1
    change v * x * v⁻¹ * (x : D)⁻¹ = 1 at h2
    have h3 : v * x * v⁻¹ = x := by
      have := congrArg (· * (x : D)) h2
      simpa using this
    calc v * x = (v * x * v⁻¹) * v := by group
      _ = x * v := by rw [h3]
  exact hVc

theorem isCyclic_of_solvable_normal_of_quasisimple {D : Type*} [Group D] (P Z : Subgroup D)
    [P.Normal] (hperf : ⁅P, P⁆ = P)
    (hsol : ∀ N : Subgroup D, N ≤ P → (∀ x ∈ P, ∀ n ∈ N, x * n * x⁻¹ ∈ N) →
      Group.IsSolvable N → ∀ n ∈ N, ∀ x ∈ P, n * x = x * n)
    [hZ : IsCyclic Z] (hcent : ∀ y : D, (∀ x ∈ P, y * x = x * y) → y ∈ Z)
    (V : Subgroup D) [hVn : V.Normal] [hV : Group.IsSolvable V] : IsCyclic V := by
  have hVc := solvable_normal_centralizes_of_perfect P hperf hsol V
  have hVZ : V ≤ Z := fun v hv => hcent v (hVc v hv)
  exact isCyclic_of_injective (Subgroup.inclusion hVZ) (Subgroup.inclusion_injective hVZ)

end CFSG.RankThree.PartOne.KE
