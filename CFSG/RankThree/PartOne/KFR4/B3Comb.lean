module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.RankThree.PartOne.KFR4

inductive Root : Type
  | s1 | s2 | s3 | m12 | m13 | m23 | p12 | p13 | p23
  deriving DecidableEq

instance : Fintype Root :=
  ⟨{.s1, .s2, .s3, .m12, .m13, .m23, .p12, .p13, .p23}, fun x => by cases x <;> simp⟩

@[expose] def Root.IsShort : Root → Prop
  | .s1 => True | .s2 => True | .s3 => True
  | _ => False

instance (ρ : Root) : Decidable ρ.IsShort := by
  cases ρ <;> simp only [Root.IsShort] <;> infer_instance

@[expose] def Root.vec : Root → Fin 3 → ℤ
  | .s1 => ![1, 0, 0] | .s2 => ![0, 1, 0] | .s3 => ![0, 0, 1]
  | .m12 => ![1, -1, 0] | .m13 => ![1, 0, -1] | .m23 => ![0, 1, -1]
  | .p12 => ![1, 1, 0] | .p13 => ![1, 0, 1] | .p23 => ![0, 1, 1]

@[expose] def Root.cor : Root → Fin 3 → ℤ
  | .s1 => ![2, 0, 0] | .s2 => ![0, 2, 0] | .s3 => ![0, 0, 2]
  | .m12 => ![1, -1, 0] | .m13 => ![1, 0, -1] | .m23 => ![0, 1, -1]
  | .p12 => ![1, 1, 0] | .p13 => ![1, 0, 1] | .p23 => ![0, 1, 1]

@[expose] def Root.nsq : Root → ℤ
  | .s1 => 1 | .s2 => 1 | .s3 => 1
  | _ => 2

@[expose] def dotZ (a b : Fin 3 → ℤ) : ℤ := a 0 * b 0 + a 1 * b 1 + a 2 * b 2

theorem dotZ_vec_cor (ρ : Root) : dotZ ρ.vec ρ.cor = 2 := by
  cases ρ <;> simp [Root.vec, Root.cor, dotZ]

theorem dotZ_vec_vec (ρ : Root) : dotZ ρ.vec ρ.vec = ρ.nsq := by
  cases ρ <;> simp [Root.vec, Root.nsq, dotZ]

theorem gram_mem (ρ ρ' : Root) (h : ρ ≠ ρ') :
    (ρ.nsq * ρ'.nsq - (dotZ ρ.vec ρ'.vec) ^ 2 : ℤ) ∈ ({1, 2, 3, 4} : Set ℤ) := by
  cases ρ <;> cases ρ' <;> simp [Root.nsq, Root.vec, dotZ] at h ⊢

section Reflections

variable (p : ℕ)

abbrev Vec : Type := Fin 3 → ZMod p

@[expose] def Root.vecp (ρ : Root) : Vec p := fun k => ((ρ.vec k : ℤ) : ZMod p)

@[expose] def Root.corp (ρ : Root) : Vec p := fun k => ((ρ.cor k : ℤ) : ZMod p)

theorem dot_vecp_corp (ρ : Root) : ρ.vecp p ⬝ᵥ ρ.corp p = 2 := by
  have h := dotZ_vec_cor ρ
  have h' : ((dotZ ρ.vec ρ.cor : ℤ) : ZMod p) = 2 := by rw [h]; norm_num
  rw [← h']
  simp [dotZ, dotProduct, Fin.sum_univ_three, Root.vecp, Root.corp]

@[expose] def reflEnd (ρ : Root) : Module.End (ZMod p) (Vec p) where
  toFun x := x - (ρ.vecp p ⬝ᵥ x) • ρ.corp p
  map_add' x y := by
    simp only [dotProduct_add, add_smul]
    abel
  map_smul' c x := by
    simp only [dotProduct_smul, smul_eq_mul, RingHom.id_apply, smul_sub, smul_smul]

theorem reflEnd_apply (ρ : Root) (x : Vec p) :
    reflEnd p ρ x = x - (ρ.vecp p ⬝ᵥ x) • ρ.corp p := rfl

theorem reflEnd_involutive (ρ : Root) : Function.Involutive (reflEnd p ρ) := by
  intro x
  rw [reflEnd_apply, reflEnd_apply, dotProduct_sub, dotProduct_smul, dot_vecp_corp, smul_eq_mul]
  module

@[expose] def reflLin (ρ : Root) : Vec p ≃ₗ[ZMod p] Vec p :=
  LinearEquiv.ofInvolutive (reflEnd p ρ) (reflEnd_involutive p ρ)

theorem reflLin_apply (ρ : Root) (x : Vec p) :
    reflLin p ρ x = x - (ρ.vecp p ⬝ᵥ x) • ρ.corp p := rfl

theorem reflLin_apply_coord (ρ : Root) (x : Vec p) (k : Fin 3) :
    reflLin p ρ x k = x k - (ρ.vecp p ⬝ᵥ x) * ρ.corp p k := by
  rw [reflLin_apply]
  simp

theorem reflLin_single (ρ : Root) (k : Fin 3) :
    reflLin p ρ (Pi.single k 1) = Pi.single k 1 - (ρ.vecp p k) • ρ.corp p := by
  rw [reflLin_apply, dotProduct_single, mul_one]

@[expose] def Root.perm : Root → Equiv.Perm (Fin 3)
  | .s1 | .s2 | .s3 => 1
  | .m12 | .p12 => Equiv.swap 0 1
  | .m13 | .p13 => Equiv.swap 0 2
  | .m23 | .p23 => Equiv.swap 1 2

@[expose] def Root.sgn : Root → Fin 3 → ℤ
  | .s1 => ![-1, 1, 1] | .s2 => ![1, -1, 1] | .s3 => ![1, 1, -1]
  | .m12 | .m13 | .m23 => ![1, 1, 1]
  | .p12 => ![-1, -1, 1] | .p13 => ![-1, 1, -1] | .p23 => ![1, -1, -1]

theorem reflLin_single_eq (ρ : Root) (k : Fin 3) :
    reflLin p ρ (Pi.single k 1) = ((ρ.sgn k : ℤ) : ZMod p) • Pi.single (ρ.perm k) 1 := by
  rw [reflLin_single]
  cases ρ <;> fin_cases k <;> (funext j; fin_cases j <;> simp [Root.vecp, Root.corp, Root.vec,
    Root.cor, Root.perm, Root.sgn, Equiv.swap_apply_def] <;> norm_num)

instance [NeZero p] : Finite (Vec p ≃ₗ[ZMod p] Vec p) :=
  Finite.of_injective (fun g : Vec p ≃ₗ[ZMod p] Vec p => (g : Vec p → Vec p))
    fun _ _ h => LinearEquiv.ext (congrFun h)

theorem neg_one_ne_one (hp : 3 ≤ p) : (-1 : ZMod p) ≠ 1 := by
  intro h
  have h2 : ((2 : ℕ) : ZMod p) = 0 := by
    have : (1 : ZMod p) + 1 = 0 := by
      calc (1 : ZMod p) + 1 = 1 + -1 * (-1) := by ring
        _ = 1 + -1 * 1 := by rw [h]
        _ = 0 := by ring
    simpa [one_add_one_eq_two] using this
  rw [ZMod.natCast_eq_zero_iff] at h2
  have := Nat.le_of_dvd (by norm_num) h2
  omega

end Reflections

section Signed

variable (p : ℕ)

@[expose] def spGroup : Subgroup (Vec p ≃ₗ[ZMod p] Vec p) where
  carrier := {g | ∃ (π : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod p), (∀ k, ε k = 1 ∨ ε k = -1) ∧
    ∀ k, g (Pi.single k 1) = ε k • Pi.single (π k) 1}
  mul_mem' := by
    rintro g g' ⟨π, ε, hε, hg⟩ ⟨π', ε', hε', hg'⟩
    refine ⟨π * π', fun k => ε' k * ε (π' k), fun k => ?_, fun k => ?_⟩
    · show ε' k * ε (π' k) = 1 ∨ ε' k * ε (π' k) = -1
      rcases hε' k with h | h <;> rcases hε (π' k) with h' | h'
      · left; rw [h, h']; ring
      · right; rw [h, h']; ring
      · right; rw [h, h']; ring
      · left; rw [h, h']; ring
    · rw [LinearEquiv.mul_apply, hg', map_smul, hg, smul_smul]
      rfl
  one_mem' := ⟨1, fun _ => 1, fun _ => Or.inl rfl, fun k => by simp⟩
  inv_mem' := by
    rintro g ⟨π, ε, hε, hg⟩
    refine ⟨π⁻¹, fun k => ε (π⁻¹ k), fun k => hε _, fun k => ?_⟩
    show g.symm _ = _
    rw [LinearEquiv.symm_apply_eq, map_smul]
    have h1 := hg (π⁻¹ k)
    have h2 : π (π⁻¹ k) = k := by simp
    rw [h2] at h1
    show Pi.single k 1 = ε (π⁻¹ k) • g (Pi.single (π⁻¹ k) 1)
    rw [h1, smul_smul]
    rcases hε (π⁻¹ k) with h | h <;> rw [h] <;> norm_num

theorem card_spGroup_le [NeZero p] (hp : 3 ≤ p) : Nat.card (spGroup p) ≤ 48 := by
  classical
  have hcard : Nat.card (Equiv.Perm (Fin 3) × (Fin 3 → Bool)) = 48 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  rw [← hcard]
  have hne := neg_one_ne_one p hp
  let P : (Vec p ≃ₗ[ZMod p] Vec p) → Equiv.Perm (Fin 3) × (Fin 3 → Bool) → Prop := fun g q =>
    ∃ ε : Fin 3 → ZMod p, (∀ k, ε k = 1 ∨ ε k = -1) ∧ (∀ k, decide (ε k = -1) = q.2 k) ∧
      ∀ k, g (Pi.single k 1) = ε k • Pi.single (q.1 k) 1
  have hex : ∀ g : spGroup p, ∃ q, P g.1 q := by
    rintro ⟨g, π, ε, hε, hg⟩
    exact ⟨(π, fun k => decide (ε k = -1)), ε, hε, fun k => rfl, hg⟩
  refine Nat.card_le_card_of_injective (fun g => (hex g).choose) ?_
  intro g g' hgg'
  have h1 := (hex g).choose_spec
  have h2 := (hex g').choose_spec
  have hgg'' : (hex g).choose = (hex g').choose := hgg'
  rw [← hgg''] at h2
  obtain ⟨ε, hε, hεs, hg⟩ := h1
  obtain ⟨ε', hε', hεs', hg'⟩ := h2
  have hεeq : ∀ k, ε k = ε' k := by
    intro k
    have := (hεs k).trans (hεs' k).symm
    rcases hε k with h | h <;> rcases hε' k with h' | h'
    · rw [h, h']
    · rw [h, h'] at this
      simp [hne.symm] at this
    · rw [h, h'] at this
      simp [hne.symm] at this
    · rw [h, h']
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  refine (Pi.basisFun (ZMod p) (Fin 3)).ext fun k => ?_
  simp only [Pi.basisFun_apply, LinearEquiv.coe_coe]
  rw [hg k, hg' k, hεeq k]

theorem reflLin_mem_spGroup (ρ : Root) : reflLin p ρ ∈ spGroup p := by
  refine ⟨ρ.perm, fun k => ((ρ.sgn k : ℤ) : ZMod p), fun k => ?_, fun k => reflLin_single_eq p ρ k⟩
  cases ρ <;> fin_cases k <;> simp [Root.sgn]

end Signed

section Invariants

variable (p : ℕ)

@[expose] def diagGroup : Subgroup (Vec p ≃ₗ[ZMod p] Vec p) where
  carrier := {g | ∀ k, g (Pi.single k 1) ∈ Submodule.span (ZMod p) {(Pi.single k 1 : Vec p)} ∧
    g.symm (Pi.single k 1) ∈ Submodule.span (ZMod p) {(Pi.single k 1 : Vec p)}}
  mul_mem' := by
    rintro g g' hg hg' k
    obtain ⟨a, b⟩ := hg k
    obtain ⟨a', b'⟩ := hg' k
    refine ⟨?_, ?_⟩
    · obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 a'
      rw [LinearEquiv.mul_apply, ← hc, map_smul]
      exact Submodule.smul_mem _ _ a
    · obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 b
      show g'.symm (g.symm _) ∈ _
      rw [← hc, map_smul]
      exact Submodule.smul_mem _ _ b'
  one_mem' := fun k => ⟨Submodule.subset_span rfl, Submodule.subset_span rfl⟩
  inv_mem' := fun {g} hg k => ⟨(hg k).2, (hg k).1⟩

@[expose] def cubGroup : Subgroup (Vec p ≃ₗ[ZMod p] Vec p) where
  carrier := {g | ∀ x : Vec p, g x 0 * g x 1 * g x 2 = x 0 * x 1 * x 2}
  mul_mem' := fun {g g'} hg hg' x => by
    rw [LinearEquiv.mul_apply, hg, hg']
  one_mem' := fun x => rfl
  inv_mem' := fun {g} hg x => by
    have := hg (g.symm x)
    rw [LinearEquiv.apply_symm_apply] at this
    exact this.symm

theorem reflLin_mem_diagGroup {ρ : Root} (h : ρ.IsShort) : reflLin p ρ ∈ diagGroup p := by
  intro k
  have hs : (reflLin p ρ).symm = reflLin p ρ := rfl
  rw [hs]
  have key : reflLin p ρ (Pi.single k 1) ∈ Submodule.span (ZMod p) {(Pi.single k 1 : Vec p)} := by
    rw [reflLin_single_eq]
    cases ρ <;> simp only [Root.IsShort] at h <;> fin_cases k <;> simp [Root.perm, Root.sgn]
  exact ⟨key, key⟩

theorem not_mem_diagGroup_m12 (hp : 3 ≤ p) : reflLin p Root.m12 ∉ diagGroup p := by
  intro h
  have h0 := (h 0).1
  rw [reflLin_single_eq] at h0
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 h0
  have h01 := congrFun hc 1
  simp [Root.perm, Root.sgn] at h01
  have : Fact (1 < p) := ⟨by omega⟩
  exact zero_ne_one h01

theorem reflLin_mem_cubGroup {ρ : Root} (h : ¬ ρ.IsShort) : reflLin p ρ ∈ cubGroup p := by
  intro x
  cases ρ <;> simp only [Root.IsShort, not_true_eq_false] at h <;>
    simp [reflLin_apply_coord, dotProduct, Fin.sum_univ_three, Root.vecp, Root.corp, Root.vec,
      Root.cor] <;> ring

theorem not_mem_cubGroup_s1 (hp : 3 ≤ p) : reflLin p Root.s1 ∉ cubGroup p := by
  intro h
  have := h (fun _ => 1)
  simp [reflLin_apply_coord, dotProduct, Fin.sum_univ_three, Root.vecp, Root.corp, Root.vec,
    Root.cor] at this
  exact neg_one_ne_one p hp (by linear_combination -this)

end Invariants

section Closure

variable (p : ℕ)

theorem exists_short_of_closure_eq (hp : 3 ≤ p) {J : Set Root}
    (h : Subgroup.closure (reflLin p '' J) = Subgroup.closure (Set.range (reflLin p))) :
    ∃ ρ ∈ J, ρ.IsShort := by
  by_contra hno
  push Not at hno
  have hle : Subgroup.closure (reflLin p '' J) ≤ cubGroup p := by
    rw [Subgroup.closure_le]
    rintro _ ⟨ρ, hρ, rfl⟩
    exact reflLin_mem_cubGroup p (hno ρ hρ)
  have hmem : reflLin p Root.s1 ∈ Subgroup.closure (reflLin p '' J) := by
    rw [h]
    exact Subgroup.subset_closure ⟨Root.s1, rfl⟩
  exact not_mem_cubGroup_s1 p hp (hle hmem)

theorem exists_long_of_closure_eq (hp : 3 ≤ p) {J : Set Root}
    (h : Subgroup.closure (reflLin p '' J) = Subgroup.closure (Set.range (reflLin p))) :
    ∃ ρ ∈ J, ¬ ρ.IsShort := by
  by_contra hno
  push Not at hno
  have hle : Subgroup.closure (reflLin p '' J) ≤ diagGroup p := by
    rw [Subgroup.closure_le]
    rintro _ ⟨ρ, hρ, rfl⟩
    exact reflLin_mem_diagGroup p (hno ρ hρ)
  have hmem : reflLin p Root.m12 ∈ Subgroup.closure (reflLin p '' J) := by
    rw [h]
    exact Subgroup.subset_closure ⟨Root.m12, rfl⟩
  exact not_mem_diagGroup_m12 p hp (hle hmem)

theorem card_closure_refl_le [NeZero p] (hp : 3 ≤ p) :
    Nat.card (Subgroup.closure (Set.range (reflLin p))) ≤ 48 := by
  have hle : Subgroup.closure (Set.range (reflLin p)) ≤ spGroup p := by
    rw [Subgroup.closure_le]
    rintro _ ⟨ρ, rfl⟩
    exact reflLin_mem_spGroup p ρ
  exact (Subgroup.card_le_of_le hle).trans (card_spGroup_le p hp)

theorem dot_vecp_vecp (ρ ρ' : Root) :
    ρ.vecp p ⬝ᵥ ρ'.vecp p = ((dotZ ρ.vec ρ'.vec : ℤ) : ZMod p) := by
  simp [dotZ, dotProduct, Fin.sum_univ_three, Root.vecp]

theorem gram_cast_ne_zero (hp5 : 5 ≤ p) {ρ ρ' : Root} (h : ρ ≠ ρ') :
    (((ρ.nsq * ρ'.nsq - (dotZ ρ.vec ρ'.vec) ^ 2 : ℤ)) : ZMod p) ≠ 0 := by
  intro h0
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
  have hmem := gram_mem ρ ρ' h
  have hle : (p : ℤ) ≤ 4 := by
    rcases hmem with h1 | h1 | h1 | h1 <;> rw [h1] at h0 <;>
      exact (Int.le_of_dvd (by norm_num) h0).trans (by norm_num)
  omega

end Closure

section Action

@[expose] def Root.act : Root → Root → Root
  | .s1, .s1 => .s1
  | .s1, .s2 => .s2
  | .s1, .s3 => .s3
  | .s1, .m12 => .p12
  | .s1, .m13 => .p13
  | .s1, .m23 => .m23
  | .s1, .p12 => .m12
  | .s1, .p13 => .m13
  | .s1, .p23 => .p23
  | .s2, .s1 => .s1
  | .s2, .s2 => .s2
  | .s2, .s3 => .s3
  | .s2, .m12 => .p12
  | .s2, .m13 => .m13
  | .s2, .m23 => .p23
  | .s2, .p12 => .m12
  | .s2, .p13 => .p13
  | .s2, .p23 => .m23
  | .s3, .s1 => .s1
  | .s3, .s2 => .s2
  | .s3, .s3 => .s3
  | .s3, .m12 => .m12
  | .s3, .m13 => .p13
  | .s3, .m23 => .p23
  | .s3, .p12 => .p12
  | .s3, .p13 => .m13
  | .s3, .p23 => .m23
  | .m12, .s1 => .s2
  | .m12, .s2 => .s1
  | .m12, .s3 => .s3
  | .m12, .m12 => .m12
  | .m12, .m13 => .m23
  | .m12, .m23 => .m13
  | .m12, .p12 => .p12
  | .m12, .p13 => .p23
  | .m12, .p23 => .p13
  | .m13, .s1 => .s3
  | .m13, .s2 => .s2
  | .m13, .s3 => .s1
  | .m13, .m12 => .m23
  | .m13, .m13 => .m13
  | .m13, .m23 => .m12
  | .m13, .p12 => .p23
  | .m13, .p13 => .p13
  | .m13, .p23 => .p12
  | .m23, .s1 => .s1
  | .m23, .s2 => .s3
  | .m23, .s3 => .s2
  | .m23, .m12 => .m13
  | .m23, .m13 => .m12
  | .m23, .m23 => .m23
  | .m23, .p12 => .p13
  | .m23, .p13 => .p12
  | .m23, .p23 => .p23
  | .p12, .s1 => .s2
  | .p12, .s2 => .s1
  | .p12, .s3 => .s3
  | .p12, .m12 => .m12
  | .p12, .m13 => .p23
  | .p12, .m23 => .p13
  | .p12, .p12 => .p12
  | .p12, .p13 => .m23
  | .p12, .p23 => .m13
  | .p13, .s1 => .s3
  | .p13, .s2 => .s2
  | .p13, .s3 => .s1
  | .p13, .m12 => .p23
  | .p13, .m13 => .m13
  | .p13, .m23 => .p12
  | .p13, .p12 => .m23
  | .p13, .p13 => .p13
  | .p13, .p23 => .m12
  | .p23, .s1 => .s1
  | .p23, .s2 => .s3
  | .p23, .s3 => .s2
  | .p23, .m12 => .p13
  | .p23, .m13 => .p12
  | .p23, .m23 => .m23
  | .p23, .p12 => .m13
  | .p23, .p13 => .m12
  | .p23, .p23 => .p23

@[expose] def Root.sg : Root → Root → ℤ
  | .s1, .s1 => -1
  | .s1, .s2 => 1
  | .s1, .s3 => 1
  | .s1, .m12 => -1
  | .s1, .m13 => -1
  | .s1, .m23 => 1
  | .s1, .p12 => -1
  | .s1, .p13 => -1
  | .s1, .p23 => 1
  | .s2, .s1 => 1
  | .s2, .s2 => -1
  | .s2, .s3 => 1
  | .s2, .m12 => 1
  | .s2, .m13 => 1
  | .s2, .m23 => -1
  | .s2, .p12 => 1
  | .s2, .p13 => 1
  | .s2, .p23 => -1
  | .s3, .s1 => 1
  | .s3, .s2 => 1
  | .s3, .s3 => -1
  | .s3, .m12 => 1
  | .s3, .m13 => 1
  | .s3, .m23 => 1
  | .s3, .p12 => 1
  | .s3, .p13 => 1
  | .s3, .p23 => 1
  | .m12, .s1 => 1
  | .m12, .s2 => 1
  | .m12, .s3 => 1
  | .m12, .m12 => -1
  | .m12, .m13 => 1
  | .m12, .m23 => 1
  | .m12, .p12 => 1
  | .m12, .p13 => 1
  | .m12, .p23 => 1
  | .m13, .s1 => 1
  | .m13, .s2 => 1
  | .m13, .s3 => 1
  | .m13, .m12 => -1
  | .m13, .m13 => -1
  | .m13, .m23 => -1
  | .m13, .p12 => 1
  | .m13, .p13 => 1
  | .m13, .p23 => 1
  | .m23, .s1 => 1
  | .m23, .s2 => 1
  | .m23, .s3 => 1
  | .m23, .m12 => 1
  | .m23, .m13 => 1
  | .m23, .m23 => -1
  | .m23, .p12 => 1
  | .m23, .p13 => 1
  | .m23, .p23 => 1
  | .p12, .s1 => -1
  | .p12, .s2 => -1
  | .p12, .s3 => 1
  | .p12, .m12 => 1
  | .p12, .m13 => -1
  | .p12, .m23 => -1
  | .p12, .p12 => -1
  | .p12, .p13 => -1
  | .p12, .p23 => -1
  | .p13, .s1 => -1
  | .p13, .s2 => 1
  | .p13, .s3 => -1
  | .p13, .m12 => -1
  | .p13, .m13 => 1
  | .p13, .m23 => 1
  | .p13, .p12 => 1
  | .p13, .p13 => -1
  | .p13, .p23 => -1
  | .p23, .s1 => 1
  | .p23, .s2 => -1
  | .p23, .s3 => -1
  | .p23, .m12 => 1
  | .p23, .m13 => 1
  | .p23, .m23 => 1
  | .p23, .p12 => 1
  | .p23, .p13 => 1
  | .p23, .p23 => -1

variable (p : ℕ)

theorem reflLin_vecp (σ ρ : Root) :
    reflLin p σ (ρ.vecp p) = ((Root.sg σ ρ : ℤ) : ZMod p) • (Root.act σ ρ).vecp p := by
  funext k
  cases σ <;> cases ρ <;> fin_cases k <;>
    simp [reflLin_apply_coord, dotProduct, Fin.sum_univ_three, Root.vecp, Root.corp, Root.vec,
      Root.cor, Root.act, Root.sg] <;> ring

theorem dot_reflLin (σ : Root) (x y : Vec p) : reflLin p σ x ⬝ᵥ reflLin p σ y = x ⬝ᵥ y := by
  cases σ <;> simp [reflLin_apply_coord, dotProduct, Fin.sum_univ_three, Root.vecp, Root.corp,
    Root.vec, Root.cor] <;> ring

theorem act_transitive : ∀ ρ ρ' : Root, (ρ.IsShort ↔ ρ'.IsShort) →
    ∃ σ τ : Root, Root.act σ (Root.act τ ρ) = ρ' := by
  decide

end Action

end CFSG.RankThree.PartOne.KFR4
