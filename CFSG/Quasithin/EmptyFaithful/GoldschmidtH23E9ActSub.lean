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

namespace CFSG.Quasithin.E9

section ActSub

variable {W G : Type*} [Group W] [Group G] (ι : W →* G)

@[expose] def ActsAs (vE : Subgroup W) (g : MulAut W) (ρ : G) : Prop :=
  ∀ v ∈ vE, ι (g v) = ρ * ι v * ρ⁻¹

@[expose] def actSub (vE : Subgroup W) (C : Subgroup (MulAut W))
    (hC : ∀ g ∈ C, ∀ w : W, w ∈ vE ↔ g w ∈ vE) (R : Subgroup G) : Subgroup (MulAut W) where
  carrier := {g | g ∈ C ∧ ∃ ρ ∈ R, ActsAs ι vE g ρ}
  one_mem' := ⟨C.one_mem, 1, R.one_mem, fun v _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨haC, ρ₁, hρ₁, ha⟩ ⟨hbC, ρ₂, hρ₂, hb⟩
    refine ⟨C.mul_mem haC hbC, ρ₁ * ρ₂, R.mul_mem hρ₁ hρ₂, fun v hv => ?_⟩
    show ι (a (b v)) = ρ₁ * ρ₂ * ι v * (ρ₁ * ρ₂)⁻¹
    rw [ha (b v) ((hC b hbC v).mp hv), hb v hv]
    group
  inv_mem' := by
    rintro a ⟨haC, ρ, hρ, ha⟩
    refine ⟨C.inv_mem haC, ρ⁻¹, R.inv_mem hρ, fun v hv => ?_⟩
    have hv' : a⁻¹ v ∈ vE := (hC a haC (a⁻¹ v)).mpr (by rw [MulAut.apply_inv_self]; exact hv)
    have h1 := ha (a⁻¹ v) hv'
    rw [MulAut.apply_inv_self] at h1
    calc ι (a⁻¹ v) = ρ⁻¹ * (ρ * ι (a⁻¹ v) * ρ⁻¹) * ρ := by group
      _ = ρ⁻¹ * ι v * ρ⁻¹⁻¹ := by rw [← h1]; group

variable {ι}

theorem ActsAs.pow {vE : Subgroup W} {g : MulAut W} {ρ : G} (hg : ActsAs ι vE g ρ)
    (hst : ∀ w : W, w ∈ vE → g w ∈ vE) (j : ℕ) : ActsAs ι vE (g ^ j) (ρ ^ j) := by
  induction j with
  | zero => exact fun v _ => by simp
  | succ j ih =>
    intro v hv
    show ι ((g ^ j) (g v)) = ρ ^ (j + 1) * ι v * (ρ ^ (j + 1))⁻¹
    rw [ih (g v) (hst v hv), hg v hv, pow_succ]
    group

theorem actSub_conj {vE : Subgroup W} {C : Subgroup (MulAut W)}
    {hC : ∀ g ∈ C, ∀ w : W, w ∈ vE ↔ g w ∈ vE} {R : Subgroup G} {c : MulAut W} (hc : c ∈ C)
    {γ : G} (hγ : ∀ w : W, ι (c w) = γ * ι w * γ⁻¹) (hγR : ∀ ρ ∈ R, γ * ρ * γ⁻¹ ∈ R)
    {g : MulAut W} (hg : g ∈ actSub ι vE C hC R) : c * g * c⁻¹ ∈ actSub ι vE C hC R := by
  obtain ⟨hgC, ρ, hρ, hgρ⟩ := hg
  refine ⟨C.mul_mem (C.mul_mem hc hgC) (C.inv_mem hc), γ * ρ * γ⁻¹, hγR ρ hρ, fun v hv => ?_⟩
  have hv' : c⁻¹ v ∈ vE := (hC c hc (c⁻¹ v)).mpr (by rw [MulAut.apply_inv_self]; exact hv)
  show ι (c (g (c⁻¹ v))) = γ * ρ * γ⁻¹ * ι v * (γ * ρ * γ⁻¹)⁻¹
  have h1 := hγ (c⁻¹ v)
  rw [MulAut.apply_inv_self] at h1
  rw [hγ, hgρ _ hv']
  have h2 : ι (c⁻¹ v) = γ⁻¹ * ι v * γ := by
    calc ι (c⁻¹ v) = γ⁻¹ * (γ * ι (c⁻¹ v) * γ⁻¹) * γ := by group
      _ = γ⁻¹ * ι v * γ := by rw [← h1]
  rw [h2]
  group

theorem trivial_of_odd_acts_two {vE : Subgroup W} {R : Subgroup G} (hR : IsPGroup 2 R)
    (hι : Function.Injective ι) {h : MulAut W} {ρ : G} (hρ : ρ ∈ R) (hact : ActsAs ι vE h ρ)
    (hst : ∀ w : W, w ∈ vE → h w ∈ vE) {m : ℕ} (hm : Odd m) (hhm : h ^ m = 1) :
    ∀ v ∈ vE, h v = v := by
  obtain ⟨j, hj⟩ := hR ⟨ρ, hρ⟩
  have hρj : ρ ^ (2 ^ (j + 1)) = 1 := by
    have h1 : ρ ^ (2 ^ j) = 1 := by simpa using congrArg Subtype.val hj
    rw [pow_succ, pow_mul, h1, one_pow]
  have hpow := hact.pow hst m
  have hcomm : ∀ v ∈ vE, Commute (ρ ^ m) (ι v) := by
    intro v hv
    have h1 := hpow v hv
    rw [hhm] at h1
    have h2 : ι v = ρ ^ m * ι v * (ρ ^ m)⁻¹ := by simpa using h1
    exact mul_inv_eq_iff_eq_mul.mp h2.symm
  have hcop : Nat.Coprime m (2 ^ (j + 1)) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hm)
  obtain ⟨s, -, hs⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop
    (Nat.one_lt_pow (Nat.succ_ne_zero j) (by norm_num))
  have hρeq : ρ = (ρ ^ m) ^ s := by
    rw [← pow_mul, pow_eq_pow_mod _ hρj, hs, pow_one]
  intro v hv
  apply hι
  have hc : Commute ρ (ι v) := by
    rw [hρeq]
    exact (hcomm v hv).pow_left s
  rw [hact v hv]
  exact mul_inv_eq_iff_eq_mul.mpr hc.eq

theorem isPGroup_actSub [Finite W] (hι : Function.Injective ι) {vE : Subgroup W}
    {C : Subgroup (MulAut W)} {hC : ∀ g ∈ C, ∀ w : W, w ∈ vE ↔ g w ∈ vE} {R : Subgroup G}
    (hR : IsPGroup 2 R)
    (hodd : ∀ h ∈ C, Odd (orderOf h) → (∀ v ∈ vE, h v = v) → h = 1) :
    IsPGroup 2 ↥(actSub ι vE C hC R) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [IsPGroup.iff_orderOf]
  rintro ⟨g, hg⟩
  obtain ⟨hgC, ρ, hρ, hgρ⟩ := id hg
  have hpos : 0 < orderOf g := orderOf_pos g
  obtain ⟨k, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd hpos.ne'
  refine ⟨k, ?_⟩
  rw [Subgroup.orderOf_mk]
  have hhC : g ^ (2 ^ k) ∈ C := C.pow_mem hgC _
  have hord : orderOf (g ^ (2 ^ k)) = m := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) ⟨m, hn⟩, hn]
    exact Nat.mul_div_cancel_left m (pow_pos two_pos k)
  have hhm : (g ^ (2 ^ k)) ^ m = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one _
  have hact : ActsAs ι vE (g ^ (2 ^ k)) (ρ ^ (2 ^ k)) :=
    hgρ.pow (fun w hw => (hC g hgC w).mp hw) _
  have htriv := trivial_of_odd_acts_two hR hι (R.pow_mem hρ _) hact
    (fun w hw => (hC _ hhC w).mp hw) hm hhm
  have h1 : g ^ (2 ^ k) = 1 := hodd _ hhC (hord ▸ hm) htriv
  rw [h1, orderOf_one] at hord
  rw [hn, ← hord, mul_one]

end ActSub

end CFSG.Quasithin.E9
