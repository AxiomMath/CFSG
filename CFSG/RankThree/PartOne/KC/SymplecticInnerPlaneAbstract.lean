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
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
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

namespace CFSG.RankThree.PartOne.KCSymplectic

open Module

section Scalar

variable {E W F : Type*} [Field E] [AddCommGroup W] [Module E W] [Group F]

theorem det_toModuleAut (c : Eˣ) [FiniteDimensional E W] :
    LinearEquiv.det (DistribMulAction.toModuleAut E W c) = c ^ finrank E W := by
  refine Units.ext ?_
  rw [LinearEquiv.coe_det, Units.val_pow_eq_pow_val]
  have : ((DistribMulAction.toModuleAut E W c : W ≃ₗ[E] W) : W →ₗ[E] W) = (c : E) • 1 := by
    ext w
    rfl
  rw [this, LinearMap.det_smul, (LinearMap.det : Module.End E W →* E).map_one, mul_one]

theorem toModuleAut_comm (c : Eˣ) (g : W ≃ₗ[E] W) :
    DistribMulAction.toModuleAut E W c * g = g * DistribMulAction.toModuleAut E W c := by
  ext w
  change (c : E) • g w = g ((c : E) • w)
  rw [map_smul]

theorem exists_scalar_factor [FiniteDimensional E W] (ψ : F →* (W ≃ₗ[E] W))
    (hψ : Function.Injective ψ) {p : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ finrank E W)
    (hscal : ∀ c : Eˣ, c ^ p = 1 → DistribMulAction.toModuleAut E W c ∈ ψ.range)
    {t : F} (ht : t ^ p = 1) :
    ∃ s : F, (∀ g : F, s * g = g * s) ∧ s ^ p = 1 ∧
      LinearEquiv.det (ψ s) = LinearEquiv.det (ψ t) := by
  set m := finrank E W with hm
  set δ : Eˣ := LinearEquiv.det (ψ t) with hδ
  have hδu : δ ^ p = 1 := by
    rw [hδ, ← map_pow, ← map_pow, ht, map_one, map_one]
  have hcop : m.Coprime p := (hp.coprime_iff_not_dvd.mpr hpm).symm
  obtain ⟨b, -, hb⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  have hc : (δ ^ b) ^ p = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hδu, one_pow]
  have hcm : (δ ^ b) ^ m = δ := by
    rw [← pow_mul, mul_comm b m]
    have h1 : m * b = p * (m * b / p) + 1 := by
      have := Nat.div_add_mod (m * b) p
      omega
    rw [h1, pow_add, pow_mul, hδu, one_pow, one_mul, pow_one]
  obtain ⟨s, hs⟩ := hscal (δ ^ b) hc
  refine ⟨s, fun g => ?_, ?_, ?_⟩
  · apply hψ
    rw [map_mul, map_mul, hs]
    exact toModuleAut_comm _ _
  · apply hψ
    rw [map_pow, hs, ← map_pow, hc, map_one, map_one]
  · rw [hs, det_toModuleAut, ← hm, hcm]

end Scalar

section Pi

variable {Γ ι : Type*} [Group Γ] [Finite ι]

theorem exists_factorization_of_family (H : ι → Subgroup Γ)
    (hcomm : Pairwise fun i j => ∀ x y : Γ, x ∈ H i → y ∈ H j → Commute x y)
    (hindep : iSupIndep H) {p : ℕ} (KK WW : Subgroup Γ)
    (hloc : ∀ i, ∀ t ∈ H i, t ^ p = 1 → ∃ s k w : Γ, s ∈ H i ∧ k ∈ H i ∧ w ∈ H i ∧ k ∈ KK ∧
      w ∈ WW ∧ t = s * k * w ∧ (∀ g ∈ H i, s * g = g * s) ∧ s ^ p = 1 ∧ k ^ p = 1 ∧ w ^ p = 1)
    {v : Γ} (hv : v ∈ ⨆ i, H i) (hvp : v ^ p = 1) :
    ∃ z k w : Γ, v = z * k * w ∧ z ∈ ⨆ i, H i ∧ (∀ g ∈ ⨆ i, H i, z * g = g * z) ∧ z ^ p = 1 ∧
      k ∈ KK ∧ k ∈ ⨆ i, H i ∧ k ^ p = 1 ∧ w ∈ WW ∧ w ∈ ⨆ i, H i ∧ w ^ p = 1 := by
  classical
  have := Fintype.ofFinite ι
  set Φ := Subgroup.noncommPiCoprod hcomm with hΦ
  have hinj : Function.Injective Φ := Subgroup.injective_noncommPiCoprod_of_iSupIndep hindep
  have hrange : Φ.range = ⨆ i, H i := Subgroup.noncommPiCoprod_range
  obtain ⟨t, rfl⟩ : v ∈ Φ.range := hrange ▸ hv
  have htp : ∀ i, (t i : Γ) ^ p = 1 := by
    have h1 : Φ (t ^ p) = Φ 1 := by rw [map_pow, hvp, map_one]
    have h2 := hinj h1
    intro i
    have := congrArg (fun u : (i : ι) → H i => (u i : Γ)) h2
    simpa using this
  have key : ∀ i, ∃ s k w : Γ, s ∈ H i ∧ k ∈ H i ∧ w ∈ H i ∧ k ∈ KK ∧ w ∈ WW ∧
      (t i : Γ) = s * k * w ∧ (∀ g ∈ H i, s * g = g * s) ∧ s ^ p = 1 ∧ k ^ p = 1 ∧ w ^ p = 1 :=
    fun i => hloc i (t i) (t i).2 (htp i)
  choose s k w hs hk hw hkK hwW hdec hsc hsp hkp hwp using key
  set s' : (i : ι) → H i := fun i => ⟨s i, hs i⟩
  set k' : (i : ι) → H i := fun i => ⟨k i, hk i⟩
  set w' : (i : ι) → H i := fun i => ⟨w i, hw i⟩
  have hts : t = s' * k' * w' := funext fun i => Subtype.ext (hdec i)
  have hmem : ∀ u : (i : ι) → H i, Φ u ∈ ⨆ i, H i := fun u => hrange ▸ ⟨u, rfl⟩
  have hpow : ∀ u : (i : ι) → H i, (∀ i, (u i : Γ) ^ p = 1) → Φ u ^ p = 1 := by
    intro u hu
    rw [← map_pow]
    have : u ^ p = 1 := funext fun i => Subtype.ext (by simpa using hu i)
    rw [this, map_one]
  refine ⟨Φ s', Φ k', Φ w', ?_, hmem s', ?_, hpow s' hsp, ?_, hmem k', hpow k' hkp, ?_, hmem w',
    hpow w' hwp⟩
  · rw [hts, map_mul, map_mul]
  · intro g hg
    obtain ⟨t', rfl⟩ : g ∈ Φ.range := hrange ▸ hg
    rw [← map_mul, ← map_mul]
    exact congrArg Φ (funext fun i => Subtype.ext (hsc i (t' i) (t' i).2))
  · have : ∀ u : (i : ι) → H i, (∀ i, (u i : Γ) ∈ KK) → Φ u ∈ KK := by
      intro u hu
      rw [hΦ, Subgroup.noncommPiCoprod_apply]
      exact Subgroup.noncommProd_mem _ _ fun i _ => hu i
    exact this k' hkK
  · have : ∀ u : (i : ι) → H i, (∀ i, (u i : Γ) ∈ WW) → Φ u ∈ WW := by
      intro u hu
      rw [hΦ, Subgroup.noncommPiCoprod_apply]
      exact Subgroup.noncommProd_mem _ _ fun i _ => hu i
    exact this w' hwW

end Pi

end CFSG.RankThree.PartOne.KCSymplectic
