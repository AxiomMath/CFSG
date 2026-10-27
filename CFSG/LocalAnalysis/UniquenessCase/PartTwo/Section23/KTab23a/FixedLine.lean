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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
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

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KTabA

open scoped Matrix Pointwise

private lemma coe_mulAut_conj {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {Γ : Subgroup (GL ι K)} (g t : ↥Γ) :
    (((MulAut.conj g) t : ↥Γ) : GL ι K) = MulAut.conj (g : GL ι K) (t : GL ι K) :=
  rfl

private lemma conj_mulVec_fixed {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {γ τ : GL ι K} {v : ι → K}
    (hv : ((τ : GL ι K) : Matrix ι ι K) *ᵥ v = v) :
    ((((MulAut.conj γ τ : GL ι K)) : Matrix ι ι K)) *ᵥ
        (((γ : GL ι K) : Matrix ι ι K) *ᵥ v) =
      ((γ : GL ι K) : Matrix ι ι K) *ᵥ v := by
  have hCγ : (((γ⁻¹ : GL ι K)) : Matrix ι ι K) * ((γ : GL ι K) : Matrix ι ι K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel]
    rfl
  calc ((((MulAut.conj γ τ : GL ι K)) : Matrix ι ι K)) *ᵥ
          (((γ : GL ι K) : Matrix ι ι K) *ᵥ v)
      = ((((MulAut.conj γ τ : GL ι K)) : Matrix ι ι K) *
            ((γ : GL ι K) : Matrix ι ι K)) *ᵥ v := Matrix.mulVec_mulVec v _ _
    _ = ((((γ : GL ι K) : Matrix ι ι K) * ((τ : GL ι K) : Matrix ι ι K)) *
            (((γ⁻¹ : GL ι K)) : Matrix ι ι K) *
              ((γ : GL ι K) : Matrix ι ι K)) *ᵥ v := by
          rw [MulAut.conj_apply, Units.val_mul, Units.val_mul]
    _ = (((γ : GL ι K) : Matrix ι ι K) * ((τ : GL ι K) : Matrix ι ι K)) *ᵥ v := by
          rw [mul_assoc, hCγ, mul_one]
    _ = ((γ : GL ι K) : Matrix ι ι K) *ᵥ
          (((τ : GL ι K) : Matrix ι ι K) *ᵥ v) :=
          (Matrix.mulVec_mulVec v _ _).symm
    _ = ((γ : GL ι K) : Matrix ι ι K) *ᵥ v := by rw [hv]

private lemma mulVec_inv_mulVec {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (g : GL ι K) (v : ι → K) :
    (((g : GL ι K) : Matrix ι ι K) * (((g⁻¹ : GL ι K) : Matrix ι ι K))) *ᵥ v = v := by
  have h : ((g : GL ι K) : Matrix ι ι K) * (((g⁻¹ : GL ι K) : Matrix ι ι K)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel]
    rfl
  rw [h, Matrix.one_mulVec]

private lemma smul_mem_fixed_conj {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {Γ : Subgroup (GL ι K)} (g : ↥Γ) (T : Subgroup ↥Γ) {v : ι → K}
    (hv : ∀ t ∈ T, ((t : GL ι K) : Matrix ι ι K) *ᵥ v = v) :
    ∀ s ∈ (MulAut.conj g • T : Subgroup ↥Γ),
      ((s : GL ι K) : Matrix ι ι K) *ᵥ ((((g : ↥Γ) : GL ι K)) : Matrix ι ι K) *ᵥ v =
        ((((g : ↥Γ) : GL ι K)) : Matrix ι ι K) *ᵥ v := by
  intro s hs
  obtain ⟨t, ht, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists s (MulAut.conj g) T).mp hs
  change (((MulAut.conj g t : ↥Γ) : GL ι K) : Matrix ι ι K) *ᵥ
        ((((g : ↥Γ) : GL ι K)) : Matrix ι ι K) *ᵥ v =
      ((((g : ↥Γ) : GL ι K)) : Matrix ι ι K) *ᵥ v
  rw [coe_mulAut_conj]
  exact conj_mulVec_fixed (γ := (g : GL ι K)) (τ := (t : GL ι K)) (hv t ht)

private lemma exists_ne_zero_fixed_sylow {ι K : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] {Γ : Subgroup (GL ι K)}
    (S : Sylow p ↥Γ) :
    ∃ v : ι → K, v ≠ 0 ∧
      ∀ s ∈ (S : Subgroup ↥Γ), ((s : GL ι K) : Matrix ι ι K) *ᵥ v = v := by
  classical
  let σ : ↥S →* Matrix ι ι K :=
    (Units.coeHom (Matrix ι ι K)).comp (Γ.subtype.comp (S : Subgroup ↥Γ).subtype)
  letI : MulAction ↥S (ι → K) :=
    { smul := fun s v => σ s *ᵥ v
      one_smul := fun v => by
        change σ 1 *ᵥ v = v
        rw [map_one, Matrix.one_mulVec]
      mul_smul := fun a b v => by
        change σ (a * b) *ᵥ v = σ a *ᵥ (σ b *ᵥ v)
        rw [map_mul σ a b, Matrix.mulVec_mulVec] }
  haveI : Finite (ι → K) := inferInstance
  have hpK : p ∣ Nat.card K := by
    haveI : Fintype K := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card]
    refine (prime_dvd_char_iff_dvd_card p).mp ?_
    simpa only [CharP.ringChar_of_prime_eq_zero (Fact.out : p.Prime) (CharP.cast_eq_zero K p)]
      using (dvd_rfl : p ∣ p)
  have hcard : Nat.card (ι → K) = Nat.card K ^ Nat.card ι := Nat.card_fun
  have hι : 0 < Nat.card ι := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_pos_iff.mpr inferInstance
  have hpV : p ∣ Nat.card (ι → K) := by
    rw [hcard]
    exact hpK.trans (dvd_pow_self (Nat.card K) hι.ne')
  have h0 : (0 : ι → K) ∈ MulAction.fixedPoints ↥S (ι → K) := by
    intro s
    show σ s *ᵥ (0 : ι → K) = 0
    rw [Matrix.mulVec_zero]
  obtain ⟨b, hb, hne⟩ :=
    IsPGroup.exists_fixed_point_of_prime_dvd_card_of_fixed_point (α := ι → K)
      S.isPGroup' hpV h0
  refine ⟨b, fun hb0 => hne hb0.symm, ?_⟩
  intro s hs
  have hsb := (MulAction.mem_fixedPoints.mp hb) ⟨s, hs⟩
  show ((s : GL ι K) : Matrix ι ι K) *ᵥ b = b
  exact hsb

private lemma mem_span_conj_of_fixed {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {Γ : Subgroup (GL ι K)} (U P S : Subgroup ↥Γ) (hUP : U ≤ P) (e : ι → K)
    (hfix : ∀ v : ι → K,
      (∀ u ∈ U, ((u : GL ι K) : Matrix ι ι K) *ᵥ v = v) → v ∈ Submodule.span K {e})
    (g : ↥Γ) (hgS : S = MulAut.conj g • P) {v : ι → K}
    (hv : ∀ s ∈ S, ((s : GL ι K) : Matrix ι ι K) *ᵥ v = v) :
    v ∈ Submodule.span K {(((g : ↥Γ) : GL ι K) : Matrix ι ι K) *ᵥ e} := by
  have hconjP : MulAut.conj (g⁻¹) • S = P := by
    rw [hgS, map_inv (MulAut.conj) g, inv_smul_smul]
  have hPfix := smul_mem_fixed_conj (g⁻¹) S hv
  rw [hconjP] at hPfix
  have hspan : ((((g⁻¹ : ↥Γ) : GL ι K)) : Matrix ι ι K) *ᵥ v ∈ Submodule.span K {e} :=
    hfix _ (fun u hu => hPfix u (hUP hu))
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hspan
  refine Submodule.mem_span_singleton.mpr ⟨c, ?_⟩
  calc c • ((((g : ↥Γ) : GL ι K) : Matrix ι ι K) *ᵥ e)
      = (((g : ↥Γ) : GL ι K) : Matrix ι ι K) *ᵥ (c • e) :=
        (Matrix.mulVec_smul _ c e).symm
    _ = ((((g : ↥Γ) : GL ι K) : Matrix ι ι K) *
          ((((g⁻¹ : ↥Γ) : GL ι K)) : Matrix ι ι K)) *ᵥ v := by
        rw [hc, Matrix.mulVec_mulVec]
    _ = v := by
        rw [show ((g⁻¹ : ↥Γ) : GL ι K) = (g : GL ι K)⁻¹ by rfl]
        exact mulVec_inv_mulVec (g : GL ι K) v

private lemma eq_span_singleton_of_ne_zero_mem {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] {F : Submodule K V} {x b : V} (hb : b ∈ F) (hb0 : b ≠ 0)
    (hle : F ≤ Submodule.span K {x}) : F = Submodule.span K {x} ∧ Nat.card ↥F = Nat.card K := by
  have hx : x ∈ F := by
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hle hb)
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc
      exact hb0 hc.symm
    have hxb : x ∈ Submodule.span K ({b} : Set V) := by
      rw [Submodule.mem_span_singleton]
      exact ⟨c⁻¹, by rw [← hc, inv_smul_smul₀ hc0]⟩
    exact (Submodule.span_le.mpr (by simpa using hb)) hxb
  have hx0 : x ≠ 0 := by
    intro h0
    have : b ∈ Submodule.span K ({x} : Set V) := hle hb
    rw [h0] at this
    exact hb0 (by simpa using this)
  have hF : F = Submodule.span K {x} :=
    le_antisymm hle (Submodule.span_le.mpr (by simpa using hx))
  refine ⟨hF, ?_⟩
  rw [hF]
  haveI : Module.Finite K ↥(Submodule.span K {x}) := FiniteDimensional.span_singleton K x
  rw [Module.natCard_eq_pow_finrank (K := K), finrank_span_singleton hx0, pow_one]

theorem card_fixed_sylow_eq_card {ι K : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] {Γ : Subgroup (GL ι K)}
    (U : Subgroup ↥Γ) (hU : IsPGroup p ↥U) (e : ι → K)
    (hfix : ∀ v : ι → K,
      (∀ u ∈ U, ((u : GL ι K) : Matrix ι ι K) *ᵥ v = v) → v ∈ Submodule.span K {e})
    (S : Sylow p ↥Γ) :
    Nat.card {v : ι → K // ∀ s ∈ (S : Subgroup ↥Γ), ((s : GL ι K) : Matrix ι ι K) *ᵥ v = v} =
      Nat.card K := by
  classical
  let F : Submodule K (ι → K) :=
    { carrier := {v | ∀ s ∈ (S : Subgroup ↥Γ), ((s : GL ι K) : Matrix ι ι K) *ᵥ v = v}
      zero_mem' := by
        intro s _
        rw [Matrix.mulVec_zero]
      add_mem' := by
        intro x y hx hy s hs
        rw [Matrix.mulVec_add, hx s hs, hy s hs]
      smul_mem' := by
        intro c x hx s hs
        rw [Matrix.mulVec_smul, hx s hs] }
  change Nat.card ↥F = Nat.card K
  obtain ⟨b, hb_ne, hb_fix⟩ := exists_ne_zero_fixed_sylow p S
  have hbF : b ∈ F := hb_fix
  obtain ⟨P, hUP⟩ := hU.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥Γ) P S
  have hgS : (S : Subgroup ↥Γ) = MulAut.conj g • (P : Subgroup ↥Γ) := by
    rw [← hg, Sylow.coe_subgroup_smul]
  have hF_le : F ≤ Submodule.span K {(((g : ↥Γ) : GL ι K) : Matrix ι ι K) *ᵥ e} :=
    fun v hv => mem_span_conj_of_fixed U P (S : Subgroup ↥Γ) hUP e hfix g hgS hv
  exact (eq_span_singleton_of_ne_zero_mem hbF hb_ne hF_le).2

end CFSG.LocalAnalysis.UniquenessCase.UC22.KTabA
