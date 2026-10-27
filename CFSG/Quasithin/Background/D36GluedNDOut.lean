module

import CFSG.Quasithin.Background.F918Z4bL2Syl
import CFSG.Walter.PSL2Facts.Even
import CFSG.Walter.Bender1970.S2.AutEven
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
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
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
public import Mathlib.Topology.Sheaves.Presheaf
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Quasithin

open CFSG.Walter CFSG.GorensteinWalter
open scoped MatrixGroups Pointwise

section Abstract

variable {L : Type} [Group L] [Finite L]

theorem fixes_of_fixes_index_two {n : ℕ} (hn : 3 ≤ n) (S D R₀ : Subgroup L)
    (hScomm : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) (hSsq : ∀ a ∈ S, a * a = 1)
    (hScard : Nat.card S = 2 ^ n) (hDnorm : D ≤ Subgroup.normalizer (S : Set L))
    (hfree : ∀ x ∈ S, x ≠ 1 → ∀ d ∈ D, d * x * d⁻¹ = x → d = 1)
    (hD1 : ∃ d ∈ D, d ≠ 1)
    (hN : ∀ g ∈ Subgroup.normalizer (S : Set L), ∃ s ∈ S, ∃ d ∈ D, g = s * d)
    (φ : MulAut L) (hφS : ∀ x ∈ S, φ x ∈ S)
    (hφN : ∀ g ∈ Subgroup.normalizer (S : Set L), φ g ∈ Subgroup.normalizer (S : Set L))
    (hR₀S : R₀ ≤ S) (hR₀ : 2 ^ (n - 1) ≤ Nat.card R₀) (hφ : ∀ x ∈ R₀, φ x = x) :
    ∀ x ∈ S, φ x = x := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x₀, hx₀S, hx₀⟩ := hcon
  have hn2 : 2 ^ n = 2 * 2 ^ (n - 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp [pow_succ]
    ring
  have hNmem : ∀ x ∈ S, φ x * x⁻¹ ∈ S := fun x hx => S.mul_mem (hφS x hx) (S.inv_mem hx)
  have hNmul : ∀ x ∈ S, ∀ y ∈ S, φ (x * y) * (x * y)⁻¹ = (φ x * x⁻¹) * (φ y * y⁻¹) := by
    intro x hx y hy
    have hc : x⁻¹ * (φ y * y⁻¹) = (φ y * y⁻¹) * x⁻¹ :=
      hScomm _ (S.inv_mem hx) _ (hNmem y hy)
    calc φ (x * y) * (x * y)⁻¹ = φ x * ((φ y * y⁻¹) * x⁻¹) := by
          rw [map_mul, mul_inv_rev]; group
      _ = φ x * (x⁻¹ * (φ y * y⁻¹)) := by rw [← hc]
      _ = (φ x * x⁻¹) * (φ y * y⁻¹) := by group
  let N : ↥S →* ↥S :=
    { toFun := fun x => ⟨φ x * (x : L)⁻¹, hNmem x x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (hNmul x x.2 y y.2) }
  have hNapply : ∀ x : ↥S, ((N x : ↥S) : L) = φ x * (x : L)⁻¹ := fun x => rfl
  have hker : 2 ^ (n - 1) ≤ Nat.card N.ker := by
    have hle : R₀.subgroupOf S ≤ N.ker := by
      intro x hx
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      rw [hNapply, hφ x (Subgroup.mem_subgroupOf.mp hx), mul_inv_cancel]
      rfl
    have h1 : Nat.card ↥(R₀.subgroupOf S) = Nat.card R₀ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR₀S).toEquiv
    have := Subgroup.card_le_of_le hle
    omega
  have hrange : Nat.card N.range ≤ 2 := by
    have h1 : N.ker.index = Nat.card N.range := Subgroup.index_ker N
    have h2 := N.ker.index_mul_card
    have hS : Nat.card ↥S = 2 ^ n := hScard
    rw [h1, hS] at h2
    by_contra hlt
    push Not at hlt
    have hge : 3 * Nat.card N.ker ≤ Nat.card N.range * Nat.card N.ker :=
      Nat.mul_le_mul_right _ hlt
    rw [h2] at hge
    have hpos : 0 < 2 ^ (n - 1) := by positivity
    omega
  have hdich : ∀ y ∈ N.range, ∀ z ∈ N.range, y = 1 ∨ z = 1 ∨ y = z := by
    intro y hy z hz
    by_contra h
    push Not at h
    obtain ⟨h1, h2, h3⟩ := h
    have hthree : ({1, ⟨y, hy⟩, ⟨z, hz⟩} : Set ↥N.range).ncard = 3 := by
      apply Set.ncard_eq_three.mpr
      refine ⟨1, ⟨y, hy⟩, ⟨z, hz⟩, ?_, ?_, ?_, rfl⟩
      · intro h; exact h1 (congrArg Subtype.val h).symm
      · intro h; exact h2 (congrArg Subtype.val h).symm
      · intro h; exact h3 (congrArg Subtype.val h)
    have := Set.ncard_le_ncard (Set.subset_univ ({1, ⟨y, hy⟩, ⟨z, hz⟩} : Set ↥N.range))
    rw [hthree, Set.ncard_univ] at this
    omega
  obtain ⟨x₁, hx₁S, hx₁⟩ : ∃ x₁ ∈ S, φ x₁ * x₁⁻¹ ≠ 1 := by
    refine ⟨x₀, hx₀S, fun h => hx₀ ?_⟩
    rwa [mul_inv_eq_one] at h
  set v : L := φ x₁ * x₁⁻¹ with hvdef
  have hvS : v ∈ S := hNmem x₁ hx₁S
  have hdichL : ∀ x ∈ S, φ x * x⁻¹ = 1 ∨ φ x * x⁻¹ = v := by
    intro x hx
    have := hdich (N ⟨x, hx⟩) ⟨_, rfl⟩ (N ⟨x₁, hx₁S⟩) ⟨_, rfl⟩
    rcases this with h | h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact absurd (congrArg Subtype.val h) hx₁
    · exact Or.inr (congrArg Subtype.val h)
  have hv1 : v ≠ 1 := hx₁
  have hNv : φ v * v⁻¹ = 1 := by
    rcases hdichL v hvS with h | h
    · exact h
    · exfalso
      have h1 : φ v = v * v := by rw [mul_inv_eq_iff_eq_mul] at h; exact h
      rw [hSsq v hvS] at h1
      apply hv1
      apply φ.injective
      rw [h1, map_one]
  have hconj : ∀ d ∈ D, ∀ x ∈ S, d * x * d⁻¹ ∈ S := fun d hd x hx =>
    ((Subgroup.mem_normalizer_iff.mp (hDnorm hd) x).mp hx)
  have hconj' : ∀ d ∈ D, ∀ x ∈ S, d⁻¹ * x * d ∈ S := fun d hd x hx => by
    have := hconj d⁻¹ (D.inv_mem hd) x hx
    simpa using this
  have hrel : ∀ d ∈ D, ∃ d₁ ∈ D, ∀ x ∈ S, φ (d * x * d⁻¹) = d₁ * φ x * d₁⁻¹ := by
    intro d hd
    obtain ⟨s₁, hs₁, d₁, hd₁, hsd⟩ := hN (φ d) (hφN d (hDnorm hd))
    refine ⟨d₁, hd₁, fun x hx => ?_⟩
    have h1 : d₁ * φ x * d₁⁻¹ ∈ S := hconj d₁ hd₁ _ (hφS x hx)
    have hc : s₁ * (d₁ * φ x * d₁⁻¹) = (d₁ * φ x * d₁⁻¹) * s₁ := hScomm _ hs₁ _ h1
    calc φ (d * x * d⁻¹) = φ d * φ x * (φ d)⁻¹ := by simp [map_mul, map_inv]
      _ = (s₁ * d₁) * φ x * (s₁ * d₁)⁻¹ := by rw [hsd]
      _ = s₁ * (d₁ * φ x * d₁⁻¹) * s₁⁻¹ := by group
      _ = (d₁ * φ x * d₁⁻¹) * s₁ * s₁⁻¹ := by rw [hc]
      _ = d₁ * φ x * d₁⁻¹ := by group
  have hd1 : ∀ d ∈ D, ∀ d₁ ∈ D, (∀ x ∈ S, φ (d * x * d⁻¹) = d₁ * φ x * d₁⁻¹) → d₁ = d := by
    intro d hd d₁ hd₁ hrel'
    by_contra hne
    set g : L := d₁ * d⁻¹ with hg
    have hgD : g ∈ D := D.mul_mem hd₁ (D.inv_mem hd)
    have hg1 : g ≠ 1 := by
      intro h
      apply hne
      rw [hg, mul_inv_eq_one] at h
      exact h
    set w : L := d₁ * v * d₁⁻¹ with hw
    have hwS : w ∈ S := hconj d₁ hd₁ v hvS
    let f : L → L := fun y => g * y * g⁻¹ * y⁻¹
    have hmaps : ∀ y ∈ (S : Set L), f y ∈ ({1, v, w, v * w} : Set L) := by
      intro y hy
      have hxS : d⁻¹ * y * d ∈ S := hconj' d hd y hy
      set x := d⁻¹ * y * d with hx
      have hyx : y = d * x * d⁻¹ := by rw [hx]; group
      have hE1 : φ y = d₁ * φ x * d₁⁻¹ := by rw [hyx]; exact hrel' x hxS
      have hfy : f y = (d₁ * (φ x * x⁻¹) * d₁⁻¹)⁻¹ * (φ y * y⁻¹) := by
        have h1 : g * y * g⁻¹ = d₁ * x * d₁⁻¹ := by rw [hg, hx]; group
        have h2 : (d₁ * (φ x * x⁻¹) * d₁⁻¹)⁻¹ * (φ y * y⁻¹) =
            (d₁ * x * d₁⁻¹) * y⁻¹ := by
          rw [hE1]
          have hxx : d₁ * (φ x * x⁻¹) * d₁⁻¹ = (d₁ * φ x * d₁⁻¹) * (d₁ * x * d₁⁻¹)⁻¹ := by group
          rw [hxx]
          group
        simp only [f]
        rw [h1, h2]
      rw [hfy]
      have hvx : d₁ * v * d₁⁻¹ = w := hw.symm
      have hwsq : w * w = 1 := hSsq w hwS
      have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hwsq
      have hwv : w * v = v * w := hScomm _ hwS _ hvS
      have e1 : (d₁ * (φ x * x⁻¹) * d₁⁻¹)⁻¹ = 1 ∨ (d₁ * (φ x * x⁻¹) * d₁⁻¹)⁻¹ = w := by
        rcases hdichL x hxS with h1 | h1
        · left
          rw [h1]
          group
        · right
          rw [h1, hvx, hwinv]
      rcases e1 with e1 | e1 <;> rcases hdichL y hy with h2 | h2 <;> rw [e1, h2]
      · simp
      · simp
      · simp
      · rw [hwv]
        simp
    have hinj : Set.InjOn f (S : Set L) := by
      intro y hy y' hy' hff
      have hz : y * y'⁻¹ ∈ S := S.mul_mem hy (S.inv_mem hy')
      have hgy : g * y * g⁻¹ ∈ S := hconj g hgD y hy
      have hc : f y ∈ S := S.mul_mem hgy (S.inv_mem hy)
      have e1 : g * y * g⁻¹ = f y * y := by simp [f]
      have e2 : g * y' * g⁻¹ = f y' * y' := by simp [f]
      have hff' : f y' = f y := hff.symm
      have hgz : g * (y * y'⁻¹) * g⁻¹ = y * y'⁻¹ := by
        calc g * (y * y'⁻¹) * g⁻¹ = (g * y * g⁻¹) * (g * y' * g⁻¹)⁻¹ := by group
          _ = (f y * y) * (f y' * y')⁻¹ := by rw [e1, e2]
          _ = f y * (y * y'⁻¹) * (f y)⁻¹ := by rw [hff']; group
          _ = y * y'⁻¹ := by rw [hScomm (f y) hc (y * y'⁻¹) hz]; group
      by_contra hne'
      have hz1 : y * y'⁻¹ ≠ 1 := fun h => hne' (mul_inv_eq_one.mp h)
      exact hg1 (hfree _ hz hz1 g hgD hgz)
    classical
    have hcard : (S : Set L).ncard ≤ ((({1, v, w, v * w} : Finset L)) : Set L).ncard :=
      Set.ncard_le_ncard_of_injOn f (fun y hy => by simpa using hmaps y hy) hinj (Set.toFinite _)
    rw [Set.ncard_coe_finset] at hcard
    have h4 : (({1, v, w, v * w} : Finset L)).card ≤ 4 := Finset.card_le_four
    have hSn : (S : Set L).ncard = 2 ^ n := by
      rw [← Nat.card_coe_set_eq]
      exact hScard
    have h8 : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  obtain ⟨d, hd, hd1'⟩ := hD1
  obtain ⟨d₁, hd₁, hrel'⟩ := hrel d hd
  have hd₁d := hd1 d hd d₁ hd₁ hrel'
  rw [hd₁d] at hrel'
  have hxS' : d * x₁ * d⁻¹ ∈ S := hconj d hd x₁ hx₁S
  have h1 : φ (d * x₁ * d⁻¹) * (d * x₁ * d⁻¹)⁻¹ = d * v * d⁻¹ := by
    rw [hrel' x₁ hx₁S, hvdef]
    group
  rcases hdichL _ hxS' with h2 | h2
  · rw [h1] at h2
    apply hv1
    have := congrArg (fun z => d⁻¹ * z * d) h2
    simpa [mul_assoc] using this
  · rw [h1] at h2
    exact hd1' (hfree v hvS hv1 d hd h2)

end Abstract

section PSL

variable {n : ℕ}

theorem mulAut_inner_of_fixes_index_two (hn : 3 ≤ n) (S : Sylow 2 PSL(2, GaloisField 2 n))
    (R₀ : Subgroup PSL(2, GaloisField 2 n))
    (hR₀S : R₀ ≤ (S : Subgroup PSL(2, GaloisField 2 n)))
    (hR₀ : 2 ^ (n - 1) ≤ Nat.card R₀) (φ : MulAut PSL(2, GaloisField 2 n))
    (hφ : ∀ x ∈ R₀, φ x = x) :
    ∃ s ∈ (S : Subgroup PSL(2, GaloisField 2 n)), φ = MulAut.conj s := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L := PSL(2, GaloisField 2 n) with hL
  have hf : 2 ≤ n := by omega
  obtain ⟨hSel, hScard⟩ := psl2_even_sylow_two hf S
  have hScomm : ∀ a ∈ (S : Subgroup L), ∀ b ∈ (S : Subgroup L), a * b = b * a :=
    fun a ha b hb => congrArg Subtype.val
      (hSel.toIsMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hSsq : ∀ a ∈ (S : Subgroup L), a * a = 1 := fun a ha => by
    have := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := (S : Subgroup L)) a ha
    simpa [pow_two] using this
  obtain ⟨D, -, hDcard, -, hsup, hreg⟩ := psl2_even_normalizer_sylow_two hf S
  have hDnorm : D ≤ Subgroup.normalizer ((S : Subgroup L) : Set L) := hsup ▸ le_sup_right
  have hfree : ∀ x ∈ (S : Subgroup L), x ≠ 1 → ∀ d ∈ D, d * x * d⁻¹ = x → d = 1 := by
    intro x hx hx1 d hd hdx
    obtain ⟨d₀, -, huniq⟩ := hreg x hx hx1 x hx hx1
    have h1 : (⟨d, hd⟩ : D) = d₀ := huniq _ hdx
    have h2 : (⟨1, D.one_mem⟩ : D) = d₀ := huniq _ (by simp)
    exact congrArg Subtype.val (h1.trans h2.symm)
  have hD1 : ∃ d ∈ D, d ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : D = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hcon
    rw [this, Subgroup.card_bot] at hDcard
    have h8 : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  have hN : ∀ g ∈ Subgroup.normalizer ((S : Subgroup L) : Set L), ∃ s ∈ (S : Subgroup L),
      ∃ d ∈ D, g = s * d := by
    intro g hg
    rw [← hsup] at hg
    have h1 : (((S : Subgroup L) ⊔ D : Subgroup L) : Set L) = (S : Subgroup L) * D :=
      Subgroup.coe_mul_of_right_le_normalizer_left (S : Subgroup L) D hDnorm
    have : g ∈ (((S : Subgroup L) ⊔ D : Subgroup L) : Set L) := hg
    rw [h1] at this
    obtain ⟨s, hs, d, hd, rfl⟩ := this
    exact ⟨s, hs, d, hd, rfl⟩
  have hmem_smul : ∀ (ψ : MulAut L) (x : L),
      x ∈ ((ψ • S : Sylow 2 L) : Subgroup L) ↔ ψ⁻¹ x ∈ (S : Subgroup L) := by
    intro ψ x
    rw [Sylow.pointwise_smul_def, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def]
  have hφSyl : φ • S = S := by
    by_contra hne
    have hti := psl2_even_normalizer_inf_eq_bot hf hne
    have hR : R₀ ≤ ⊥ := by
      intro x hx
      have hxS : x ∈ (S : Subgroup L) := hR₀S hx
      have hxφ : x ∈ ((φ • S : Sylow 2 L) : Subgroup L) := by
        rw [hmem_smul]
        have : φ⁻¹ x = x := by
          rw [MulAut.inv_apply, MulEquiv.symm_apply_eq]
          exact (hφ x hx).symm
        rw [this]
        exact hxS
      rw [← hti]
      exact ⟨Subgroup.le_normalizer hxφ, hxS⟩
    have h1 : Nat.card R₀ = 1 := by
      have : R₀ = ⊥ := le_bot_iff.mp hR
      rw [this, Subgroup.card_bot]
    have h8 : 2 ^ 2 ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hφS : ∀ x ∈ (S : Subgroup L), φ x ∈ (S : Subgroup L) := by
    intro x hx
    have h1 : φ x ∈ ((φ • S : Sylow 2 L) : Subgroup L) := by
      rw [hmem_smul]
      simpa using hx
    rwa [hφSyl] at h1
  have hφS' : ∀ y : L, φ y ∈ (S : Subgroup L) → y ∈ (S : Subgroup L) := by
    intro y hy
    have h1 : φ y ∈ ((φ • S : Sylow 2 L) : Subgroup L) := by rwa [hφSyl]
    rw [hmem_smul] at h1
    simpa using h1
  have hφN : ∀ g ∈ Subgroup.normalizer ((S : Subgroup L) : Set L),
      φ g ∈ Subgroup.normalizer ((S : Subgroup L) : Set L) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff] at hg ⊢
    intro h
    have e : φ g * h * (φ g)⁻¹ = φ (g * φ⁻¹ h * g⁻¹) := by simp [map_mul, map_inv]
    constructor
    · intro hh
      rw [e]
      apply hφS
      apply (hg _).mp
      exact hφS' _ (by simpa using hh)
    · intro hh
      rw [e] at hh
      have := (hg (φ⁻¹ h)).mpr (hφS' _ hh)
      have h2 := hφS _ this
      simpa using h2
  have hfix := fixes_of_fixes_index_two hn (S : Subgroup L) D R₀ hScomm hSsq hScard hDnorm hfree
    hD1 hN φ hφS hφN hR₀S hR₀ hφ
  exact mulAut_eq_conj_of_fixes_sylow hf S hScomm φ hfix

end PSL

end CFSG.Quasithin
