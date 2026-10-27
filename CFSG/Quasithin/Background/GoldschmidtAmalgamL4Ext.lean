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
public import Mathlib.Order.CompletePartialOrder
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

namespace CFSG.Quasithin.F6.GoldAmL4

variable {D E : Type*} [Group D] [Group E]

structure Ext3Data (T Q : Subgroup D) (y t₀ : D) : Prop where
  Q_le : Q ≤ T
  y_cube : y ^ 3 = 1
  y_not_mem : y ∉ T
  t₀_mem : t₀ ∈ T
  T_eq : ∀ t ∈ T, t ∈ Q ∨ t * t₀⁻¹ ∈ Q
  conj_Q : ∀ q ∈ Q, y * q * y⁻¹ ∈ Q
  conj_Q' : ∀ q ∈ Q, y⁻¹ * q * y ∈ Q
  conj_t₀ : y * t₀ * y ∈ T
  conj_t₀' : y⁻¹ * t₀ * y⁻¹ ∈ T

structure Ext3Compat (T Q : Subgroup D) (T' : Subgroup E) (y t₀ : D) (y' : E) (ι : D → E) :
    Prop where
  mul : ∀ t₁ ∈ T, ∀ t₂ ∈ T, ι (t₁ * t₂) = ι t₁ * ι t₂
  mem : ∀ t ∈ T, ι t ∈ T'
  inj : ∀ t₁ ∈ T, ∀ t₂ ∈ T, ι t₁ = ι t₂ → t₁ = t₂
  surj : ∀ t' ∈ T', ∃ t ∈ T, ι t = t'
  conj_Q : ∀ q ∈ Q, ι (y * q * y⁻¹) = y' * ι q * y'⁻¹
  conj_t₀ : ι (y * t₀ * y) = y' * ι t₀ * y'
  conj_t₀' : ι (y⁻¹ * t₀ * y⁻¹) = y'⁻¹ * ι t₀ * y'⁻¹

namespace Ext3Data

variable {T Q : Subgroup D} {y t₀ : D} (h : Ext3Data T Q y t₀)

include h

omit [Group E] in
theorem y_inv : y⁻¹ = y ^ 2 := by
  rw [inv_eq_iff_mul_eq_one, ← pow_succ', h.y_cube]

omit [Group E] in
theorem y_inv_not_mem : y⁻¹ ∉ T := fun hy => h.y_not_mem (by simpa using T.inv_mem hy)

omit [Group E] in
theorem y_sq_not_mem : y ^ 2 ∉ T := by
  rw [← h.y_inv]
  exact h.y_inv_not_mem

omit [Group E] in
theorem zpow_not_mem {m : ℤ} (hm : ¬ (3 : ℤ) ∣ m) : y ^ m ∉ T := by
  have h3 : y ^ (3 : ℤ) = 1 := by exact_mod_cast h.y_cube
  have e : y ^ m = y ^ (m % 3) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv m 3]
    rw [zpow_add, zpow_mul, h3, one_zpow, mul_one]
  rw [e]
  have h12 : m % 3 = 1 ∨ m % 3 = 2 := by omega
  rcases h12 with h1 | h1
  · rw [h1]; simpa using h.y_not_mem
  · rw [h1]; simpa [zpow_two] using h.y_sq_not_mem

omit [Group E] in
theorem nf_unique {t₁ t₂ : D} (h₁ : t₁ ∈ T) (h₂ : t₂ ∈ T) {i k : ℕ} (hi : i < 3) (hk : k < 3)
    (e : t₁ * y ^ i = t₂ * y ^ k) : i = k ∧ t₁ = t₂ := by
  have hik : i = k := by
    by_contra hne
    have hc : y ^ ((i : ℤ) - k) = t₁⁻¹ * t₂ := by
      rw [zpow_sub, zpow_natCast, zpow_natCast]
      calc y ^ i * (y ^ k)⁻¹ = t₁⁻¹ * (t₁ * y ^ i) * (y ^ k)⁻¹ := by group
        _ = t₁⁻¹ * (t₂ * y ^ k) * (y ^ k)⁻¹ := by rw [e]
        _ = t₁⁻¹ * t₂ := by group
    have hmem : y ^ ((i : ℤ) - k) ∈ T := by rw [hc]; exact T.mul_mem (T.inv_mem h₁) h₂
    exact h.zpow_not_mem (by omega) hmem
  subst hik
  exact ⟨rfl, mul_right_cancel e⟩

end Ext3Data

namespace Ext3Compat

variable {T Q : Subgroup D} {T' : Subgroup E} {y t₀ : D} {y' : E} {ι : D → E}

theorem map_one (hc : Ext3Compat T Q T' y t₀ y' ι) : ι 1 = 1 := by
  have := hc.mul 1 T.one_mem 1 T.one_mem
  simpa using this

theorem conj_inv (hc : Ext3Compat T Q T' y t₀ y' ι) (h : Ext3Data T Q y t₀) {q : D}
    (hq : q ∈ Q) : ι (y⁻¹ * q * y) = y'⁻¹ * ι q * y' := by
  have h1 := hc.conj_Q (y⁻¹ * q * y) (h.conj_Q' q hq)
  rw [show y * (y⁻¹ * q * y) * y⁻¹ = q by group] at h1
  have : ι (y⁻¹ * q * y) = y'⁻¹ * (y' * ι (y⁻¹ * q * y) * y'⁻¹) * y' := by group
  rw [this, ← h1]

end Ext3Compat

namespace Ext3Data

variable {T Q : Subgroup D} {T' : Subgroup E} {y t₀ : D} {y' : E} {ι : D → E}
  (h : Ext3Data T Q y t₀)

include h

theorem twist (hc : Ext3Compat T Q T' y t₀ y' ι) (hy'3 : y' ^ 3 = 1) {s : D} (hs : s ∈ T)
    {i : ℕ} (hi : i < 3) :
    ∃ t' ∈ T, ∃ k : ℕ, k < 3 ∧ y ^ i * s = t' * y ^ k ∧ y' ^ i * ι s = ι t' * y' ^ k := by
  have hyc := h.y_cube
  have hQT := h.Q_le
  have hy'inv : y'⁻¹ = y' ^ 2 := by rw [inv_eq_iff_mul_eq_one, ← pow_succ', hy'3]
  interval_cases i
  · exact ⟨s, hs, 0, by norm_num, by simp, by simp⟩
  · rcases h.T_eq s hs with hq | hq
    · refine ⟨y * s * y⁻¹, hQT (h.conj_Q s hq), 1, by norm_num, by group, ?_⟩
      rw [hc.conj_Q s hq]
      group
    · have hs' : s = (s * t₀⁻¹) * t₀ := by group
      have hq1 : y * (s * t₀⁻¹) * y⁻¹ ∈ T := hQT (h.conj_Q _ hq)
      have hqT : s * t₀⁻¹ ∈ T := hQT hq
      refine ⟨(y * (s * t₀⁻¹) * y⁻¹) * (y * t₀ * y), T.mul_mem hq1 h.conj_t₀, 2, by norm_num,
        ?_, ?_⟩
      · have e : (y * (s * t₀⁻¹) * y⁻¹) * (y * t₀ * y) * y ^ 2 = y * (s * t₀⁻¹) * t₀ * y ^ 3 := by
          group
        rw [e, hyc, mul_one]
        conv_lhs => rw [hs']
        group
      · rw [hc.mul _ hq1 _ h.conj_t₀, hc.conj_Q _ hq, hc.conj_t₀]
        have e : (y' * ι (s * t₀⁻¹) * y'⁻¹) * (y' * ι t₀ * y') * y' ^ 2 =
            y' * ι (s * t₀⁻¹) * ι t₀ * y' ^ 3 := by group
        rw [e, hy'3, mul_one]
        conv_lhs => rw [hs']
        rw [hc.mul _ hqT _ h.t₀_mem]
        group
  · rcases h.T_eq s hs with hq | hq
    · refine ⟨y⁻¹ * s * y, hQT (h.conj_Q' s hq), 2, by norm_num, ?_, ?_⟩
      · have e : y⁻¹ * s * y * y ^ 2 = y⁻¹ * s * y ^ 3 := by group
        rw [e, hyc, mul_one, ← h.y_inv]
      · rw [hc.conj_inv h hq]
        have e : y'⁻¹ * ι s * y' * y' ^ 2 = y'⁻¹ * ι s * y' ^ 3 := by group
        rw [e, hy'3, mul_one, ← hy'inv]
    · have hs' : s = (s * t₀⁻¹) * t₀ := by group
      have hq1 : y⁻¹ * (s * t₀⁻¹) * y ∈ T := hQT (h.conj_Q' _ hq)
      have hqT : s * t₀⁻¹ ∈ T := hQT hq
      refine ⟨(y⁻¹ * (s * t₀⁻¹) * y) * (y⁻¹ * t₀ * y⁻¹), T.mul_mem hq1 h.conj_t₀', 1,
        by norm_num, ?_, ?_⟩
      · have e : (y⁻¹ * (s * t₀⁻¹) * y) * (y⁻¹ * t₀ * y⁻¹) * y ^ 1 = y⁻¹ * (s * t₀⁻¹) * t₀ := by
          group
        rw [e, ← h.y_inv]
        conv_lhs => rw [hs']
        group
      · rw [hc.mul _ hq1 _ h.conj_t₀', hc.conj_inv h hq, hc.conj_t₀']
        have e : (y'⁻¹ * ι (s * t₀⁻¹) * y') * (y'⁻¹ * ι t₀ * y'⁻¹) * y' ^ 1 =
            y'⁻¹ * ι (s * t₀⁻¹) * ι t₀ := by group
        rw [e, ← hy'inv]
        conv_lhs => rw [hs']
        rw [hc.mul _ hqT _ h.t₀_mem]
        group

theorem nf_mul_y {g : D} (hg : ∃ t ∈ T, ∃ i : ℕ, i < 3 ∧ g = t * y ^ i) :
    ∃ t ∈ T, ∃ i : ℕ, i < 3 ∧ g * y = t * y ^ i := by
  obtain ⟨t, ht, i, hi, rfl⟩ := hg
  interval_cases i
  · exact ⟨t, ht, 1, by norm_num, by simp⟩
  · exact ⟨t, ht, 2, by norm_num, by group⟩
  · exact ⟨t, ht, 0, by norm_num, by rw [mul_assoc, ← pow_succ, h.y_cube]; simp⟩

theorem exists_nf (hc : Ext3Compat T Q T' y t₀ y' ι) (hy'3 : y' ^ 3 = 1) {g : D}
    (hg : g ∈ Subgroup.closure ((T : Set D) ∪ {y})) : ∃ t ∈ T, ∃ i : ℕ, i < 3 ∧ g = t * y ^ i := by
  have hT : ∀ {g : D}, (∃ t ∈ T, ∃ i : ℕ, i < 3 ∧ g = t * y ^ i) → ∀ s ∈ T,
      ∃ t ∈ T, ∃ i : ℕ, i < 3 ∧ g * s = t * y ^ i := by
    intro g hg s hs
    obtain ⟨t, ht, i, hi, rfl⟩ := hg
    obtain ⟨t', ht', k, hk, e, -⟩ := h.twist hc hy'3 hs hi
    exact ⟨t * t', T.mul_mem ht ht', k, hk, by rw [mul_assoc, e, ← mul_assoc]⟩
  induction hg using Subgroup.closure_induction_right with
  | one => exact ⟨1, T.one_mem, 0, by norm_num, by simp⟩
  | mul_right x hx s hs ih =>
    rcases hs with hs | hs
    · exact hT ih s hs
    · rw [Set.mem_singleton_iff] at hs
      subst hs
      exact h.nf_mul_y ih
  | mul_inv_cancel x hx s hs ih =>
    rcases hs with hs | hs
    · exact hT ih s⁻¹ (T.inv_mem hs)
    · rw [Set.mem_singleton_iff] at hs
      subst hs
      have h2 := h.nf_mul_y (h.nf_mul_y ih)
      rw [h.y_inv, pow_two, ← mul_assoc]
      exact h2

open Classical in
noncomputable def phiFun (T : Subgroup D) (y : D) (ι : D → E) (y' : E) (g : D) : E :=
  if hg : ∃ p : D × ℕ, p.1 ∈ T ∧ p.2 < 3 ∧ g = p.1 * y ^ p.2 then
    ι hg.choose.1 * y' ^ hg.choose.2 else 1

theorem phiFun_nf {t : D} (ht : t ∈ T) {i : ℕ} (hi : i < 3) :
    phiFun T y ι y' (t * y ^ i) = ι t * y' ^ i := by
  have hex : ∃ p : D × ℕ, p.1 ∈ T ∧ p.2 < 3 ∧ t * y ^ i = p.1 * y ^ p.2 := ⟨(t, i), ht, hi, rfl⟩
  unfold phiFun
  rw [dite_eq_left_of_eq_true (eq_true hex)]
  obtain ⟨h1, h2, h3⟩ := hex.choose_spec
  obtain ⟨e1, e2⟩ := h.nf_unique ht h1 hi h2 h3
  rw [← e1, ← e2]

theorem phiFun_mul_T (hc : Ext3Compat T Q T' y t₀ y' ι) (hy'3 : y' ^ 3 = 1) {g : D}
    (hg : ∃ t ∈ T, ∃ i : ℕ, i < 3 ∧ g = t * y ^ i) {s : D} (hs : s ∈ T) :
    phiFun T y ι y' (g * s) = phiFun T y ι y' g * ι s := by
  obtain ⟨t, ht, i, hi, rfl⟩ := hg
  obtain ⟨t', ht', k, hk, e, e'⟩ := h.twist hc hy'3 hs hi
  have hx : t * y ^ i * s = (t * t') * y ^ k := by rw [mul_assoc, e, ← mul_assoc]
  rw [hx, h.phiFun_nf (T.mul_mem ht ht') hk, h.phiFun_nf ht hi, hc.mul t ht t' ht',
    mul_assoc, mul_assoc, ← e']

theorem phiFun_mul_y (hy'3 : y' ^ 3 = 1) {g : D}
    (hg : ∃ t ∈ T, ∃ i : ℕ, i < 3 ∧ g = t * y ^ i) :
    phiFun T y ι y' (g * y) = phiFun T y ι y' g * y' := by
  obtain ⟨t, ht, i, hi, rfl⟩ := hg
  interval_cases i
  · rw [show t * y ^ 0 * y = t * y ^ 1 by simp, h.phiFun_nf ht (by norm_num),
      h.phiFun_nf ht (by norm_num)]
    simp
  · rw [show t * y ^ 1 * y = t * y ^ 2 by group, h.phiFun_nf ht (by norm_num),
      h.phiFun_nf ht (by norm_num)]
    group
  · rw [show t * y ^ 2 * y = t * y ^ 0 by rw [mul_assoc, ← pow_succ, h.y_cube]; simp,
      h.phiFun_nf ht (by norm_num), h.phiFun_nf ht (by norm_num)]
    rw [mul_assoc, ← pow_succ, hy'3]
    simp

theorem phiFun_mul_ypow (hy'3 : y' ^ 3 = 1) {g : D}
    (hg : ∃ t ∈ T, ∃ i : ℕ, i < 3 ∧ g = t * y ^ i) (j : ℕ) :
    phiFun T y ι y' (g * y ^ j) = phiFun T y ι y' g * y' ^ j ∧
      ∃ t ∈ T, ∃ i : ℕ, i < 3 ∧ g * y ^ j = t * y ^ i := by
  induction j with
  | zero => exact ⟨by simp, by simpa using hg⟩
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have e : g * y ^ (n + 1) = g * y ^ n * y := by rw [pow_succ, mul_assoc]
    rw [e, h.phiFun_mul_y hy'3 ih2, ih1, pow_succ, mul_assoc]
    exact ⟨rfl, h.nf_mul_y ih2⟩

theorem phiFun_mul (hc : Ext3Compat T Q T' y t₀ y' ι) (hy'3 : y' ^ 3 = 1) {g k : D}
    (hg : ∃ t ∈ T, ∃ i : ℕ, i < 3 ∧ g = t * y ^ i)
    (hk : ∃ t ∈ T, ∃ i : ℕ, i < 3 ∧ k = t * y ^ i) :
    phiFun T y ι y' (g * k) = phiFun T y ι y' g * phiFun T y ι y' k := by
  obtain ⟨s, hs, j, hj, rfl⟩ := hk
  have hgs : ∃ t ∈ T, ∃ i : ℕ, i < 3 ∧ g * s = t * y ^ i := by
    obtain ⟨t, ht, i, hi, rfl⟩ := hg
    obtain ⟨t', ht', k, hk, e, -⟩ := h.twist hc hy'3 hs hi
    exact ⟨t * t', T.mul_mem ht ht', k, hk, by rw [mul_assoc, e, ← mul_assoc]⟩
  rw [← mul_assoc, (h.phiFun_mul_ypow hy'3 hgs j).1, h.phiFun_mul_T hc hy'3 hg hs,
    h.phiFun_nf hs hj, mul_assoc]

theorem exists_mulEquiv (hc : Ext3Compat T Q T' y t₀ y' ι) (hy'3 : y' ^ 3 = 1) (hy'T : y' ∉ T') :
    ∃ φ : ↥(Subgroup.closure ((T : Set D) ∪ {y})) ≃*
        ↥(Subgroup.closure ((T' : Set E) ∪ {y'})),
      (∀ (t : D) (ht : t ∈ T),
        ((φ ⟨t, Subgroup.subset_closure (Or.inl ht)⟩ : ↥(Subgroup.closure ((T' : Set E) ∪ {y'})))
          : E) = ι t) ∧
      ((φ ⟨y, Subgroup.subset_closure (Or.inr rfl)⟩ : ↥(Subgroup.closure ((T' : Set E) ∪ {y'})))
        : E) = y' := by
  set Gc : Subgroup D := Subgroup.closure ((T : Set D) ∪ {y}) with hGc
  set G'c : Subgroup E := Subgroup.closure ((T' : Set E) ∪ {y'}) with hG'c
  have hy'inv : y'⁻¹ = y' ^ 2 := by rw [inv_eq_iff_mul_eq_one, ← pow_succ', hy'3]
  have hy'mem : y' ∈ G'c := Subgroup.subset_closure (Or.inr rfl)
  have hT'mem : ∀ u ∈ T', u ∈ G'c := fun u hu => Subgroup.subset_closure (Or.inl hu)
  have hmem : ∀ g ∈ Gc, phiFun T y ι y' g ∈ G'c := by
    intro g hg
    obtain ⟨t, ht, i, hi, rfl⟩ := h.exists_nf hc hy'3 hg
    rw [h.phiFun_nf ht hi]
    exact G'c.mul_mem (hT'mem _ (hc.mem t ht)) (G'c.pow_mem hy'mem i)
  have hone : phiFun T y ι y' 1 = 1 := by
    have : phiFun T y ι y' (1 * y ^ 0) = ι 1 * y' ^ 0 := h.phiFun_nf T.one_mem (by norm_num)
    simpa [hc.map_one] using this
  let Φ : ↥Gc →* ↥G'c :=
    { toFun := fun g => ⟨phiFun T y ι y' g, hmem g g.2⟩
      map_one' := Subtype.ext hone
      map_mul' := fun g k => Subtype.ext
        (h.phiFun_mul hc hy'3 (h.exists_nf hc hy'3 g.2) (h.exists_nf hc hy'3 k.2)) }
  have hinj : Function.Injective Φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    have hg1 : phiFun T y ι y' g = 1 := congrArg Subtype.val hg
    obtain ⟨t, ht, i, hi, hgt⟩ := h.exists_nf hc hy'3 g.2
    rw [hgt, h.phiFun_nf ht hi] at hg1
    have hy'2 : y' ^ 2 ∉ T' := by
      rw [← hy'inv]
      exact fun hy => hy'T (by simpa using T'.inv_mem hy)
    have hit : y' ^ i ∈ T' := by
      rw [eq_inv_of_mul_eq_one_right hg1]
      exact T'.inv_mem (hc.mem t ht)
    have hi0 : i = 0 := by
      interval_cases i
      · rfl
      · exact absurd hit (by simpa using hy'T)
      · exact absurd hit hy'2
    subst hi0
    have h1 : ι t = 1 := by simpa using hg1
    have ht1 : t = 1 := hc.inj t ht 1 T.one_mem (by rw [h1, hc.map_one])
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    rw [hgt, ht1]
    simp
  have hstep : ∀ {x : E}, (∃ t ∈ T, ∃ i : ℕ, i < 3 ∧ x = ι t * y' ^ i) →
      ∃ t ∈ T, ∃ i : ℕ, i < 3 ∧ x * y' = ι t * y' ^ i := by
    rintro x ⟨t, ht, i, hi, rfl⟩
    interval_cases i
    · exact ⟨t, ht, 1, by norm_num, by simp⟩
    · exact ⟨t, ht, 2, by norm_num, by group⟩
    · exact ⟨t, ht, 0, by norm_num, by rw [mul_assoc, ← pow_succ, hy'3]; simp⟩
  have hY : ∀ {x : E}, x ∈ G'c → ∃ t ∈ T, ∃ i : ℕ, i < 3 ∧ x = ι t * y' ^ i := by
    intro x hx
    have hT : ∀ {x : E}, (∃ t ∈ T, ∃ i : ℕ, i < 3 ∧ x = ι t * y' ^ i) → ∀ u ∈ T',
        ∃ t ∈ T, ∃ i : ℕ, i < 3 ∧ x * u = ι t * y' ^ i := by
      rintro x ⟨t, ht, i, hi, rfl⟩ u hu
      obtain ⟨s, hs, rfl⟩ := hc.surj u hu
      obtain ⟨t', ht', k, hk, -, e'⟩ := h.twist hc hy'3 hs hi
      exact ⟨t * t', T.mul_mem ht ht', k, hk,
        by rw [hc.mul t ht t' ht']; simp only [mul_assoc]; rw [e']⟩
    induction hx using Subgroup.closure_induction_right with
    | one => exact ⟨1, T.one_mem, 0, by norm_num, by simp [hc.map_one]⟩
    | mul_right x hx u hu ih =>
      rcases hu with hu | hu
      · exact hT ih u hu
      · rw [Set.mem_singleton_iff] at hu
        subst hu
        exact hstep ih
    | mul_inv_cancel x hx u hu ih =>
      rcases hu with hu | hu
      · exact hT ih u⁻¹ (T'.inv_mem hu)
      · rw [Set.mem_singleton_iff] at hu
        subst hu
        have h2 := hstep (hstep ih)
        rw [hy'inv, pow_two, ← mul_assoc]
        exact h2
  have hsurj : Function.Surjective Φ := by
    intro g'
    obtain ⟨t, ht, i, hi, hg'⟩ := hY g'.2
    have hmemG : t * y ^ i ∈ Gc :=
      Gc.mul_mem (Subgroup.subset_closure (Or.inl ht)) (Gc.pow_mem (Subgroup.subset_closure
        (Or.inr rfl)) i)
    refine ⟨⟨t * y ^ i, hmemG⟩, Subtype.ext ?_⟩
    show phiFun T y ι y' (t * y ^ i) = (g' : E)
    rw [h.phiFun_nf ht hi, hg']
  refine ⟨MulEquiv.ofBijective Φ ⟨hinj, hsurj⟩, fun t ht => ?_, ?_⟩
  · show phiFun T y ι y' t = ι t
    have := h.phiFun_nf (ι := ι) (y' := y') ht (show 0 < 3 by norm_num)
    simpa using this
  · show phiFun T y ι y' y = y'
    have := h.phiFun_nf (ι := ι) (y' := y') T.one_mem (show 1 < 3 by norm_num)
    simpa [hc.map_one] using this

end Ext3Data

end CFSG.Quasithin.F6.GoldAmL4
