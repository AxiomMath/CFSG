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

public section

namespace CFSG.Quasithin.RuType

namespace Tv

variable {G : Type*} [Group G] {b c : G}

@[expose] def emb (b c : G) (v : ZMod 5 × ZMod 5) : G := b ^ v.1.val * c ^ v.2.val

theorem pow_eq_pow_val {g : G} (hg : g ^ 5 = 1) (n : ℕ) : g ^ n = g ^ (n : ZMod 5).val := by
  rw [ZMod.val_natCast]
  conv_lhs => rw [← Nat.div_add_mod n 5, pow_add, pow_mul, hg, one_pow, one_mul]

theorem pow_val_add {g : G} (hg : g ^ 5 = 1) (m n : ZMod 5) :
    g ^ (m + n).val = g ^ m.val * g ^ n.val := by
  rw [← pow_add, pow_eq_pow_val hg (m.val + n.val)]
  congr 2

theorem emb_add (hbc : b * c = c * b) (hb : b ^ 5 = 1) (hc : c ^ 5 = 1)
    (v w : ZMod 5 × ZMod 5) : emb b c (v + w) = emb b c v * emb b c w := by
  unfold emb
  rw [Prod.fst_add, Prod.snd_add, pow_val_add hb, pow_val_add hc]
  have h1 : Commute (c ^ v.2.val) (b ^ w.1.val) :=
    ((show Commute c b from hbc.symm).pow_left _).pow_right _
  calc b ^ v.1.val * b ^ w.1.val * (c ^ v.2.val * c ^ w.2.val)
      = b ^ v.1.val * (b ^ w.1.val * c ^ v.2.val) * c ^ w.2.val := by group
    _ = b ^ v.1.val * (c ^ v.2.val * b ^ w.1.val) * c ^ w.2.val := by rw [h1.eq]
    _ = b ^ v.1.val * c ^ v.2.val * (b ^ w.1.val * c ^ w.2.val) := by group

theorem emb_nsmul (hbc : b * c = c * b) (hb : b ^ 5 = 1) (hc : c ^ 5 = 1)
    (v : ZMod 5 × ZMod 5) (k : ℕ) : emb b c (k • v) = emb b c v ^ k := by
  induction k with
  | zero => simp [emb]
  | succ k ih => rw [succ_nsmul, emb_add hbc hb hc, ih, pow_succ]

theorem val_one_five : (1 : ZMod 5).val = 1 := rfl

theorem emb_e1 : emb b c ((1 : ZMod 5), (0 : ZMod 5)) = b := by
  simp [emb, val_one_five]

theorem emb_e2 : emb b c ((0 : ZMod 5), (1 : ZMod 5)) = c := by
  simp [emb, val_one_five]

@[expose] def lin (A : Matrix (Fin 2) (Fin 2) (ZMod 5)) (v : ZMod 5 × ZMod 5) :
    ZMod 5 × ZMod 5 :=
  (A 0 0 * v.1 + A 0 1 * v.2, A 1 0 * v.1 + A 1 1 * v.2)

theorem lin_mul (A B : Matrix (Fin 2) (Fin 2) (ZMod 5)) (v : ZMod 5 × ZMod 5) :
    lin (A * B) v = lin A (lin B v) := by
  simp only [lin, Matrix.mul_apply, Fin.sum_univ_two]
  ext <;> ring

theorem lin_one (v : ZMod 5 × ZMod 5) : lin 1 v = v := by
  simp [lin]

theorem conj_emb (hbc : b * c = c * b) (hb : b ^ 5 = 1) (hc : c ^ 5 = 1) {x : G}
    (A : Matrix (Fin 2) (Fin 2) (ZMod 5))
    (h1 : x * b * x⁻¹ = emb b c (A 0 0, A 1 0)) (h2 : x * c * x⁻¹ = emb b c (A 0 1, A 1 1))
    (v : ZMod 5 × ZMod 5) : x * emb b c v * x⁻¹ = emb b c (lin A v) := by
  have hconj : ∀ g h : G, x * (g * h) * x⁻¹ = (x * g * x⁻¹) * (x * h * x⁻¹) := fun g h => by
    group
  have hpow : ∀ (g : G) (k : ℕ), x * g ^ k * x⁻¹ = (x * g * x⁻¹) ^ k := fun g k =>
    (conj_pow).symm
  conv_lhs => rw [emb]
  rw [hconj, hpow, hpow, h1, h2]
  have e : lin A v = v.1.val • (A 0 0, A 1 0) + v.2.val • (A 0 1, A 1 1) := by
    simp only [lin]
    ext <;> simp [mul_comm]
  rw [e, emb_add hbc hb hc, emb_nsmul hbc hb hc, emb_nsmul hbc hb hc]

theorem conj_pow_emb (hbc : b * c = c * b) (hb : b ^ 5 = 1) (hc : c ^ 5 = 1) {x : G}
    (A : Matrix (Fin 2) (Fin 2) (ZMod 5))
    (h1 : x * b * x⁻¹ = emb b c (A 0 0, A 1 0)) (h2 : x * c * x⁻¹ = emb b c (A 0 1, A 1 1))
    (k : ℕ) (v : ZMod 5 × ZMod 5) : x ^ k * emb b c v * (x ^ k)⁻¹ = emb b c (lin (A ^ k) v) := by
  induction k generalizing v with
  | zero => simp [lin_one]
  | succ k ih =>
    rw [pow_succ', pow_succ', lin_mul]
    calc x * x ^ k * emb b c v * (x * x ^ k)⁻¹ = x * (x ^ k * emb b c v * (x ^ k)⁻¹) * x⁻¹ := by
          group
      _ = x * emb b c (lin (A ^ k) v) * x⁻¹ := by rw [ih]
      _ = emb b c (lin A (lin (A ^ k) v)) := conj_emb hbc hb hc A h1 h2 _

theorem conj_pow_transv {x₂ : G} {m : ℕ}
    (h2b : x₂ * b * x₂⁻¹ = b * c ^ m) (h2c : x₂ * c * x₂⁻¹ = c) (k : ℕ) :
    x₂ ^ k * b * (x₂ ^ k)⁻¹ = b * c ^ (m * k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hcp : ∀ n : ℕ, x₂ * c ^ n * x₂⁻¹ = c ^ n := fun n => by rw [← conj_pow, h2c]
    calc x₂ ^ (k + 1) * b * (x₂ ^ (k + 1))⁻¹ = x₂ * (x₂ ^ k * b * (x₂ ^ k)⁻¹) * x₂⁻¹ := by
          rw [pow_succ']; group
      _ = x₂ * (b * c ^ (m * k)) * x₂⁻¹ := by rw [ih]
      _ = (x₂ * b * x₂⁻¹) * (x₂ * c ^ (m * k) * x₂⁻¹) := by group
      _ = b * c ^ m * c ^ (m * k) := by rw [h2b, hcp]
      _ = b * c ^ (m * (k + 1)) := by rw [mul_assoc, ← pow_add]; ring_nf

end Tv

theorem exists_mat_pow_three : ∀ l m : ZMod 5, l ≠ 0 → m ≠ 0 → ∃ k : ZMod 5,
    (!![1 + l * k * m, l; k * m, 1] : Matrix (Fin 2) (Fin 2) (ZMod 5)) ^ 3 = 1 := by
  decide

theorem exists_conj_pow_three {G : Type*} [Group G] {b c x₁ x₂ : G} (hbc : b * c = c * b)
    (hb : b ^ 5 = 1) (hc : c ^ 5 = 1) {l m : ℕ} (hl : (l : ZMod 5) ≠ 0) (hm : (m : ZMod 5) ≠ 0)
    (h1b : x₁ * b * x₁⁻¹ = b) (h1c : x₁ * c * x₁⁻¹ = c * b ^ l)
    (h2b : x₂ * b * x₂⁻¹ = b * c ^ m) (h2c : x₂ * c * x₂⁻¹ = c) :
    ∃ k : ℕ, (x₁ * x₂ ^ k) ^ 3 * b * ((x₁ * x₂ ^ k) ^ 3)⁻¹ = b ∧
      (x₁ * x₂ ^ k) ^ 3 * c * ((x₁ * x₂ ^ k) ^ 3)⁻¹ = c := by
  obtain ⟨k, hk⟩ := exists_mat_pow_three (l : ZMod 5) (m : ZMod 5) hl hm
  refine ⟨k.val, ?_⟩
  have hcb : Commute c b := hbc.symm
  have hcomm : ∀ p q : ℕ, c ^ p * b ^ q = b ^ q * c ^ p := fun p q =>
    ((hcb.pow_left p).pow_right q).eq
  set A : Matrix (Fin 2) (Fin 2) (ZMod 5) := !![1 + (l : ZMod 5) * k * m, l; k * m, 1] with hA
  have hc2 : ∀ n : ℕ, x₂ ^ n * c * (x₂ ^ n)⁻¹ = c := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc x₂ ^ (n + 1) * c * (x₂ ^ (n + 1))⁻¹ = x₂ * (x₂ ^ n * c * (x₂ ^ n)⁻¹) * x₂⁻¹ := by
            rw [pow_succ']; group
        _ = c := by rw [ih, h2c]
  have hxc : (x₁ * x₂ ^ k.val) * c * (x₁ * x₂ ^ k.val)⁻¹ = Tv.emb b c (A 0 1, A 1 1) := by
    have e1 : (x₁ * x₂ ^ k.val) * c * (x₁ * x₂ ^ k.val)⁻¹ =
        x₁ * (x₂ ^ k.val * c * (x₂ ^ k.val)⁻¹) * x₁⁻¹ := by group
    rw [e1, hc2, h1c]
    simp only [hA, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Tv.emb, Tv.val_one_five, pow_one]
    rw [← Tv.pow_eq_pow_val hb l]
    have := hcomm 1 l
    rwa [pow_one] at this
  have hxb : (x₁ * x₂ ^ k.val) * b * (x₁ * x₂ ^ k.val)⁻¹ = Tv.emb b c (A 0 0, A 1 0) := by
    have e1 : (x₁ * x₂ ^ k.val) * b * (x₁ * x₂ ^ k.val)⁻¹ =
        x₁ * (x₂ ^ k.val * b * (x₂ ^ k.val)⁻¹) * x₁⁻¹ := by group
    rw [e1, Tv.conj_pow_transv h2b h2c]
    have e2 : x₁ * (b * c ^ (m * k.val)) * x₁⁻¹ =
        (x₁ * b * x₁⁻¹) * (x₁ * c * x₁⁻¹) ^ (m * k.val) := by
      rw [conj_pow]; group
    rw [e2, h1b, h1c, (hcb.pow_right l).mul_pow, ← pow_mul]
    have e3 : b * (c ^ (m * k.val) * b ^ (l * (m * k.val))) =
        b ^ (1 + l * (m * k.val)) * c ^ (m * k.val) := by
      rw [hcomm, ← mul_assoc, ← pow_succ', add_comm]
    rw [e3]
    simp only [hA, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Tv.emb]
    rw [Tv.pow_eq_pow_val hb (1 + l * (m * k.val)), Tv.pow_eq_pow_val hc (m * k.val)]
    congr 3 <;> push_cast [ZMod.natCast_val, ZMod.cast_id', id] <;> ring
  have hx3 := Tv.conj_pow_emb hbc hb hc A hxb hxc 3
  rw [hk] at hx3
  refine ⟨?_, ?_⟩
  · have h := hx3 ((1 : ZMod 5), (0 : ZMod 5))
    rwa [Tv.lin_one, Tv.emb_e1] at h
  · have h := hx3 ((0 : ZMod 5), (1 : ZMod 5))
    rwa [Tv.lin_one, Tv.emb_e2] at h

theorem inv_of_normalizes_zpowers {G : Type*} [Group G] {s x : G} (hs : s * s = 1)
    (hx5 : x ^ 5 = 1) (hN : ∃ k : ℕ, s * x * s⁻¹ = x ^ k) (hC : s * x ≠ x * s) :
    s * x * s⁻¹ = x⁻¹ := by
  obtain ⟨k, hk⟩ := hN
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have hk5 : s * x * s⁻¹ = x ^ (k % 5) := by
    rw [hk]
    conv_lhs => rw [← Nat.div_add_mod k 5, pow_add, pow_mul, hx5, one_pow, one_mul]
  have hx : x = (x ^ (k % 5)) ^ (k % 5) := by
    calc x = s * (s * x * s⁻¹) * s⁻¹ := by
          rw [hsi, ← mul_assoc, ← mul_assoc, hs, one_mul, mul_assoc, hs, mul_one]
      _ = s * x ^ (k % 5) * s⁻¹ := by rw [hk5]
      _ = (s * x * s⁻¹) ^ (k % 5) := by rw [conj_pow]
      _ = (x ^ (k % 5)) ^ (k % 5) := by rw [hk5]
  have hlt : k % 5 < 5 := Nat.mod_lt _ (by norm_num)
  have hpow1 : ∀ m : ℕ, x ^ m = 1 → Nat.Coprime m 5 → x = 1 := by
    intro m hm hc
    have := (pow_gcd_eq_one (a := x)).mpr ⟨hm, hx5⟩
    rwa [hc.gcd_eq_one, pow_one] at this
  interval_cases hm : k % 5
  · exfalso; apply hC
    have h1 : x = 1 := by rw [hx]; simp
    rw [h1]; group
  · exfalso; apply hC
    have e : s * x * s⁻¹ = x := by rw [hk5, pow_one]
    calc s * x = s * x * s⁻¹ * s := by group
      _ = x * s := by rw [e]
  · exfalso; apply hC
    have h3 : x ^ 3 = 1 := by
      have h4 : x ^ 4 = x := by rw [← pow_mul] at hx; exact hx.symm
      calc x ^ 3 = x ^ 4 * x⁻¹ := by group
        _ = 1 := by rw [h4]; group
    rw [hpow1 3 h3 (by norm_num)]; group
  · exfalso; apply hC
    have h8 : x ^ 8 = 1 := by
      have h9 : x ^ 9 = x := by rw [← pow_mul] at hx; exact hx.symm
      calc x ^ 8 = x ^ 9 * x⁻¹ := by group
        _ = 1 := by rw [h9]; group
    rw [hpow1 8 h8 (by norm_num)]; group
  · rw [hk5]
    calc x ^ 4 = x ^ 5 * x⁻¹ := by group
      _ = x⁻¹ := by rw [hx5, one_mul]

@[expose] def emb3 {G : Type*} [Group G] (x₁ x₂ x₃ : G) (v : ZMod 5 × ZMod 5 × ZMod 5) : G :=
  x₁ ^ v.1.val * x₂ ^ v.2.1.val * x₃ ^ v.2.2.val

section Emb3

variable {G : Type*} [Group G] {x₁ x₂ x₃ : G} (h₁5 : x₁ ^ 5 = 1) (h₂5 : x₂ ^ 5 = 1)
  (h₃5 : x₃ ^ 5 = 1) (h12 : Commute x₁ x₂) (h13 : Commute x₁ x₃) (h23 : Commute x₂ x₃)
include h₁5 h₂5 h₃5 h12 h13 h23

theorem emb3_add (v w : ZMod 5 × ZMod 5 × ZMod 5) :
    emb3 x₁ x₂ x₃ (v + w) = emb3 x₁ x₂ x₃ v * emb3 x₁ x₂ x₃ w := by
  unfold emb3
  rw [Prod.fst_add, Prod.snd_add, Prod.fst_add, Prod.snd_add, Tv.pow_val_add h₁5,
    Tv.pow_val_add h₂5, Tv.pow_val_add h₃5]
  have c1 : Commute (x₂ ^ v.2.1.val) (x₁ ^ w.1.val) := (h12.symm.pow_left _).pow_right _
  have c2 : Commute (x₃ ^ v.2.2.val) (x₁ ^ w.1.val) := (h13.symm.pow_left _).pow_right _
  have c3 : Commute (x₃ ^ v.2.2.val) (x₂ ^ w.2.1.val) := (h23.symm.pow_left _).pow_right _
  calc x₁ ^ v.1.val * x₁ ^ w.1.val * (x₂ ^ v.2.1.val * x₂ ^ w.2.1.val) *
        (x₃ ^ v.2.2.val * x₃ ^ w.2.2.val)
      = x₁ ^ v.1.val * (x₁ ^ w.1.val * x₂ ^ v.2.1.val) * x₂ ^ w.2.1.val *
        (x₃ ^ v.2.2.val * x₃ ^ w.2.2.val) := by group
    _ = x₁ ^ v.1.val * (x₂ ^ v.2.1.val * x₁ ^ w.1.val) * x₂ ^ w.2.1.val *
        (x₃ ^ v.2.2.val * x₃ ^ w.2.2.val) := by rw [c1.eq]
    _ = x₁ ^ v.1.val * x₂ ^ v.2.1.val * (x₁ ^ w.1.val * (x₂ ^ w.2.1.val * x₃ ^ v.2.2.val)) *
        x₃ ^ w.2.2.val := by group
    _ = x₁ ^ v.1.val * x₂ ^ v.2.1.val * ((x₁ ^ w.1.val * x₃ ^ v.2.2.val) * x₂ ^ w.2.1.val) *
        x₃ ^ w.2.2.val := by rw [← c3.eq]; group
    _ = x₁ ^ v.1.val * x₂ ^ v.2.1.val * (x₃ ^ v.2.2.val * x₁ ^ w.1.val * x₂ ^ w.2.1.val) *
        x₃ ^ w.2.2.val := by rw [← c2.eq]
    _ = x₁ ^ v.1.val * x₂ ^ v.2.1.val * x₃ ^ v.2.2.val *
        (x₁ ^ w.1.val * x₂ ^ w.2.1.val * x₃ ^ w.2.2.val) := by group

omit h₁5 h₂5 h₃5 h12 h13 h23 in
theorem emb3_zero : emb3 x₁ x₂ x₃ 0 = 1 := by simp [emb3]

theorem emb3_comm (v w : ZMod 5 × ZMod 5 × ZMod 5) :
    Commute (emb3 x₁ x₂ x₃ v) (emb3 x₁ x₂ x₃ w) := by
  show _ * _ = _ * _
  rw [← emb3_add h₁5 h₂5 h₃5 h12 h13 h23, ← emb3_add h₁5 h₂5 h₃5 h12 h13 h23, add_comm]

theorem emb3_neg (v : ZMod 5 × ZMod 5 × ZMod 5) :
    emb3 x₁ x₂ x₃ (-v) = (emb3 x₁ x₂ x₃ v)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← emb3_add h₁5 h₂5 h₃5 h12 h13 h23, neg_add_cancel, emb3_zero]

end Emb3

theorem eq_zero_of_pow_val {G : Type*} [Group G] {x : G} (hx5 : x ^ 5 = 1) (hx1 : x ≠ 1)
    {a : ZMod 5} (h : x ^ a.val = 1) : a = 0 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have ho : orderOf x = 5 := orderOf_eq_prime hx5 hx1
  have hd := orderOf_dvd_of_pow_eq_one h
  rw [ho] at hd
  have hlt : a.val < 5 := ZMod.val_lt a
  have h0 : a.val = 0 := by
    obtain ⟨c, hc⟩ := hd
    rcases c with _ | c
    · simpa using hc
    · omega
  exact (ZMod.val_eq_zero a).mp h0

theorem false_of_signs {G : Type*} [Group G] {P : Subgroup G} (hP : Nat.card P = 125)
    (hPnc : ¬ ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) {x₁ x₂ x₃ s s' : G} (h₁ : x₁ ∈ P) (h₂ : x₂ ∈ P)
    (h₃ : x₃ ∈ P) (h₁5 : x₁ ^ 5 = 1) (h₂5 : x₂ ^ 5 = 1) (h₃5 : x₃ ^ 5 = 1)
    (h₁1 : x₁ ≠ 1) (h₂1 : x₂ ≠ 1) (h₃1 : x₃ ≠ 1)
    (h12 : Commute x₁ x₂) (h13 : Commute x₁ x₃) (h23 : Commute x₂ x₃)
    (hs1 : s * x₁ * s⁻¹ = x₁⁻¹) (hs2 : s * x₂ * s⁻¹ = x₂⁻¹) (hs3 : s * x₃ * s⁻¹ = x₃)
    (hs'1 : s' * x₁ * s'⁻¹ = x₁⁻¹) (hs'2 : s' * x₂ * s'⁻¹ = x₂) : False := by
  classical
  have hadd := emb3_add h₁5 h₂5 h₃5 h12 h13 h23
  have hcomm := emb3_comm h₁5 h₂5 h₃5 h12 h13 h23
  set e := emb3 x₁ x₂ x₃ with he
  have e1 : ∀ a : ZMod 5, e (a, 0, 0) = x₁ ^ a.val := fun a => by simp [he, emb3]
  have e2 : ∀ b : ZMod 5, e (0, b, 0) = x₂ ^ b.val := fun b => by simp [he, emb3]
  have e3 : ∀ c : ZMod 5, e (0, 0, c) = x₃ ^ c.val := fun c => by simp [he, emb3]
  have hsplit : ∀ v : ZMod 5 × ZMod 5 × ZMod 5,
      e v = e (v.1, 0, 0) * e (0, v.2.1, 0) * e (0, 0, v.2.2) := fun v => by
    rw [← hadd, ← hadd]; congr 1; ext <;> simp
  have hker : ∀ v, e v = 1 → v = 0 := by
    intro v hv
    set A := e (v.1, 0, 0)
    set B := e (0, v.2.1, 0)
    set C := e (0, 0, v.2.2)
    have hABC : A * B * C = 1 := by rw [← hsplit]; exact hv
    have hsA : s * A * s⁻¹ = A⁻¹ := by
      show s * e (v.1, 0, 0) * s⁻¹ = (e (v.1, 0, 0))⁻¹
      rw [e1, ← conj_pow, hs1, inv_pow]
    have hsB : s * B * s⁻¹ = B⁻¹ := by
      show s * e (0, v.2.1, 0) * s⁻¹ = (e (0, v.2.1, 0))⁻¹
      rw [e2, ← conj_pow, hs2, inv_pow]
    have hsC : s * C * s⁻¹ = C := by
      show s * e (0, 0, v.2.2) * s⁻¹ = e (0, 0, v.2.2)
      rw [e3, ← conj_pow, hs3]
    have hconj : A⁻¹ * B⁻¹ * C = 1 := by
      rw [← hsA, ← hsB, ← hsC]
      calc s * A * s⁻¹ * (s * B * s⁻¹) * (s * C * s⁻¹) = s * (A * B * C) * s⁻¹ := by group
        _ = 1 := by rw [hABC]; group
    have cAB : Commute A B := hcomm _ _
    have cAC : Commute A C := hcomm _ _
    have cBC : Commute B C := hcomm _ _
    have hcomm1 : A * B * A⁻¹ * B⁻¹ = 1 := by rw [cAB.eq]; group
    have hC2 : C * C = 1 := by
      have hc' : Commute (A⁻¹ * B⁻¹) C := (cAC.inv_left).mul_left (cBC.inv_left)
      have h : (A * B * C) * (A⁻¹ * B⁻¹ * C) = (A * B * A⁻¹ * B⁻¹) * (C * C) := by
        calc (A * B * C) * (A⁻¹ * B⁻¹ * C) = A * B * (C * (A⁻¹ * B⁻¹)) * C := by group
          _ = A * B * ((A⁻¹ * B⁻¹) * C) * C := by rw [hc'.eq]
          _ = (A * B * A⁻¹ * B⁻¹) * (C * C) := by group
      rw [hcomm1, one_mul, hABC, hconj, one_mul] at h
      exact h.symm
    have hc : v.2.2 = 0 := by
      have h2c : C * C = e (0, 0, v.2.2 + v.2.2) := by
        show e (0, 0, v.2.2) * e (0, 0, v.2.2) = _
        rw [← hadd]; congr 1
      rw [hC2, e3] at h2c
      have := eq_zero_of_pow_val h₃5 h₃1 h2c.symm
      have h2 : (2 : ZMod 5) * v.2.2 = 0 := by rw [two_mul]; exact this
      have : (3 : ZMod 5) * ((2 : ZMod 5) * v.2.2) = v.2.2 := by
        rw [← mul_assoc, show (3 : ZMod 5) * 2 = 1 by decide, one_mul]
      rw [← this, h2, mul_zero]
    have hC1 : C = 1 := by
      show e (0, 0, v.2.2) = 1
      rw [e3, hc]; simp
    rw [hC1, mul_one] at hABC hconj
    have hs'A : s' * A * s'⁻¹ = A⁻¹ := by
      show s' * e (v.1, 0, 0) * s'⁻¹ = (e (v.1, 0, 0))⁻¹
      rw [e1, ← conj_pow, hs'1, inv_pow]
    have hs'B : s' * B * s'⁻¹ = B := by
      show s' * e (0, v.2.1, 0) * s'⁻¹ = e (0, v.2.1, 0)
      rw [e2, ← conj_pow, hs'2]
    have hconj' : A⁻¹ * B = 1 := by
      rw [← hs'A, ← hs'B]
      calc s' * A * s'⁻¹ * (s' * B * s'⁻¹) = s' * (A * B) * s'⁻¹ := by group
        _ = 1 := by rw [hABC]; group
    have hA2 : A * A = 1 := by
      calc A * A = (A * B) * (A⁻¹ * B)⁻¹ := by group
        _ = 1 := by rw [hABC, hconj', inv_one, mul_one]
    have ha : v.1 = 0 := by
      have h2a : A * A = e (v.1 + v.1, 0, 0) := by
        show e (v.1, 0, 0) * e (v.1, 0, 0) = _
        rw [← hadd]; congr 1
      rw [hA2, e1] at h2a
      have := eq_zero_of_pow_val h₁5 h₁1 h2a.symm
      have h2 : (2 : ZMod 5) * v.1 = 0 := by rw [two_mul]; exact this
      have : (3 : ZMod 5) * ((2 : ZMod 5) * v.1) = v.1 := by
        rw [← mul_assoc, show (3 : ZMod 5) * 2 = 1 by decide, one_mul]
      rw [← this, h2, mul_zero]
    have hA1 : A = 1 := by
      show e (v.1, 0, 0) = 1
      rw [e1, ha]; simp
    rw [hA1, one_mul] at hABC
    have hb : v.2.1 = 0 := eq_zero_of_pow_val h₂5 h₂1 (by rw [← e2]; exact hABC)
    ext <;> simp [ha, hb, hc]
  have hneg : ∀ v, e (-v) = (e v)⁻¹ := fun v => emb3_neg h₁5 h₂5 h₃5 h12 h13 h23 v
  have hinj : Function.Injective e := by
    intro v w h
    have : e (v - w) = 1 := by
      rw [sub_eq_add_neg, hadd, hneg, h, mul_inv_cancel]
    exact sub_eq_zero.mp (hker _ this)
  have hmem : ∀ v, e v ∈ P := fun v =>
    mul_mem (mul_mem (pow_mem h₁ _) (pow_mem h₂ _)) (pow_mem h₃ _)
  let f : ZMod 5 × ZMod 5 × ZMod 5 → P := fun v => ⟨e v, hmem v⟩
  have hfinj : Function.Injective f := fun v w h => hinj (congrArg Subtype.val h)
  have hcard : Nat.card (ZMod 5 × ZMod 5 × ZMod 5) = Nat.card P := by
    rw [hP, Nat.card_prod, Nat.card_prod, Nat.card_zmod]
  have : Finite P := Nat.finite_of_card_ne_zero (by rw [hP]; norm_num)
  have hfsurj : Function.Surjective f := by
    have := (Function.Injective.bijective_of_nat_card_le hfinj hcard.ge).2
    exact this
  apply hPnc
  intro x hx y hy
  obtain ⟨v, hv⟩ := hfsurj ⟨x, hx⟩
  obtain ⟨w, hw⟩ := hfsurj ⟨y, hy⟩
  have hx' : e v = x := congrArg Subtype.val hv
  have hy' : e w = y := congrArg Subtype.val hw
  rw [← hx', ← hy']
  exact hcomm v w

end CFSG.Quasithin.RuType
