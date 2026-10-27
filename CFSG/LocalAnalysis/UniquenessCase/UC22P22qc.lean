module

import CFSG.Goldschmidt.Steps.G310Basic
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

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

section Helpers

variable {G : Type*} [Group G]

private theorem uc22p22qc_comm {V₀ : Subgroup G} (hexp : ∀ d ∈ V₀, d ^ 2 = 1) {d e : G} (hd : d ∈ V₀)
    (he : e ∈ V₀) : d * e = e * d := by
  have hinv : ∀ a ∈ V₀, a⁻¹ = a := fun a ha =>
    inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hexp a ha)
  calc d * e = (d * e)⁻¹ := (hinv _ (mul_mem hd he)).symm
    _ = e * d := by rw [mul_inv_rev, hinv d hd, hinv e he]

private theorem uc22p22qc_four_le_card {E : Subgroup G} [Finite E] {a b c d : G} (ha : a ∈ E)
    (hb : b ∈ E) (hc : c ∈ E) (hd : d ∈ E) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) : 4 ≤ Nat.card E := by
  classical
  let f : Fin 4 → E := ![⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ⟨d, hd⟩]
  have hf : Function.Injective f := by
    intro i j hij
    have hij' := congrArg Subtype.val hij
    fin_cases i <;> fin_cases j <;> simp_all [f]
  have := Nat.card_le_card_of_injective f hf
  simpa using this

private theorem uc22p22qc_conj_inj {x a b : G} (h : x * a * x⁻¹ = x * b * x⁻¹) : a = b :=
  mul_left_cancel (mul_right_cancel h)

private theorem uc22p22qc_conj_ne_one {x a : G} (ha : a ≠ 1) : x * a * x⁻¹ ≠ 1 := fun h =>
  ha (uc22p22qc_conj_inj (x := x) (by rw [h]; simp))

private theorem uc22p22qc_commute_of_coprime {x d : G} {m n : ℕ} (hmn : Nat.Coprime m n)
    (hx : x ^ n = 1) (hc : Commute (x ^ m) d) : Commute x d := by
  obtain ⟨k, hk⟩ := exists_pow_eq_self_of_coprime
    (Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hx) hmn)
  have := hc.pow_left k
  rwa [hk] at this

private theorem uc22p22qc_commute_sq {x d : G} (h : x * (x * d * x⁻¹) * x⁻¹ = d) :
    Commute (x ^ 2) d := by
  rw [sq]
  have e : x * x * d * (x * x)⁻¹ = x * (x * d * x⁻¹) * x⁻¹ := by group
  rw [h] at e
  exact mul_inv_eq_iff_eq_mul.1 e

private theorem uc22p22qc_commute_cube {x d : G} (h : x * (x * (x * d * x⁻¹) * x⁻¹) * x⁻¹ = d) :
    Commute (x ^ 3) d := by
  rw [pow_three']
  have e : x * x * x * d * (x * x * x)⁻¹ = x * (x * (x * d * x⁻¹) * x⁻¹) * x⁻¹ := by group
  rw [h] at e
  exact mul_inv_eq_iff_eq_mul.1 e

end Helpers

theorem uc22p22q_klein_action {G : Type*} [Group G] [Finite G] {V₀ : Subgroup G}
    (hcard : Nat.card V₀ ≤ 4) (hexp : ∀ d ∈ V₀, d ^ 2 = 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {x : G} (hxN : ∀ d ∈ V₀, x * d * x⁻¹ ∈ V₀) (hxp : x ^ p = 1)
    (hx : ∃ d ∈ V₀, x * d * x⁻¹ ≠ d) :
    Nat.card V₀ = 4 ∧ p = 3 ∧ ∀ d ∈ V₀, d ≠ 1 → x * d * x⁻¹ ≠ d := by
  obtain ⟨d₀, hd₀, hmove⟩ := hx
  have hsq : ∀ a ∈ V₀, a * a = 1 := fun a ha => by rw [← sq]; exact hexp a ha
  obtain ⟨d₁, hd₁def⟩ : ∃ d₁, x * d₀ * x⁻¹ = d₁ := ⟨_, rfl⟩
  have hd₁ : d₁ ∈ V₀ := hd₁def ▸ hxN d₀ hd₀
  have hd₀1 : d₀ ≠ 1 := by
    rintro rfl
    exact hmove (by simp)
  have hd₁1 : d₁ ≠ 1 := hd₁def ▸ uc22p22qc_conj_ne_one (x := x) hd₀1
  have hd₀d₁ : d₀ ≠ d₁ := fun h => hmove (hd₁def.trans h.symm)
  have hprod : d₀ * d₁ ∈ V₀ := mul_mem hd₀ hd₁
  have h3 : (1 : G) ≠ d₀ * d₁ := by
    intro h
    have h' : d₁ = d₀⁻¹ := eq_inv_of_mul_eq_one_right h.symm
    exact hd₀d₁ ((inv_eq_of_mul_eq_one_right (hsq d₀ hd₀)).symm.trans h'.symm)
  have h5 : d₀ ≠ d₀ * d₁ := fun h => hd₁1 (left_eq_mul.1 h)
  have h6 : d₁ ≠ d₀ * d₁ := fun h => hd₀1 (right_eq_mul.1 h)
  have hV : Nat.card V₀ = 4 :=
    le_antisymm hcard (uc22p22qc_four_le_card (one_mem V₀) hd₀ hd₁ hprod hd₀1.symm hd₁1.symm h3 hd₀d₁
      h5 h6)
  have hexh : ∀ y ∈ V₀, y = 1 ∨ y = d₀ ∨ y = d₁ ∨ y = d₀ * d₁ := fun y hy =>
    CFSG.Goldschmidt.G310.eq_of_card_four hV (one_mem V₀) hd₀ hd₁ hprod hd₀1.symm hd₁1.symm h3
      hd₀d₁ h5 h6 hy
  obtain ⟨d₂, hd₂def⟩ : ∃ d₂, x * d₁ * x⁻¹ = d₂ := ⟨_, rfl⟩
  have hd₂ : d₂ ∈ V₀ := hd₂def ▸ hxN d₁ hd₁
  have hd₂1 : d₂ ≠ 1 := hd₂def ▸ uc22p22qc_conj_ne_one (x := x) hd₁1
  have hd₂d₁ : d₂ ≠ d₁ := by
    intro h
    apply hd₀d₁
    apply uc22p22qc_conj_inj (x := x)
    rw [hd₁def, hd₂def, h]
  have hφ : d₂ = d₀ * d₁ → x * (d₀ * d₁) * x⁻¹ = d₀ := fun hB =>
    calc x * (d₀ * d₁) * x⁻¹ = (x * d₀ * x⁻¹) * (x * d₁ * x⁻¹) := by group
      _ = d₁ * (d₀ * d₁) := by rw [hd₁def, hd₂def, hB]
      _ = d₀ := by rw [← mul_assoc, uc22p22qc_comm hexp hd₁ hd₀, mul_assoc, hsq d₁ hd₁, mul_one]
  rcases hexh d₂ hd₂ with h | h | h | h
  · exact absurd h hd₂1
  ·
    exfalso
    have hc2 : Commute (x ^ 2) d₀ :=
      uc22p22qc_commute_sq (by rw [hd₁def, hd₂def, h])
    exact hmove (uc22p22qc_commute_of_coprime ((Nat.coprime_primes Nat.prime_two hp).2
      (Ne.symm hp2)) hxp hc2).mul_inv_cancel
  · exact absurd h hd₂d₁
  ·
    have hp3 : p = 3 := by
      by_contra hp3
      have hc3 : Commute (x ^ 3) d₀ :=
        uc22p22qc_commute_cube (by rw [hd₁def, hd₂def, h, hφ h])
      exact hmove (uc22p22qc_commute_of_coprime ((Nat.coprime_primes Nat.prime_three hp).2
        (Ne.symm hp3)) hxp hc3).mul_inv_cancel
    refine ⟨hV, hp3, fun d hd hd1 => ?_⟩
    rcases hexh d hd with h' | h' | h' | h'
    · exact absurd h' hd1
    · rw [h']
      exact hmove
    · rw [h', hd₂def]
      exact hd₂d₁
    · rw [h', hφ h]
      exact h5

theorem uc22p22q_coset_transitive {G : Type*} [Group G] [Finite G] {M C V₀ V : Subgroup G}
    (hCnorm : ∀ m ∈ M, ∀ c ∈ C, m * c * m⁻¹ ∈ C)
    (hV₀V : V₀ ≤ V) (hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    (hV₀card : Nat.card V₀ = 4)
    (hCV : ∀ c ∈ C, ∀ v ∈ V, c * v * c⁻¹ * v⁻¹ ∈ V₀)
    {u : G} (hu : u ∈ V) (hgen : Subgroup.closure {w : G | ∃ m ∈ M, w = m * u * m⁻¹} = V)
    {x : G} (hxC : x ∈ C) (hxu : x * u * x⁻¹ = u) (hx3 : x ^ 3 = 1)
    (hfpf : ∀ d ∈ V₀, d ≠ 1 → x * d * x⁻¹ ≠ d) :
    ∀ d ∈ V₀, ∃ c ∈ C, c * u * c⁻¹ = u * d := by
  have hP : ∀ y : G, (∃ c ∈ C, c * u * c⁻¹ * u⁻¹ = y) → y ∈ V₀ := by
    rintro y ⟨c, hc, rfl⟩
    exact hCV c hc u hu
  have hPφ : ∀ y : G, (∃ c ∈ C, c * u * c⁻¹ * u⁻¹ = y) →
      ∃ c ∈ C, c * u * c⁻¹ * u⁻¹ = x * y * x⁻¹ := by
    rintro y ⟨c, hc, rfl⟩
    refine ⟨x * c * x⁻¹, mul_mem (mul_mem hxC hc) (inv_mem hxC), ?_⟩
    calc x * c * x⁻¹ * u * (x * c * x⁻¹)⁻¹ * u⁻¹
        = x * c * x⁻¹ * (x * u * x⁻¹) * (x * c * x⁻¹)⁻¹ * (x * u * x⁻¹)⁻¹ := by rw [hxu]
      _ = x * (c * u * c⁻¹ * u⁻¹) * x⁻¹ := by group
  have hnt : ∃ c ∈ C, c * u * c⁻¹ * u⁻¹ ≠ 1 := by
    by_contra hall
    push Not at hall
    have hcu : ∀ c ∈ C, c * u * c⁻¹ = u := fun c hc => mul_inv_eq_one.1 (hall c hc)
    have hgensub : {w : G | ∃ m ∈ M, w = m * u * m⁻¹} ⊆ (Subgroup.centralizer {x} : Subgroup G) := by
      rintro _ ⟨m, hm, rfl⟩
      have hc' : m⁻¹ * x * m ∈ C := by
        have := hCnorm m⁻¹ (inv_mem hm) x hxC
        rwa [inv_inv] at this
      have h1 := hcu _ hc'
      have e : x * (m * u * m⁻¹) * x⁻¹ = m * u * m⁻¹ := by
        calc x * (m * u * m⁻¹) * x⁻¹ = m * (m⁻¹ * x * m * u * (m⁻¹ * x * m)⁻¹) * m⁻¹ := by group
          _ = m * u * m⁻¹ := by rw [h1]
      exact Subgroup.mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 e).symm
    have hVcent : V ≤ Subgroup.centralizer {x} :=
      hgen.symm.le.trans ((Subgroup.closure_le _).2 hgensub)
    haveI : Nontrivial V₀ := Finite.one_lt_card_iff_nontrivial.1 (by rw [hV₀card]; norm_num)
    obtain ⟨⟨d, hd⟩, hd1⟩ := exists_ne (1 : V₀)
    have hdc := Subgroup.mem_centralizer_singleton_iff.1 (hVcent (hV₀V hd))
    refine hfpf d hd (fun h => hd1 (Subtype.ext h)) ?_
    rw [← hdc, mul_inv_cancel_right]
  obtain ⟨c₁, hc₁, he1⟩ := hnt
  obtain ⟨e, hedef⟩ : ∃ e, c₁ * u * c₁⁻¹ * u⁻¹ = e := ⟨_, rfl⟩
  have hPe : ∃ c ∈ C, c * u * c⁻¹ * u⁻¹ = e := ⟨c₁, hc₁, hedef⟩
  have he1' : e ≠ 1 := hedef ▸ he1
  obtain ⟨e₁, he₁def⟩ : ∃ e₁, x * e * x⁻¹ = e₁ := ⟨_, rfl⟩
  have hPe₁ : ∃ c ∈ C, c * u * c⁻¹ * u⁻¹ = e₁ := he₁def ▸ hPφ e hPe
  obtain ⟨e₂, he₂def⟩ : ∃ e₂, x * e₁ * x⁻¹ = e₂ := ⟨_, rfl⟩
  have hPe₂ : ∃ c ∈ C, c * u * c⁻¹ * u⁻¹ = e₂ := he₂def ▸ hPφ e₁ hPe₁
  have he₁1 : e₁ ≠ 1 := he₁def ▸ uc22p22qc_conj_ne_one (x := x) he1'
  have he₂1 : e₂ ≠ 1 := he₂def ▸ uc22p22qc_conj_ne_one (x := x) he₁1
  have k4 : e ≠ e₁ := fun h => hfpf e (hP e hPe) he1' (he₁def.trans h.symm)
  have k5 : e ≠ e₂ := by
    intro h
    have h3 : x * e₂ * x⁻¹ = e := by
      rw [← he₂def, ← he₁def]
      have : x * (x * (x * e * x⁻¹) * x⁻¹) * x⁻¹ = x * x * x * e * (x * x * x)⁻¹ := by group
      rw [this, ← pow_three', hx3]
      simp
    apply k4
    calc e = x * e₂ * x⁻¹ := h3.symm
      _ = x * e * x⁻¹ := by rw [← h]
      _ = e₁ := he₁def
  have k6 : e₁ ≠ e₂ := by
    intro h
    apply k4
    apply uc22p22qc_conj_inj (x := x)
    rw [he₁def, he₂def]
    exact h
  intro d hd
  have hPd : ∃ c ∈ C, c * u * c⁻¹ * u⁻¹ = d := by
    rcases CFSG.Goldschmidt.G310.eq_of_card_four hV₀card (one_mem V₀) (hP e hPe) (hP e₁ hPe₁)
      (hP e₂ hPe₂) he1'.symm he₁1.symm he₂1.symm k4 k5 k6 hd with h | h | h | h
    · exact ⟨1, one_mem C, by rw [h]; simp⟩
    · rw [h]
      exact hPe
    · rw [h]
      exact hPe₁
    · rw [h]
      exact hPe₂
  obtain ⟨c, hc, hcd⟩ := hPd
  refine ⟨c, hc, ?_⟩
  calc c * u * c⁻¹ = d * u := mul_inv_eq_iff_eq_mul.1 hcd
    _ = u * d := hVab d (hV₀V hd) u hu

end CFSG.LocalAnalysis.UniquenessCase.UC22
