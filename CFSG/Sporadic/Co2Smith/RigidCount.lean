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

namespace CFSG.Sporadic.Co2Smith

theorem card_modEq_fixed {X : Type*} [Finite X] {p n : ℕ} [Fact p.Prime] (f : X → X)
    (hf : ∀ x, f^[p ^ n] x = x) : Nat.card X ≡ Nat.card {x // f x = x} [MOD p] := by
  classical
  have := Fintype.ofFinite X
  let g : Function.End X := f
  have hf' : g ^ p ^ n = 1 := funext hf
  have h := Equiv.Perm.card_fixedPoints_modEq (α := X) hf'
  rw [Nat.card_eq_fintype_card]
  convert h using 1
  rw [← Nat.card_eq_fintype_card]
  rfl

theorem ratio_of_modEq_five {a b : ℕ} (hab : a ∣ b) (hb : b ∣ 2 ^ 9) (h5 : b ≡ a [MOD 5]) :
    b = a ∨ b = 16 * a ∨ b = 256 * a := by
  obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hb
  obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hab
  unfold Nat.ModEq at h5
  have key : ∀ j < 10, ∀ i < 10, i ≤ j → 2 ^ j % 5 = 2 ^ i % 5 →
      2 ^ j = 2 ^ i ∨ 2 ^ j = 16 * 2 ^ i ∨ 2 ^ j = 256 * 2 ^ i := by decide
  exact key j (by omega) i (by omega) hi h5

section Elementary

variable {A : Type*} [Group A]

@[expose] def fixSub (σ : A →* A) : Subgroup A where
  carrier := {a | σ a = a}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, map_mul] at *
    rw [ha, hb]
  one_mem' := map_one σ
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq, map_inv] at *
    rw [ha]

theorem mem_fixSub {σ : A →* A} {a : A} : a ∈ fixSub σ ↔ σ a = a := Iff.rfl

theorem comm4 (hc : ∀ a b : A, a * b = b * a) (a b c d : A) :
    a * b * (c * d) = a * c * (b * d) := by
  rw [mul_assoc, ← mul_assoc b, hc b c, mul_assoc c, ← mul_assoc]

theorem card_le_sq_fixSub [Finite A] (hc : ∀ a b : A, a * b = b * a) (σ : A →* A)
    (B : Subgroup A) (he : ∀ b ∈ B, b * b = 1) (hB : ∀ b ∈ B, σ b ∈ B)
    (hσ : ∀ a, σ (σ a) = a) :
    Nat.card B ≤ Nat.card (B ⊓ fixSub σ : Subgroup A) ^ 2 := by
  let τ : B →* B :=
    { toFun := fun b => ⟨b * σ b, B.mul_mem b.2 (hB _ b.2)⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by
        ext
        simp only [Subgroup.coe_mul, map_mul]
        exact comm4 hc _ _ _ _ }
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup τ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange τ).toEquiv] at h1
  have hker : τ.ker.map B.subtype = B ⊓ fixSub σ := by
    ext a
    simp only [Subgroup.mem_map, MonoidHom.mem_ker, Subgroup.mem_inf, mem_fixSub]
    constructor
    · rintro ⟨b, hb, rfl⟩
      have hb' : (b : A) * σ b = 1 := congrArg Subtype.val hb
      refine ⟨b.2, ?_⟩
      have := eq_inv_of_mul_eq_one_right hb'
      rw [inv_eq_of_mul_eq_one_right (he b b.2)] at this
      exact this
    · rintro ⟨ha, hfix⟩
      refine ⟨⟨a, ha⟩, ?_, rfl⟩
      apply Subtype.ext
      show a * σ a = 1
      rw [hfix, he a ha]
  have hran : τ.range.map B.subtype ≤ B ⊓ fixSub σ := by
    rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
    refine ⟨(τ b).2, ?_⟩
    show σ (b * σ b) = b * σ b
    rw [map_mul, hσ, hc]
  have h2 : Nat.card τ.ker = Nat.card (B ⊓ fixSub σ : Subgroup A) := by
    rw [← hker, Subgroup.card_map_of_injective B.subtype_injective]
  have h3 : Nat.card τ.range ≤ Nat.card (B ⊓ fixSub σ : Subgroup A) := by
    rw [← Subgroup.card_map_of_injective B.subtype_injective]
    exact Subgroup.card_le_of_le hran
  rw [h1, sq]
  exact Nat.mul_le_mul h3 h2.le

@[expose] def prodMapSub {U V B : Subgroup A} (hU : U ≤ B) (hV : V ≤ B) (p : U × V) : B :=
  ⟨p.1 * p.2, B.mul_mem (hU p.1.2) (hV p.2.2)⟩

theorem prodMapSub_injective {U V B : Subgroup A} (hU : U ≤ B) (hV : V ≤ B) (hUV : U ⊓ V = ⊥) :
    Function.Injective (prodMapSub hU hV) := by
  rintro ⟨u, v⟩ ⟨u', v'⟩ h
  have h1 : (u : A) * v = u' * v' := congrArg Subtype.val h
  have h2 : (u' : A)⁻¹ * u = v' * (v : A)⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h1, mul_inv_cancel_right]
  have hmem : (u' : A)⁻¹ * u ∈ U ⊓ V :=
    ⟨U.mul_mem (U.inv_mem u'.2) u.2, by rw [h2]; exact V.mul_mem v'.2 (V.inv_mem v.2)⟩
  rw [hUV, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  have hv : (v : A) = v' := by
    rw [← hmem] at h1
    exact mul_left_cancel h1
  exact Prod.ext (Subtype.ext hmem.symm) (Subtype.ext hv)

theorem card_mul_card_le [Finite A] {U V B : Subgroup A} (hU : U ≤ B) (hV : V ≤ B)
    (hUV : U ⊓ V = ⊥) : Nat.card U * Nat.card V ≤ Nat.card B := by
  rw [← Nat.card_prod]
  exact Nat.card_le_card_of_injective _ (prodMapSub_injective hU hV hUV)

theorem exists_mul_of_card [Finite A] {U V B : Subgroup A} (hU : U ≤ B) (hV : V ≤ B)
    (hUV : U ⊓ V = ⊥) (hcard : Nat.card B ≤ Nat.card U * Nat.card V) :
    ∀ b ∈ B, ∃ u ∈ U, ∃ v ∈ V, b = u * v := by
  intro b hb
  have hbij := (prodMapSub_injective hU hV hUV).bijective_of_nat_card_le
    (by rw [Nat.card_prod]; exact hcard)
  obtain ⟨⟨u, v⟩, huv⟩ := hbij.2 ⟨b, hb⟩
  exact ⟨u, u.2, v, v.2, (congrArg Subtype.val huv).symm⟩

theorem decomp [Finite A] (hc : ∀ a b : A, a * b = b * a) (y σ : A →* A)
    (hy3 : ∀ a, y (y (y a)) = a) (hσ2 : ∀ a, σ (σ a) = a) (hσy : ∀ a, σ (y (σ a)) = y (y a))
    (B : Subgroup A) (he : ∀ b ∈ B, b * b = 1) (hyB : ∀ b ∈ B, y b ∈ B)
    (hσB : ∀ b ∈ B, σ b ∈ B) (hfpf : ∀ b ∈ B, y b = b → b = 1) :
    Nat.card (B ⊓ fixSub σ : Subgroup A) ^ 2 = Nat.card B ∧
      ∀ b ∈ B, ∃ c ∈ B ⊓ fixSub σ, ∃ c' ∈ B ⊓ fixSub σ, b = c * y c' := by
  set C := B ⊓ fixSub σ with hC
  have hyinj : Function.Injective y := fun a b h => by
    rw [← hy3 a, ← hy3 b, h]
  have hCB : C ≤ B := inf_le_left
  have hCyB : C.map y ≤ B := by
    rintro _ ⟨c, hc, rfl⟩
    exact hyB c (hCB hc)
  have hinf : C ⊓ C.map y = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨hvC, hvy⟩ := Subgroup.mem_inf.mp hv
    obtain ⟨u, huC, rfl⟩ := Subgroup.mem_map.mp hvy
    have huσ : σ u = u := (Subgroup.mem_inf.mp huC).2
    have hvσ : σ (y u) = y u := (Subgroup.mem_inf.mp hvC).2
    have hvB : y u ∈ B := (Subgroup.mem_inf.mp hvC).1
    rw [Subgroup.mem_bot]
    have h1 : σ (y u) = y (y u) := by
      have := hσy u
      rwa [huσ] at this
    have h2 : y (y u) = y u := by rw [← h1, hvσ]
    exact hfpf _ hvB h2
  have hcardy : Nat.card (C.map y) = Nat.card C := Subgroup.card_map_of_injective hyinj
  have hle1 := card_mul_card_le hCB hCyB hinf
  have hle2 := card_le_sq_fixSub hc σ B he hσB hσ2
  rw [hcardy] at hle1
  have heq : Nat.card C ^ 2 = Nat.card B := le_antisymm (by rw [sq]; exact hle1) hle2
  refine ⟨heq, fun b hb => ?_⟩
  obtain ⟨c, hc, v, ⟨c', hc', rfl⟩, rfl⟩ := exists_mul_of_card hCB hCyB hinf
    (by rw [hcardy, ← sq, heq]) b hb
  exact ⟨c, hc, c', hc', rfl⟩

@[expose] def normSub (hc : ∀ a b : A, a * b = b * a) (y : A →* A) : Subgroup A where
  carrier := {a | a * y a * y (y a) = 1}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, map_mul] at *
    calc a * b * (y a * y b) * (y (y a) * y (y b))
        = a * y a * (b * y b) * (y (y a) * y (y b)) := by rw [comm4 hc a b]
      _ = (a * y a * y (y a)) * (b * y b * y (y b)) := comm4 hc _ _ _ _
      _ = 1 := by rw [ha, hb, one_mul]
  one_mem' := by simp
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq, map_inv] at *
    have e : a⁻¹ * (y a)⁻¹ * (y (y a))⁻¹ = (a * y a * y (y a))⁻¹ := by
      rw [mul_inv_rev, mul_inv_rev, hc a⁻¹, hc _ (y (y a))⁻¹]
    rw [e, ha, inv_one]

theorem trivial_or_large [Finite A] (hc : ∀ a b : A, a * b = b * a) (y σ x : A →* A)
    (Ω : Subgroup A) (he : ∀ a ∈ Ω, a * a = 1)
    (hyΩ : ∀ a ∈ Ω, y a ∈ Ω) (hσΩ : ∀ a ∈ Ω, σ a ∈ Ω) (hxΩ : ∀ a ∈ Ω, x a ∈ Ω)
    (hy3 : ∀ a, y (y (y a)) = a) (hσ2 : ∀ a, σ (σ a) = a) (hσy : ∀ a, σ (y (σ a)) = y (y a))
    (hxy : ∀ a, x (y a) = y (x a)) (hxσ : ∀ a, x (σ a) = σ (x a))
    (h5 : ∀ U : Subgroup A, U ≤ Ω → (∀ u ∈ U, x u ∈ U) → Nat.card U % 5 = 1)
    (hcard : Nat.card Ω ∣ 2 ^ 9) :
    (∀ a ∈ Ω, y a = a) ∨
      (256 ≤ Nat.card Ω ∧ (Nat.card Ω ≤ 256 → ∀ a ∈ Ω, y a = a → a = 1)) := by
  have hyσ : ∀ a, y (σ a) = σ (y (y a)) := by
    intro a
    have h1 : ∀ b, σ (y b) = y (y (σ b)) := fun b => by
      have := hσy (σ b)
      rwa [hσ2] at this
    have h2 := h1 (y (y a))
    rw [hy3] at h2
    rw [h2, hy3]
  set W := Ω ⊓ normSub hc y with hW
  have hWΩ : W ≤ Ω := inf_le_left
  have hyW : ∀ b ∈ W, y b ∈ W := by
    intro b hb
    refine ⟨hyΩ b hb.1, ?_⟩
    have hb2 : b * y b * y (y b) = 1 := hb.2
    show y b * y (y b) * y (y (y b)) = 1
    rw [hy3, hc, ← mul_assoc]
    exact hb2
  have hσW : ∀ b ∈ W, σ b ∈ W := by
    intro b hb
    refine ⟨hσΩ b hb.1, ?_⟩
    have hb2 : b * y b * y (y b) = 1 := hb.2
    show σ b * y (σ b) * y (y (σ b)) = 1
    have e1 : y (σ b) = σ (y (y b)) := hyσ b
    have e2 : y (y (σ b)) = σ (y b) := by
      rw [e1, hyσ, hy3]
    rw [e2, e1, ← map_mul, ← map_mul, mul_assoc, hc (y (y b)), ← mul_assoc, hb2, map_one]
  have hfpfW : ∀ b ∈ W, y b = b → b = 1 := by
    intro b hb hyb
    have hb2 : b * y b * y (y b) = 1 := hb.2
    rw [hyb, hyb, he b hb.1, one_mul] at hb2
    exact hb2
  have heW : ∀ b ∈ W, b * b = 1 := fun b hb => he b (hWΩ hb)
  by_cases hWt : ∀ a ∈ W, a = 1
  · left
    intro a ha
    have hya := hyΩ a ha
    have hyya := hyΩ _ hya
    have ht : y a * y (y a) ∈ W := by
      refine ⟨Ω.mul_mem hya hyya, ?_⟩
      show y a * y (y a) * y (y a * y (y a)) * y (y (y a * y (y a))) = 1
      simp only [map_mul, hy3]
      calc y a * y (y a) * (y (y a) * a) * (a * y a)
          = y a * (y (y a) * y (y a)) * (a * (a * y a)) := by simp only [mul_assoc]
        _ = 1 := by rw [he _ hyya, ← mul_assoc a, he _ ha, mul_one, one_mul, he _ hya]
    have h1 := hWt _ ht
    have h2 : y (y a) = y a := by
      have := eq_inv_of_mul_eq_one_right h1
      rwa [inv_eq_of_mul_eq_one_right (he _ hya)] at this
    have h3 := congrArg y h2
    rw [hy3, h2] at h3
    exact h3.symm
  · right
    push Not at hWt
    obtain ⟨a0, ha0, ha0'⟩ := hWt
    obtain ⟨hsq, -⟩ := decomp hc y σ hy3 hσ2 hσy W heW hyW hσW hfpfW
    set C := W ⊓ fixSub σ with hC
    have hC5 : Nat.card C % 5 = 1 := by
      refine h5 C (inf_le_left.trans hWΩ) fun u hu => ?_
      have hu1 : u ∈ Ω := hu.1.1
      have hu2 : u * y u * y (y u) = 1 := hu.1.2
      have hu3 : σ u = u := hu.2
      refine ⟨⟨hxΩ u hu1, ?_⟩, ?_⟩
      · show x u * y (x u) * y (y (x u)) = 1
        rw [← hxy, ← hxy, ← map_mul, ← map_mul, hu2, map_one]
      · show σ (x u) = x u
        rw [← hxσ, hu3]
    have hCdvd : Nat.card C ∣ 2 ^ 9 :=
      (Subgroup.card_dvd_of_le (inf_le_left.trans hWΩ)).trans hcard
    have hW2 : 1 < Nat.card W := by
      rw [Subgroup.one_lt_card_iff_ne_bot]
      intro hbot
      rw [hbot, Subgroup.mem_bot] at ha0
      exact ha0' ha0
    have hC16 : 16 ≤ Nat.card C := by
      obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hCdvd
      rw [← hsq, hj'] at hW2
      rw [hj'] at hC5 ⊢
      have key : ∀ j < 10, 2 ^ j % 5 = 1 → 1 < (2 ^ j) ^ 2 → 16 ≤ 2 ^ j := by decide
      exact key j (by omega) hC5 hW2
    have hW256 : 256 ≤ Nat.card W := by
      rw [← hsq]
      calc 256 = 16 * 16 := by norm_num
        _ ≤ Nat.card C * Nat.card C := Nat.mul_le_mul hC16 hC16
        _ = Nat.card C ^ 2 := (sq _).symm
    have hWle : Nat.card W ≤ Nat.card Ω := Subgroup.card_le_of_le hWΩ
    refine ⟨hW256.trans hWle, fun hA b hb => ?_⟩
    have hWeq : W = Ω := Subgroup.eq_of_le_of_card_ge hWΩ (hA.trans hW256)
    exact hfpfW b (hWeq ▸ hb)

end Elementary

end CFSG.Sporadic.Co2Smith
