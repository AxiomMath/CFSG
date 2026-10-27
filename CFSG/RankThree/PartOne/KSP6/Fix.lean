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
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.RankThree.PartOne.KSP6

open Matrix

section Sym

variable {K : Type}

@[expose] def sym3 (x1 x2 x3 x4 x5 x6 : K) : Matrix (Fin 3) (Fin 3) K :=
  !![x1, x2, x3; x2, x4, x5; x3, x5, x6]

theorem sym3_inj {x1 x2 x3 x4 x5 x6 y1 y2 y3 y4 y5 y6 : K} :
    sym3 x1 x2 x3 x4 x5 x6 = sym3 y1 y2 y3 y4 y5 y6 ↔
      x1 = y1 ∧ x2 = y2 ∧ x3 = y3 ∧ x4 = y4 ∧ x5 = y5 ∧ x6 = y6 := by
  constructor
  · intro h
    have h1 := congrFun (congrFun h 0) 0
    have h2 := congrFun (congrFun h 0) 1
    have h3 := congrFun (congrFun h 0) 2
    have h4 := congrFun (congrFun h 1) 1
    have h5 := congrFun (congrFun h 1) 2
    have h6 := congrFun (congrFun h 2) 2
    simp [sym3] at h1 h2 h3 h4 h5 h6
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  · rintro ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl

theorem sym3_eq {C : Matrix (Fin 3) (Fin 3) K} (hC : Cᵀ = C) :
    C = sym3 (C 0 0) (C 0 1) (C 0 2) (C 1 1) (C 1 2) (C 2 2) := by
  have h : ∀ i j, C j i = C i j := fun i j => by
    have := congrFun (congrFun hC i) j
    simpa [Matrix.transpose_apply] using this
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sym3] <;> exact h _ _

end Sym

section Ut

variable {K : Type} [Field K]

@[expose] def ut3 (a b c : K) : Matrix (Fin 3) (Fin 3) K := !![1, a, c; 0, 1, b; 0, 0, 1]

theorem eq_ut3 {A : Matrix (Fin 3) (Fin 3) K} (h : ∃ a b c, A = ut3 a b c) :
    A = ut3 (A 0 1) (A 1 2) (A 0 2) := by
  obtain ⟨a, b, c, rfl⟩ := h
  simp [ut3]

theorem ut3_inj {a b c a' b' c' : K} : ut3 a b c = ut3 a' b' c' ↔ a = a' ∧ b = b' ∧ c = c' := by
  constructor
  · intro h
    have h1 := congrFun (congrFun h 0) 1
    have h2 := congrFun (congrFun h 1) 2
    have h3 := congrFun (congrFun h 0) 2
    simp [ut3] at h1 h2 h3
    exact ⟨h1, h2, h3⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

theorem ut3_one : ut3 (0 : K) 0 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ut3]

theorem ut3_mul_ut3 (a b c a' b' c' : K) :
    ut3 a b c * ut3 a' b' c' = ut3 (a + a') (b + b') (c + c' + a * b') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ut3, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

variable [CharP K 2]

theorem two_eq_zero_of : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2

theorem add_self_eq_zero_of (a : K) : a + a = 0 := by
  rw [← two_mul, two_eq_zero_of, zero_mul]

theorem ut3_mul_self (a b c : K) : ut3 a b c * ut3 a b c = ut3 0 0 (a * b) := by
  rw [ut3_mul_ut3, add_self_eq_zero_of a, add_self_eq_zero_of b, add_self_eq_zero_of c, zero_add]

theorem conj_sym3 (a b c x1 x2 x3 x4 x5 x6 : K) :
    ut3 a b c * sym3 x1 x2 x3 x4 x5 x6 * (ut3 a b c)ᵀ = sym3 (x1 + (a^2*x4 + c^2*x6))
      (x2 + (a*x4 + c*x5 + b*x3 + a*b*x5 + b*c*x6)) (x3 + (a*x5 + c*x6)) (x4 + b^2*x6)
      (x5 + b*x6) x6 := by
  have h2 : (2 : K) = 0 := two_eq_zero_of
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ut3, sym3, Matrix.mul_apply, Fin.sum_univ_three,
    Matrix.transpose_apply] <;> ring_nf <;> simp [h2]

theorem fixes_iff' {a b c : K} {C : Matrix (Fin 3) (Fin 3) K} (hC : Cᵀ = C) :
    ut3 a b c * C * (ut3 a b c)ᵀ = C ↔
      (a^2*C 1 1 + c^2*C 2 2 = 0 ∧ a*C 1 1 + c*C 1 2 + b*C 0 2 + a*b*C 1 2 + b*c*C 2 2 = 0 ∧
        a*C 1 2 + c*C 2 2 = 0 ∧ b^2*C 2 2 = 0 ∧ b*C 2 2 = 0) := by
  obtain ⟨x1, x2, x3, x4, x5, x6, rfl⟩ : ∃ x1 x2 x3 x4 x5 x6, C = sym3 x1 x2 x3 x4 x5 x6 :=
    ⟨_, _, _, _, _, _, sym3_eq hC⟩
  rw [conj_sym3, sym3_inj]
  simp [sym3]

end Ut

section Count

variable {K : Type} [Field K] [Finite K] [CharP K 2]

@[expose] def FixSet (H : Set (Matrix (Fin 3) (Fin 3) K)) : Type :=
  {C : Matrix (Fin 3) (Fin 3) K // Cᵀ = C ∧ ∀ A ∈ H, A * C * Aᵀ = C}

instance (H : Set (Matrix (Fin 3) (Fin 3) K)) : Finite (FixSet H) := by
  unfold FixSet
  infer_instance

omit [Field K] [Finite K] [CharP K 2] in
theorem card_K_pow_two : Nat.card (K × K) = Nat.card K ^ 2 := by
  rw [Nat.card_prod, sq]

omit [Field K] [Finite K] [CharP K 2] in
theorem card_K_pow_three : Nat.card (K × K × K) = Nat.card K ^ 3 := by
  rw [Nat.card_prod, Nat.card_prod]
  ring

abbrev SgI (H : Set (Matrix (Fin 3) (Fin 3) K)) : Type :=
  {y : K × K // ∀ A ∈ H, A 0 2 * y.2 + A 1 2 * y.1 = 0}

abbrev SgII (H : Set (Matrix (Fin 3) (Fin 3) K)) : Type :=
  {s : K × K × K // ∀ A ∈ H, A 0 1 * s.1 + A 0 2 * s.2.1 = 0 ∧
    A 0 1 * s.2.1 + A 0 2 * s.2.2 = 0}

theorem typeI_bound (H : Set (Matrix (Fin 3) (Fin 3) K))
    (hU : ∀ A ∈ H, ∃ a b c, A = ut3 a b c)
    (ha : ∀ A ∈ H, A 0 1 = 0) (hne : ∃ A ∈ H, A ≠ 1) :
    Nat.card H * Nat.card (FixSet H) ≤ Nat.card K ^ 5 := by
  classical
  have hform : ∀ A ∈ H, A = ut3 0 (A 1 2) (A 0 2) := fun A hA => by
    have := eq_ut3 (hU A hA)
    rwa [ha A hA] at this
  obtain ⟨A₀, hA₀H, hA₀1⟩ := hne
  have hcb₀ : ¬ (A₀ 1 2 = 0 ∧ A₀ 0 2 = 0) := by
    rintro ⟨h1, h2⟩
    apply hA₀1
    rw [hform A₀ hA₀H, h1, h2, ut3_one]
  have hcond : ∀ C : FixSet H, ∀ A ∈ H, A 0 2 * C.1 1 2 + A 1 2 * C.1 0 2 = 0 := by
    intro C A hA
    have h := (fixes_iff' (a := 0) (b := A 1 2) (c := A 0 2) C.2.1).1 (by
      rw [← hform A hA]; exact C.2.2 A hA)
    obtain ⟨-, h2, h3, -, -⟩ := h
    linear_combination h2 - A 1 2 * h3
  have hx6 : ∀ C : FixSet H, C.1 2 2 = 0 := by
    intro C
    have h := (fixes_iff' (a := 0) (b := A₀ 1 2) (c := A₀ 0 2) C.2.1).1 (by
      rw [← hform A₀ hA₀H]; exact C.2.2 A₀ hA₀H)
    obtain ⟨-, -, h3, -, h5⟩ := h
    by_cases hc : A₀ 0 2 = 0
    · have hb : A₀ 1 2 ≠ 0 := fun hb => hcb₀ ⟨hb, hc⟩
      exact (mul_eq_zero.1 h5).resolve_left hb
    · have h3' : A₀ 0 2 * C.1 2 2 = 0 := by linear_combination h3
      exact (mul_eq_zero.1 h3').resolve_left hc
  let f : FixSet H → (K × K × K) × SgI H := fun C =>
    ((C.1 0 0, C.1 0 1, C.1 1 1), ⟨(C.1 0 2, C.1 1 2), hcond C⟩)
  have hf : Function.Injective f := by
    intro C C' h
    simp only [f, Prod.mk.injEq] at h
    obtain ⟨⟨h1, h2, h4⟩, h'⟩ := h
    have h'' := congrArg Subtype.val h'
    simp only [Prod.mk.injEq] at h''
    obtain ⟨h3, h5⟩ := h''
    apply Subtype.ext
    rw [sym3_eq C.2.1, sym3_eq C'.2.1, h1, h2, h3, h4, h5, hx6 C, hx6 C']
  have hX : Nat.card (FixSet H) ≤ Nat.card K ^ 3 * Nat.card (SgI H) := by
    calc Nat.card (FixSet H) ≤ Nat.card ((K × K × K) × SgI H) :=
          Nat.card_le_card_of_injective f hf
      _ = Nat.card K ^ 3 * Nat.card (SgI H) := by rw [Nat.card_prod, card_K_pow_three]
  have hHSg : Nat.card H * Nat.card (SgI H) ≤ Nat.card K ^ 2 := by
    by_cases hy : ∃ y : SgI H, y.1 ≠ 0
    · obtain ⟨y, hy⟩ := hy
      have hH1 : Nat.card H ≤ Nat.card K := by
        by_cases hy1 : y.1.1 = 0
        · have hy2 : y.1.2 ≠ 0 := fun h2 => hy (Prod.ext hy1 h2)
          have hc0 : ∀ A ∈ H, A 0 2 = 0 := fun A hA => by
            have := y.2 A hA
            rw [hy1, mul_zero, add_zero] at this
            exact (mul_eq_zero.1 this).resolve_right hy2
          refine Nat.card_le_card_of_injective (fun A : H => A.1 1 2) ?_
          intro A B h
          apply Subtype.ext
          rw [hform A.1 A.2, hform B.1 B.2, hc0 A.1 A.2, hc0 B.1 B.2]
          simp only at h
          rw [h]
        · refine Nat.card_le_card_of_injective (fun A : H => A.1 0 2) ?_
          intro A B h
          apply Subtype.ext
          have hA := y.2 A.1 A.2
          have hB := y.2 B.1 B.2
          simp only at h
          have hb : A.1 1 2 = B.1 1 2 := by
            apply mul_right_cancel₀ hy1
            linear_combination hA - hB - y.1.2 * h
          rw [hform A.1 A.2, hform B.1 B.2, h, hb]
      have hS1 : Nat.card (SgI H) ≤ Nat.card K := by
        by_cases hc : A₀ 0 2 = 0
        · have hb : A₀ 1 2 ≠ 0 := fun hb => hcb₀ ⟨hb, hc⟩
          refine Nat.card_le_card_of_injective (fun z : SgI H => z.1.2) ?_
          intro z w h
          apply Subtype.ext
          have hz := z.2 A₀ hA₀H
          have hw := w.2 A₀ hA₀H
          rw [hc, zero_mul, zero_add] at hz hw
          have h1 : z.1.1 = 0 := (mul_eq_zero.1 hz).resolve_left hb
          have h2 : w.1.1 = 0 := (mul_eq_zero.1 hw).resolve_left hb
          simp only at h
          exact Prod.ext (h1.trans h2.symm) h
        · refine Nat.card_le_card_of_injective (fun z : SgI H => z.1.1) ?_
          intro z w h
          apply Subtype.ext
          have hz := z.2 A₀ hA₀H
          have hw := w.2 A₀ hA₀H
          simp only at h
          have h2 : z.1.2 = w.1.2 := by
            apply mul_left_cancel₀ hc
            linear_combination hz - hw - A₀ 1 2 * h
          exact Prod.ext h h2
      calc Nat.card H * Nat.card (SgI H) ≤ Nat.card K * Nat.card K := Nat.mul_le_mul hH1 hS1
        _ = Nat.card K ^ 2 := (sq _).symm
    · push Not at hy
      have hSg1 : Nat.card (SgI H) ≤ 1 := by
        rw [Finite.card_le_one_iff_subsingleton]
        exact ⟨fun y z => Subtype.ext ((hy y).trans (hy z).symm)⟩
      have hH2 : Nat.card H ≤ Nat.card K ^ 2 := by
        calc Nat.card H ≤ Nat.card (K × K) := Nat.card_le_card_of_injective
              (fun A : H => (A.1 0 2, A.1 1 2)) (by
                intro A B h
                apply Subtype.ext
                simp only [Prod.mk.injEq] at h
                rw [hform A.1 A.2, hform B.1 B.2, h.1, h.2])
          _ = Nat.card K ^ 2 := card_K_pow_two
      calc Nat.card H * Nat.card (SgI H) ≤ Nat.card K ^ 2 * 1 := Nat.mul_le_mul hH2 hSg1
        _ = Nat.card K ^ 2 := mul_one _
  calc Nat.card H * Nat.card (FixSet H) ≤ Nat.card H * (Nat.card K ^ 3 * Nat.card (SgI H)) :=
        Nat.mul_le_mul_left _ hX
    _ = Nat.card K ^ 3 * (Nat.card H * Nat.card (SgI H)) := by ring
    _ ≤ Nat.card K ^ 3 * Nat.card K ^ 2 := Nat.mul_le_mul_left _ hHSg
    _ = Nat.card K ^ 5 := by rw [← pow_add]

theorem typeII_bound (H : Set (Matrix (Fin 3) (Fin 3) K))
    (hU : ∀ A ∈ H, ∃ a b c, A = ut3 a b c)
    (hb : ∀ A ∈ H, A 1 2 = 0) (hne : ∃ A ∈ H, A ≠ 1) :
    Nat.card H * Nat.card (FixSet H) ≤ Nat.card K ^ 5 := by
  classical
  have hform : ∀ A ∈ H, A = ut3 (A 0 1) 0 (A 0 2) := fun A hA => by
    have := eq_ut3 (hU A hA)
    rwa [hb A hA] at this
  obtain ⟨A₀, hA₀H, hA₀1⟩ := hne
  have hac₀ : ¬ (A₀ 0 1 = 0 ∧ A₀ 0 2 = 0) := by
    rintro ⟨h1, h2⟩
    apply hA₀1
    rw [hform A₀ hA₀H, h1, h2, ut3_one]
  have hcond : ∀ C : FixSet H, ∀ A ∈ H, A 0 1 * C.1 1 1 + A 0 2 * C.1 1 2 = 0 ∧
      A 0 1 * C.1 1 2 + A 0 2 * C.1 2 2 = 0 := by
    intro C A hA
    have h := (fixes_iff' (a := A 0 1) (b := 0) (c := A 0 2) C.2.1).1 (by
      rw [← hform A hA]; exact C.2.2 A hA)
    obtain ⟨-, h2, h3, -, -⟩ := h
    exact ⟨by linear_combination h2, h3⟩
  let f : FixSet H → (K × K × K) × SgII H := fun C =>
    ((C.1 0 0, C.1 0 1, C.1 0 2), ⟨(C.1 1 1, C.1 1 2, C.1 2 2), hcond C⟩)
  have hf : Function.Injective f := by
    intro C C' h
    simp only [f, Prod.mk.injEq] at h
    obtain ⟨⟨h1, h2, h3⟩, h'⟩ := h
    have h'' := congrArg Subtype.val h'
    simp only [Prod.mk.injEq] at h''
    obtain ⟨h4, h5, h6⟩ := h''
    apply Subtype.ext
    rw [sym3_eq C.2.1, sym3_eq C'.2.1, h1, h2, h3, h4, h5, h6]
  have hX : Nat.card (FixSet H) ≤ Nat.card K ^ 3 * Nat.card (SgII H) := by
    calc Nat.card (FixSet H) ≤ Nat.card ((K × K × K) × SgII H) :=
          Nat.card_le_card_of_injective f hf
      _ = Nat.card K ^ 3 * Nat.card (SgII H) := by rw [Nat.card_prod, card_K_pow_three]
  have hHSg : Nat.card H * Nat.card (SgII H) ≤ Nat.card K ^ 2 := by
    by_cases hy : ∃ s : SgII H, s.1 ≠ 0
    · obtain ⟨s, hs⟩ := hy
      have hH1 : Nat.card H ≤ Nat.card K := by
        by_cases hs4 : s.1.1 = 0
        ·
          have hc0 : ∀ A ∈ H, A 0 2 = 0 := fun A hA => by
            obtain ⟨e1, e2⟩ := s.2 A hA
            rw [hs4, mul_zero, zero_add] at e1
            by_cases hs5 : s.1.2.1 = 0
            · have hs6 : s.1.2.2 ≠ 0 := fun h6 => hs (Prod.ext hs4 (Prod.ext hs5 h6))
              rw [hs5, mul_zero, zero_add] at e2
              exact (mul_eq_zero.1 e2).resolve_right hs6
            · exact (mul_eq_zero.1 e1).resolve_right hs5
          refine Nat.card_le_card_of_injective (fun A : H => A.1 0 1) ?_
          intro A B h
          apply Subtype.ext
          simp only at h
          rw [hform A.1 A.2, hform B.1 B.2, hc0 A.1 A.2, hc0 B.1 B.2, h]
        · refine Nat.card_le_card_of_injective (fun A : H => A.1 0 2) ?_
          intro A B h
          apply Subtype.ext
          simp only at h
          have eA := (s.2 A.1 A.2).1
          have eB := (s.2 B.1 B.2).1
          have ha : A.1 0 1 = B.1 0 1 := by
            apply mul_right_cancel₀ hs4
            linear_combination eA - eB - s.1.2.1 * h
          rw [hform A.1 A.2, hform B.1 B.2, h, ha]
      have hS1 : Nat.card (SgII H) ≤ Nat.card K := by
        by_cases ha0 : A₀ 0 1 = 0
        · have hc0 : A₀ 0 2 ≠ 0 := fun hc => hac₀ ⟨ha0, hc⟩
          refine Nat.card_le_card_of_injective (fun z : SgII H => z.1.1) ?_
          intro z w h
          apply Subtype.ext
          obtain ⟨ez1, ez2⟩ := z.2 A₀ hA₀H
          obtain ⟨ew1, ew2⟩ := w.2 A₀ hA₀H
          rw [ha0, zero_mul, zero_add] at ez1 ez2 ew1 ew2
          have h5z : z.1.2.1 = 0 := (mul_eq_zero.1 ez1).resolve_left hc0
          have h5w : w.1.2.1 = 0 := (mul_eq_zero.1 ew1).resolve_left hc0
          have h6z : z.1.2.2 = 0 := (mul_eq_zero.1 ez2).resolve_left hc0
          have h6w : w.1.2.2 = 0 := (mul_eq_zero.1 ew2).resolve_left hc0
          simp only at h
          exact Prod.ext h (Prod.ext (h5z.trans h5w.symm) (h6z.trans h6w.symm))
        · refine Nat.card_le_card_of_injective (fun z : SgII H => z.1.2.2) ?_
          intro z w h
          apply Subtype.ext
          obtain ⟨ez1, ez2⟩ := z.2 A₀ hA₀H
          obtain ⟨ew1, ew2⟩ := w.2 A₀ hA₀H
          simp only at h
          have h5 : z.1.2.1 = w.1.2.1 := by
            apply mul_left_cancel₀ ha0
            linear_combination ez2 - ew2 - A₀ 0 2 * h
          have h4 : z.1.1 = w.1.1 := by
            apply mul_left_cancel₀ ha0
            linear_combination ez1 - ew1 - A₀ 0 2 * h5
          exact Prod.ext h4 (Prod.ext h5 h)
      calc Nat.card H * Nat.card (SgII H) ≤ Nat.card K * Nat.card K := Nat.mul_le_mul hH1 hS1
        _ = Nat.card K ^ 2 := (sq _).symm
    · push Not at hy
      have hSg1 : Nat.card (SgII H) ≤ 1 := by
        rw [Finite.card_le_one_iff_subsingleton]
        exact ⟨fun y z => Subtype.ext ((hy y).trans (hy z).symm)⟩
      have hH2 : Nat.card H ≤ Nat.card K ^ 2 := by
        calc Nat.card H ≤ Nat.card (K × K) := Nat.card_le_card_of_injective
              (fun A : H => (A.1 0 1, A.1 0 2)) (by
                intro A B h
                apply Subtype.ext
                simp only [Prod.mk.injEq] at h
                rw [hform A.1 A.2, hform B.1 B.2, h.1, h.2])
          _ = Nat.card K ^ 2 := card_K_pow_two
      calc Nat.card H * Nat.card (SgII H) ≤ Nat.card K ^ 2 * 1 := Nat.mul_le_mul hH2 hSg1
        _ = Nat.card K ^ 2 := mul_one _
  calc Nat.card H * Nat.card (FixSet H) ≤ Nat.card H * (Nat.card K ^ 3 * Nat.card (SgII H)) :=
        Nat.mul_le_mul_left _ hX
    _ = Nat.card K ^ 3 * (Nat.card H * Nat.card (SgII H)) := by ring
    _ ≤ Nat.card K ^ 3 * Nat.card K ^ 2 := Nat.mul_le_mul_left _ hHSg
    _ = Nat.card K ^ 5 := by rw [← pow_add]

theorem card_mul_card_fix_le (H : Set (Matrix (Fin 3) (Fin 3) K))
    (hU : ∀ A ∈ H, ∃ a b c, A = ut3 a b c) (hsq : ∀ A ∈ H, A * A = 1)
    (hcomm : ∀ A ∈ H, ∀ B ∈ H, A * B = B * A) (hne : ∃ A ∈ H, A ≠ 1) :
    Nat.card H * Nat.card (FixSet H) ≤ Nat.card K ^ 5 := by
  have hab : ∀ A ∈ H, A 0 1 * A 1 2 = 0 := fun A hA => by
    have h := hsq A hA
    rw [eq_ut3 (hU A hA), ut3_mul_self, ← ut3_one, ut3_inj] at h
    exact h.2.2
  have hcm : ∀ A ∈ H, ∀ B ∈ H, A 0 1 * B 1 2 = B 0 1 * A 1 2 := fun A hA B hB => by
    have h := hcomm A hA B hB
    rw [eq_ut3 (hU A hA), eq_ut3 (hU B hB), ut3_mul_ut3, ut3_mul_ut3, ut3_inj] at h
    obtain ⟨-, -, h3⟩ := h
    linear_combination h3
  by_cases h : ∀ A ∈ H, A 0 1 = 0
  · exact typeI_bound H hU h hne
  · push Not at h
    obtain ⟨A, hA, ha⟩ := h
    have hbA : A 1 2 = 0 := (mul_eq_zero.1 (hab A hA)).resolve_left ha
    have hb : ∀ B ∈ H, B 1 2 = 0 := fun B hB => by
      have := hcm A hA B hB
      rw [hbA, mul_zero] at this
      exact (mul_eq_zero.1 this).resolve_left ha
    exact typeII_bound H hU hb hne

end Count

end CFSG.RankThree.PartOne.KSP6
