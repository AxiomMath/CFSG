module

public import CFSG.Sporadic.J4.QTMask
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.LawfulXor.Basic
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

public section

namespace CFSG.Sporadic.J4.QT

section Elem

variable {G : Type*} [Group G]

@[expose] def eta (u : ℕ → G) (n c : ℕ) : G :=
  (List.range n).foldl (fun acc j => if c.testBit j then acc * u j else acc) 1

theorem eta_zero (u : ℕ → G) (n : ℕ) : eta u n 0 = 1 := by
  unfold eta
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.foldl_append]; simp

theorem eta_succ (u : ℕ → G) (n c : ℕ) :
    eta u (n + 1) c = eta u n c * (if c.testBit n then u n else 1) := by
  unfold eta
  rw [List.range_succ, List.foldl_append]
  by_cases h : c.testBit n <;> simp [h]

structure Elem (u : ℕ → G) (n : ℕ) : Prop where
  sq : ∀ j < n, u j * u j = 1
  comm : ∀ i < n, ∀ j < n, u i * u j = u j * u i

variable {u : ℕ → G} {n : ℕ}

theorem eta_comm_left (h : Elem u n) {m : ℕ} (hm : m ≤ n) {j : ℕ} (hj : j < n) (c : ℕ) :
    u j * eta u m c = eta u m c * u j := by
  induction m with
  | zero => simp [eta]
  | succ m ih =>
    rw [eta_succ]
    have ih' := ih (by omega)
    split_ifs
    · calc u j * (eta u m c * u m) = (u j * eta u m c) * u m := by group
        _ = eta u m c * u j * u m := by rw [ih']
        _ = eta u m c * (u j * u m) := by group
        _ = eta u m c * (u m * u j) := by rw [h.comm j hj m (by omega)]
        _ = eta u m c * u m * u j := by group
    · simp [ih']

theorem eta_xor (h : Elem u n) {m : ℕ} (hm : m ≤ n) (c d : ℕ) :
    eta u m (c ^^^ d) = eta u m c * eta u m d := by
  induction m with
  | zero => simp [eta]
  | succ m ih =>
    have ih' := ih (by omega)
    have hcm : u m * eta u m d = eta u m d * u m := eta_comm_left h (by omega) (by omega) d
    have hsq : u m * u m = 1 := h.sq m (by omega)
    rw [eta_succ, eta_succ, eta_succ, ih']
    cases hc : c.testBit m <;> cases hd : d.testBit m <;> simp [Nat.testBit_xor, hc, hd]
    · exact mul_assoc _ _ _
    · calc eta u m c * eta u m d * u m = eta u m c * (eta u m d * u m) := by group
        _ = eta u m c * (u m * eta u m d) := by rw [hcm]
        _ = eta u m c * u m * eta u m d := by group
    · calc eta u m c * eta u m d = eta u m c * eta u m d * (u m * u m) := by rw [hsq, mul_one]
        _ = eta u m c * (eta u m d * u m) * u m := by group
        _ = eta u m c * (u m * eta u m d) * u m := by rw [hcm]
        _ = eta u m c * u m * (eta u m d * u m) := by group

theorem eta_sq (h : Elem u n) (c : ℕ) : eta u n c * eta u n c = 1 := by
  rw [← eta_xor h le_rfl, Nat.xor_self, eta_zero]

theorem eta_comm (h : Elem u n) (c d : ℕ) : eta u n c * eta u n d = eta u n d * eta u n c := by
  rw [← eta_xor h le_rfl, ← eta_xor h le_rfl, Nat.xor_comm]

theorem eta_two_pow {j : ℕ} (hj : j < n) : eta u n (2 ^ j) = u j := by
  have key : ∀ m, m ≤ n → eta u m (2 ^ j) = if j < m then u j else 1 := by
    intro m
    induction m with
    | zero => intro _; simp [eta]
    | succ m ih =>
      intro hm
      rw [eta_succ, ih (by omega), Nat.testBit_two_pow]
      by_cases h1 : j = m
      · subst h1; simp
      · by_cases h2 : j < m
        · simp [h1, h2, show j < m + 1 by omega]
        · simp [h1, h2, show ¬ j < m + 1 by omega]
  rw [key n le_rfl]
  simp [hj]

@[expose] def Eg (u : ℕ → G) (n : ℕ) : Subgroup G :=
  Subgroup.closure {g | ∃ j < n, g = u j}

theorem eta_mem_Eg (m : ℕ) (hm : m ≤ n) (c : ℕ) : eta u m c ∈ Eg u n := by
  induction m with
  | zero => simp [eta]
  | succ m ih =>
    rw [eta_succ]
    refine Subgroup.mul_mem _ (ih (by omega)) ?_
    split_ifs
    · exact Subgroup.subset_closure ⟨m, by omega, rfl⟩
    · exact Subgroup.one_mem _

theorem mem_Eg_iff (h : Elem u n) {g : G} : g ∈ Eg u n ↔ ∃ c < 2 ^ n, g = eta u n c := by
  constructor
  · intro hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨j, hj, rfl⟩ := hx
      exact ⟨2 ^ j, Nat.pow_lt_pow_right (by norm_num) hj, (eta_two_pow hj).symm⟩
    | one => exact ⟨0, Nat.two_pow_pos n, (eta_zero u n).symm⟩
    | mul x y _ _ hx hy =>
      obtain ⟨c, hc, rfl⟩ := hx
      obtain ⟨d, hd, rfl⟩ := hy
      exact ⟨c ^^^ d, Nat.xor_lt_two_pow hc hd, (eta_xor h le_rfl c d).symm⟩
    | inv x _ hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      refine ⟨c, hc, ?_⟩
      exact inv_eq_of_mul_eq_one_right (eta_sq h c)
  · rintro ⟨c, -, rfl⟩
    exact eta_mem_Eg n le_rfl c

theorem Eg_comm (h : Elem u n) {g g' : G} (hg : g ∈ Eg u n) (hg' : g' ∈ Eg u n) :
    g * g' = g' * g := by
  obtain ⟨c, -, rfl⟩ := (mem_Eg_iff h).1 hg
  obtain ⟨d, -, rfl⟩ := (mem_Eg_iff h).1 hg'
  exact eta_comm h c d

theorem Eg_sq (h : Elem u n) {g : G} (hg : g ∈ Eg u n) : g * g = 1 := by
  obtain ⟨c, -, rfl⟩ := (mem_Eg_iff h).1 hg
  exact eta_sq h c

theorem u_mem_Eg {j : ℕ} (hj : j < n) : u j ∈ Eg u n := Subgroup.subset_closure ⟨j, hj, rfl⟩

theorem card_Eg (h : Elem u n)
    (hinj : ∀ c < 2 ^ n, ∀ d < 2 ^ n, eta u n c = eta u n d → c = d) :
    Nat.card (Eg u n) = 2 ^ n := by
  have : Nat.card (Eg u n) = Nat.card (Fin (2 ^ n)) := by
    symm
    refine Nat.card_congr (Equiv.ofBijective
      (fun c : Fin (2 ^ n) => (⟨eta u n c, eta_mem_Eg n le_rfl c⟩ : Eg u n)) ⟨?_, ?_⟩)
    · intro c d hcd
      exact Fin.ext (hinj c c.2 d d.2 (congrArg Subtype.val hcd))
    · rintro ⟨g, hg⟩
      obtain ⟨c, hc, rfl⟩ := (mem_Eg_iff h).1 hg
      exact ⟨⟨c, hc⟩, rfl⟩
  rw [this, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem rowsXor_succ (r : ℕ → ℕ) (m c : ℕ) :
    rowsXor r (m + 1) c = rowsXor r m c ^^^ (if c.testBit m then r m else 0) := by
  unfold rowsXor
  rw [List.range_succ, List.foldl_append]
  by_cases hb : c.testBit m <;> simp [hb]

theorem rowsXor_zero (r : ℕ → ℕ) (c : ℕ) : rowsXor r 0 c = 0 := rfl

theorem conj_eta (h : Elem u n) (x : G) (r : ℕ → ℕ)
    (hx : ∀ j < n, x * u j * x⁻¹ = eta u n (r j)) {m : ℕ} (hm : m ≤ n) (c : ℕ) :
    x * eta u m c * x⁻¹ = eta u n (rowsXor r m c) := by
  induction m with
  | zero => simp [eta, rowsXor_zero]
  | succ m ih =>
    have ih' := ih (by omega)
    rw [eta_succ, rowsXor_succ, eta_xor h le_rfl]
    have e : x * (eta u m c * (if c.testBit m then u m else 1)) * x⁻¹ =
        (x * eta u m c * x⁻¹) * (x * (if c.testBit m then u m else 1) * x⁻¹) := by group
    rw [e, ih']
    congr 1
    split_ifs
    · exact hx m (by omega)
    · rw [eta_zero]; group

theorem word_conj {ι : Type*} (X : ι → G) (act : ι → ℕ → ℕ) (w : List ι)
    (hX : ∀ ℓ ∈ w, ∀ c, X ℓ * eta u n c * (X ℓ)⁻¹ = eta u n (act ℓ c)) (c : ℕ) :
    (w.map X).prod * eta u n c * ((w.map X).prod)⁻¹ = eta u n (w.foldr act c) := by
  induction w with
  | nil => simp
  | cons ℓ w ih =>
    rw [List.map_cons, List.prod_cons, List.foldr_cons]
    have e : X ℓ * (w.map X).prod * eta u n c * (X ℓ * (w.map X).prod)⁻¹ =
        X ℓ * ((w.map X).prod * eta u n c * ((w.map X).prod)⁻¹) * (X ℓ)⁻¹ := by group
    rw [e, ih (fun ℓ' hℓ' => hX ℓ' (List.mem_cons_of_mem _ hℓ')), hX ℓ (List.mem_cons_self ..)]

end Elem

end CFSG.Sporadic.J4.QT
