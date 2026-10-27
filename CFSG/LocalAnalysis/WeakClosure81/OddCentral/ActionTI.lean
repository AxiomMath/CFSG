module
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow
public section
namespace CFSG.LocalAnalysis.WeakClosure81.OddCentral

variable {Γ A : Type*} [Group Γ] [AddCommGroup A] [DistribMulAction Γ A]

@[expose] def TIPair (u u' : Γ) : Prop :=
  ∀ a b : A, u • a - a = u' • b - b → u • a - a = 0

omit [Group Γ] [DistribMulAction Γ A] in
theorem nsmul_odd_eq (h2 : ∀ a : A, a + a = 0) {n : ℕ} (hn : Odd n) (c : A) : n • c = c := by
  obtain ⟨m, rfl⟩ := hn
  rw [add_nsmul, mul_nsmul, two_nsmul, h2, nsmul_zero, zero_add, one_nsmul]

theorem pow_smul_of_fix {x : Γ} {a : A} (h : x • (x • a - a) = x • a - a) (k : ℕ) :
    x ^ k • a = a + k • (x • a - a) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_smul, ih, smul_add, smul_comm x k, h, succ_nsmul]
    abel

theorem eq_zero_of_fix (h2 : ∀ a : A, a + a = 0) {x : Γ} (hx : Odd (orderOf x)) {a : A}
    (h : x • (x • a - a) = x • a - a) : x • a - a = 0 := by
  have := pow_smul_of_fix h (orderOf x)
  rw [pow_orderOf_eq_one, one_smul, nsmul_odd_eq h2 hx] at this
  have h' : a + (x • a - a) = a + 0 := by rw [← this, add_zero]
  exact add_left_cancel h'

theorem smul_eq_of_sq {x : Γ} (hx : Odd (orderOf x)) {b : A} (h : x • x • b = b) : x • b = b := by
  obtain ⟨m, hm⟩ := hx
  have hxx : x = (x ^ 2) ^ (m + 1) := by
    rw [← pow_mul, show 2 * (m + 1) = orderOf x + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  have h2 : (x ^ 2) • b = b := by rw [sq, mul_smul, h]
  have : ∀ k : ℕ, (x ^ 2) ^ k • b = b := fun k => by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', mul_smul, ih, h2]
  rw [hxx]; exact this _

theorem fix_of_tiPair {u u' : Γ} (hc : u * u' = u' * u) (hTI : TIPair (A := A) u u') (a : A) :
    u • (u' • a - a) = u' • a - a := by
  have key : u • (u' • a - a) - (u' • a - a) = u' • (u • a - a) - (u • a - a) := by
    rw [smul_sub, smul_sub, smul_smul, smul_smul, hc]; abel
  have := hTI (u' • a - a) (u • a - a) key
  exact sub_eq_zero.mp this

theorem fix_of_square {w w' x : Γ} (hwx : w * x * w⁻¹ = x⁻¹) (hw'w : w * w' = w' * w)
    (hw'x : w' * x = x * w') (hx : Odd (orderOf x)) (hTI1 : TIPair (A := A) w w')
    (hTI2 : TIPair (A := A) (x⁻¹ * w * x) w') (a : A) :
    x • (w' • a - a) = w' • a - a := by
  set b := w' • a - a
  have h1 : w • b = b := fix_of_tiPair hw'w hTI1 a
  have hc2 : (x⁻¹ * w * x) * w' = w' * (x⁻¹ * w * x) := by
    have hcx : Commute x w' := hw'x.symm
    have hcw : Commute w w' := hw'w
    exact ((hcx.inv_left.mul_left hcw).mul_left hcx).eq
  have h2 : (x⁻¹ * w * x) • b = b := fix_of_tiPair hc2 hTI2 a
  have hconj : x⁻¹ * w * x = x⁻¹ * x⁻¹ * w := by
    have : w * x = x⁻¹ * w := by
      rw [← hwx, inv_mul_cancel_right]
    rw [mul_assoc, this, mul_assoc]
  rw [hconj, mul_smul, mul_smul, h1] at h2
  apply smul_eq_of_sq hx
  calc x • x • b = x • x • (x⁻¹ • x⁻¹ • b) := by rw [h2]
    _ = b := by rw [smul_inv_smul, smul_inv_smul]

theorem fix_of_factA (h2 : ∀ a : A, a + a = 0) {x y w₂ : Γ} (hxw : x * w₂ = w₂ * x)
    (hxy : x * y = y * x) (hyw : w₂ * y * w₂⁻¹ = y⁻¹) (hxo : Odd (orderOf x))
    (hyo : Odd (orderOf y)) (hfix : ∀ a : A, x • (w₂ • a - a) = w₂ • a - a) (a : A) :
    y • (x • a - a) = x • a - a := by
  have hw : ∀ e : A, w₂ • (x • e - e) = x • e - e := by
    intro e
    have hc : w₂ • (x • e - e) - (x • e - e) = x • (w₂ • e - e) - (w₂ • e - e) := by
      rw [smul_sub, smul_sub, smul_smul, smul_smul, hxw]; abel
    have hfx : x • (x • (w₂ • e - e) - (w₂ • e - e)) = x • (w₂ • e - e) - (w₂ • e - e) := by
      rw [← hc]; exact hfix (x • e - e)
    exact sub_eq_zero.mp (hc.trans (eq_zero_of_fix h2 hxo hfx))
  set b := x • a - a
  have hyb : y • b = x • (y • a) - y • a := by
    rw [smul_sub, smul_smul, ← hxy, ← smul_smul]
  have h1 : w₂ • b = b := hw a
  have h3 : w₂ • y • b = y • b := by rw [hyb]; exact hw (y • a)
  have hinv : y⁻¹ • b = y • b := by
    rw [← hyw, mul_smul, mul_smul]
    have : w₂⁻¹ • b = b := by
      conv_lhs => rw [← h1]
      rw [inv_smul_smul]
    rw [this, h3]
  apply smul_eq_of_sq hyo
  have := congrArg (y • ·) hinv
  simp only [smul_inv_smul] at this
  exact this.symm

theorem fix_comm_of_fix {x' y' w' : Γ} (hζw : (x' * y' * x'⁻¹ * y'⁻¹) * w' = w' * (x' * y' * x'⁻¹ * y'⁻¹))
    (hx : ∀ a : A, x' • (w' • a - a) = w' • a - a)
    (hy : ∀ a : A, y' • (w' • a - a) = w' • a - a) (a : A) :
    w' • ((x' * y' * x'⁻¹ * y'⁻¹) • a - a) = (x' * y' * x'⁻¹ * y'⁻¹) • a - a := by
  set ζ := x' * y' * x'⁻¹ * y'⁻¹
  have hinvx : ∀ e : A, x'⁻¹ • (w' • e - e) = w' • e - e := fun e => by
    conv_lhs => rw [← hx e]
    rw [inv_smul_smul]
  have hinvy : ∀ e : A, y'⁻¹ • (w' • e - e) = w' • e - e := fun e => by
    conv_lhs => rw [← hy e]
    rw [inv_smul_smul]
  have hζ : ζ • (w' • a - a) = w' • a - a := by
    simp only [ζ, mul_smul, hinvy, hinvx, hy, hx]
  have hc : w' • (ζ • a - a) - (ζ • a - a) = ζ • (w' • a - a) - (w' • a - a) := by
    rw [smul_sub, smul_sub, smul_smul, smul_smul, hζw]; abel
  rw [hζ, sub_self] at hc
  exact sub_eq_zero.mp hc

theorem comm_acts_trivially (h2 : ∀ a : A, a + a = 0) {x y w : Γ}
    (hζx : (x * y * x⁻¹ * y⁻¹) * x = x * (x * y * x⁻¹ * y⁻¹))
    (hζy : (x * y * x⁻¹ * y⁻¹) * y = y * (x * y * x⁻¹ * y⁻¹))
    (hwx : w * x * w⁻¹ = x⁻¹) (hwy : w * y * w⁻¹ = y⁻¹) (hxo : Odd (orderOf x))
    (hyo : Odd (orderOf y)) (hζo : Odd (orderOf (x * y * x⁻¹ * y⁻¹)))
    (hw : ∀ a : A, w • ((x * y * x⁻¹ * y⁻¹) • a - a) = (x * y * x⁻¹ * y⁻¹) • a - a) (a : A) :
    (x * y * x⁻¹ * y⁻¹) • a = a := by
  set ζ := x * y * x⁻¹ * y⁻¹
  have key : ∀ v : Γ, ζ * v = v * ζ → w * v * w⁻¹ = v⁻¹ → Odd (orderOf v) →
      ∀ e : A, v • (ζ • e - e) = ζ • e - e := by
    intro v hv hwv hvo e
    set b := ζ • e - e
    have hvb : v • b = ζ • (v • e) - v • e := by
      rw [smul_sub, smul_smul, ← hv, ← smul_smul]
    have hwb : w • b = b := hw e
    have hwvb : w • v • b = v • b := by rw [hvb]; exact hw (v • e)
    have hinv : v⁻¹ • b = v • b := by
      rw [← hwv, mul_smul, mul_smul]
      have : w⁻¹ • b = b := by
        conv_lhs => rw [← hwb]
        rw [inv_smul_smul]
      rw [this, hwvb]
    apply smul_eq_of_sq hvo
    have := congrArg (v • ·) hinv
    simp only [smul_inv_smul] at this
    exact this.symm
  have hxb := key x hζx hwx hxo
  have hyb := key y hζy hwy hyo
  have hxib : ∀ e : A, x⁻¹ • (ζ • e - e) = ζ • e - e := fun e => by
    conv_lhs => rw [← hxb e]
    rw [inv_smul_smul]
  have hyib : ∀ e : A, y⁻¹ • (ζ • e - e) = ζ • e - e := fun e => by
    conv_lhs => rw [← hyb e]
    rw [inv_smul_smul]
  have hfix : ζ • (ζ • a - a) = ζ • a - a := by
    show (x * y * x⁻¹ * y⁻¹) • (ζ • a - a) = ζ • a - a
    simp only [mul_smul, hyib, hxib, hyb, hxb]
  exact sub_eq_zero.mp (eq_zero_of_fix h2 hζo hfix)

theorem fix_or_fix_of_minimal {Q : Set Γ} (hQ : ∀ p ∈ Q, ∀ q ∈ Q, p * q = q * p)
    {U : AddSubgroup A} (hUQ : ∀ q ∈ Q, ∀ u ∈ U, q • u ∈ U)
    (hmin : ∀ U' : AddSubgroup A, U' ≤ U → (∀ q ∈ Q, ∀ u ∈ U', q • u ∈ U') → U' = ⊥ ∨ U' = U)
    {C₁ C₂ : Set Γ} (hC₁ : C₁ ⊆ Q) (hfact : ∀ x ∈ C₁, ∀ y ∈ C₂, ∀ a : A, y • (x • a - a) = x • a - a) :
    (∀ x ∈ C₁, ∀ u ∈ U, x • u = u) ∨ (∀ y ∈ C₂, ∀ u ∈ U, y • u = u) := by
  by_cases h : ∀ x ∈ C₁, ∀ u ∈ U, x • u = u
  · exact Or.inl h
  right
  push_neg at h
  obtain ⟨x₀, hx₀, u₀, hu₀, hne⟩ := h
  set U' : AddSubgroup A := AddSubgroup.closure {e | ∃ x ∈ C₁, ∃ u ∈ U, e = x • u - u}
  have hU'U : U' ≤ U := by
    rw [AddSubgroup.closure_le]
    rintro _ ⟨x, hx, u, hu, rfl⟩
    exact U.sub_mem (hUQ x (hC₁ hx) u hu) hu
  have hU'Q : ∀ q ∈ Q, ∀ u ∈ U', q • u ∈ U' := by
    intro q hq u hu
    induction hu using AddSubgroup.closure_induction with
    | mem e he =>
      obtain ⟨x, hx, u, hu, rfl⟩ := he
      apply AddSubgroup.subset_closure
      refine ⟨x, hx, q • u, hUQ q hq u hu, ?_⟩
      rw [smul_sub, smul_smul, smul_smul, hQ q hq x (hC₁ hx)]
    | zero => rw [smul_zero]; exact U'.zero_mem
    | add e f _ _ he hf => rw [smul_add]; exact U'.add_mem he hf
    | neg e _ he => rw [smul_neg]; exact U'.neg_mem he
  have hne' : U' ≠ ⊥ := by
    intro hbot
    have hmem : x₀ • u₀ - u₀ ∈ U' := AddSubgroup.subset_closure ⟨x₀, hx₀, u₀, hu₀, rfl⟩
    rw [hbot, AddSubgroup.mem_bot, sub_eq_zero] at hmem
    exact hne hmem
  have hEq : U' = U := (hmin U' hU'U hU'Q).resolve_left hne'
  intro y hy u hu
  rw [← hEq] at hu
  induction hu using AddSubgroup.closure_induction with
  | mem e he =>
    obtain ⟨x, hx, u, -, rfl⟩ := he
    exact hfact x hx y hy u
  | zero => exact smul_zero y
  | add e f _ _ he hf => rw [smul_add, he, hf]
  | neg e _ he => rw [smul_neg, he]

end CFSG.LocalAnalysis.WeakClosure81.OddCentral
