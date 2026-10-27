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
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.TotallySplit
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

namespace CFSG.Quasithin.SteinbergCB.I16

open Matrix

abbrev Vec4 : Type := Fin 4 → ZMod 2
abbrev Mat4 : Type := Matrix (Fin 4) (Fin 4) (ZMod 2)

theorem vec4_add_self (v : Vec4) : v + v = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero (v i)

theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · left; rfl
  · right; rfl

theorem mat4_add_self (M : Mat4) : M + M = 0 := by
  ext i j
  exact CharTwo.add_self_eq_zero (M i j)

variable {x : Mat4}

@[expose] def InW (x : Mat4) (v : Vec4) : Prop := (x * x + x + 1) *ᵥ v = 0

theorem InW.add {v w : Vec4} (hv : InW x v) (hw : InW x w) : InW x (v + w) := by
  unfold InW at *
  rw [mulVec_add, hv, hw, add_zero]

theorem InW.smul {v : Vec4} (c : ZMod 2) (hv : InW x v) : InW x (c • v) := by
  unfold InW at *
  rw [mulVec_smul, hv, smul_zero]

theorem InW.mulVec_of_comm {y : Mat4} (hxy : x * y = y * x) {v : Vec4} (hv : InW x v) :
    InW x (y *ᵥ v) := by
  unfold InW at *
  have hxx : x * x * y = y * (x * x) := by
    rw [mul_assoc, hxy, ← mul_assoc, hxy, mul_assoc]
  have h : (x * x + x + 1) * y = y * (x * x + x + 1) := by
    rw [add_mul, add_mul, mul_add, mul_add, hxx, hxy, one_mul, mul_one]
  rw [mulVec_mulVec, h, ← mulVec_mulVec, hv, mulVec_zero]

theorem InW.mulVec_x {v : Vec4} (hv : InW x v) : InW x (x *ᵥ v) :=
  hv.mulVec_of_comm rfl

theorem mulVec_inj_of_cube (hx3 : x ^ 3 = 1) {v w : Vec4} (h : x *ᵥ v = x *ᵥ w) : v = w := by
  have h2 : (x * x) *ᵥ (x *ᵥ v) = (x * x) *ᵥ (x *ᵥ w) := by rw [h]
  rw [mulVec_mulVec, mulVec_mulVec, ← pow_three', hx3, one_mulVec, one_mulVec] at h2
  exact h2

theorem eq_zero_of_fixed_inW {v : Vec4} (hU : x *ᵥ v = v) (hW : InW x v) : v = 0 := by
  unfold InW at hW
  rw [add_mulVec, add_mulVec, ← mulVec_mulVec, hU, hU, one_mulVec, vec4_add_self, zero_add]
    at hW
  exact hW

theorem decomp (v : Vec4) : v = (x * x + x + 1) *ᵥ v + (x * x + x) *ᵥ v := by
  rw [← add_mulVec]
  have : x * x + x + 1 + (x * x + x) = 1 := by
    rw [add_comm, ← add_assoc, mat4_add_self, zero_add]
  rw [this, one_mulVec]

theorem fixed_PU (hx3 : x ^ 3 = 1) (v : Vec4) :
    x *ᵥ ((x * x + x + 1) *ᵥ v) = (x * x + x + 1) *ᵥ v := by
  rw [mulVec_mulVec]
  congr 1
  rw [mul_add, mul_add, mul_one, ← mul_assoc, ← pow_three', hx3]
  abel

theorem inW_PW (hx3 : x ^ 3 = 1) (v : Vec4) : InW x ((x * x + x) *ᵥ v) := by
  unfold InW
  rw [mulVec_mulVec]
  have h : (x * x + x + 1) * (x * x + x) = 0 := by
    have h4 : x * x * (x * x) = x := by rw [← mul_assoc, ← pow_three', hx3, one_mul]
    have h3 : x * x * x = 1 := by rw [← pow_three', hx3]
    have h3' : x * (x * x) = 1 := by rw [← pow_three, hx3]
    rw [add_mul, add_mul, mul_add, mul_add, mul_add, h4, h3, h3', one_mul, one_mul]
    rw [show x + 1 + (1 + x * x) + (x * x + x) = (x + x) + (1 + 1) + (x * x + x * x) by abel]
    simp only [mat4_add_self, add_zero]
  rw [h, zero_mulVec]

theorem indep_W (hx3 : x ^ 3 = 1) {w : Vec4} (hw : InW x w) (hw0 : w ≠ 0) (a b : ZMod 2)
    (h : a • w + b • (x *ᵥ w) = 0) : a = 0 ∧ b = 0 := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl
  · exact ⟨rfl, rfl⟩
  · exfalso
    rw [zero_smul, one_smul, zero_add] at h
    exact hw0 (mulVec_inj_of_cube hx3 (h.trans (mulVec_zero x).symm))
  · exfalso
    rw [zero_smul, one_smul, add_zero] at h
    exact hw0 h
  · exfalso
    rw [one_smul, one_smul] at h
    have hfix : x *ᵥ w = w := by
      have := congrArg (· + w) h
      simp only [zero_add] at this
      rw [add_comm, ← add_assoc, vec4_add_self, zero_add] at this
      exact this
    exact hw0 (eq_zero_of_fixed_inW hfix hw)

theorem fixed_of_add_eq_zero {v w : Vec4} (h : v + w = 0) : v = w := by
  calc v = v + w + w := by rw [add_assoc, vec4_add_self, add_zero]
    _ = w := by rw [h, zero_add]

theorem PU_of_fixed {u : Vec4} (hu : x *ᵥ u = u) : (x * x + x + 1) *ᵥ u = u := by
  rw [add_mulVec, add_mulVec, ← mulVec_mulVec, hu, hu, one_mulVec, vec4_add_self, zero_add]

theorem eq_one_of_mulVec {M : Mat4} (h : ∀ z, M *ᵥ z = z) : M = 1 := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro z
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, one_mulVec, h]

theorem sq_add_one_eq_zero {y : Mat4} (hy : y * y = 1) : (y + 1) * (y + 1) = 0 := by
  rw [add_mul, mul_add, mul_add, hy, mul_one, one_mul, one_mul]
  rw [show 1 + y + (y + 1) = (1 + 1) + (y + y) by abel]
  simp only [mat4_add_self, add_zero]

theorem comm_add_one {y : Mat4} (hxy : x * y = y * x) : x * (y + 1) = (y + 1) * x := by
  rw [mul_add, add_mul, hxy, mul_one, one_mul]

theorem trivial_on_W (hx3 : x ^ 3 = 1) {v₀ : Vec4} (hv₀ : x *ᵥ v₀ = v₀) (hv₀0 : v₀ ≠ 0)
    {y : Mat4} (hy : y * y = 1) (hxy : x * y = y * x) {w : Vec4} (hw : InW x w) :
    y *ᵥ w = w := by
  by_contra hne
  set D : Mat4 := y + 1 with hD
  set d := D *ᵥ w with hd
  have hd0 : d ≠ 0 := by
    intro h0
    apply hne
    apply fixed_of_add_eq_zero
    rw [← h0, hd, hD, add_mulVec, one_mulVec]
  have hxD : x * D = D * x := comm_add_one hxy
  have hDD : D * D = 0 := sq_add_one_eq_zero hy
  have hdW : InW x d := hw.mulVec_of_comm hxD
  have hDd : D *ᵥ d = 0 := by rw [hd, mulVec_mulVec, hDD, zero_mulVec]
  have hDxd : D *ᵥ (x *ᵥ d) = 0 := by
    rw [mulVec_mulVec, ← hxD, ← mulVec_mulVec, hDd, mulVec_zero]
  have hDxw : D *ᵥ (x *ᵥ w) = x *ᵥ d := by rw [mulVec_mulVec, ← hxD, ← mulVec_mulVec]
  let c : Vec4 → Vec4 := fun a => a 0 • w + a 1 • (x *ᵥ w) + a 2 • d + a 3 • (x *ᵥ d)
  have hc_add : ∀ a b, c (a + b) = c a + c b := by
    intro a b
    simp only [c, Pi.add_apply, add_smul]
    abel
  have hc0 : ∀ a, c a = 0 → a = 0 := by
    intro a ha
    have h1 : D *ᵥ c a = a 0 • d + a 1 • (x *ᵥ d) := by
      simp only [c, mulVec_add, mulVec_smul, hDxw, hDd, hDxd, smul_zero, add_zero]
      rfl
    rw [ha, mulVec_zero] at h1
    obtain ⟨h0, h1'⟩ := indep_W hx3 hdW hd0 (a 0) (a 1) h1.symm
    have h2 : a 2 • d + a 3 • (x *ᵥ d) = 0 := by
      have h := ha
      simp only [c, h0, h1', zero_smul, zero_add] at h
      exact h
    obtain ⟨h2', h3'⟩ := indep_W hx3 hdW hd0 (a 2) (a 3) h2
    funext i
    fin_cases i <;> simp [h0, h1', h2', h3']
  have hinj : Function.Injective c := by
    intro a b hab
    apply fixed_of_add_eq_zero
    apply hc0
    rw [hc_add, hab, vec4_add_self]
  obtain ⟨a, ha⟩ := Finite.injective_iff_surjective.1 hinj v₀
  have hW : InW x (c a) :=
    (((hw.smul _).add (hw.mulVec_x.smul _)).add (hdW.smul _)).add (hdW.mulVec_x.smul _)
  rw [ha] at hW
  exact hv₀0 (eq_zero_of_fixed_inW hv₀ hW)

theorem fixed_eq_zero_of_fourGroup (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) {y₁ y₂ : Mat4}
    (hy₁ : y₁ * y₁ = 1) (hy₂ : y₂ * y₂ = 1) (hxy₁ : x * y₁ = y₁ * x) (hxy₂ : x * y₂ = y₂ * x)
    (hyy : y₁ * y₂ = y₂ * y₁) (h₁ : y₁ ≠ 1) (h₂ : y₂ ≠ 1) (h₁₂ : y₁ ≠ y₂) {v : Vec4}
    (hv : x *ᵥ v = v) : v = 0 := by
  by_contra hv0
  obtain ⟨w₀, hw₀, hw₀0⟩ : ∃ w₀, InW x w₀ ∧ w₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hx1
    apply eq_one_of_mulVec
    intro z
    have h := decomp (x := x) z
    rw [hcon _ (inW_PW hx3 z), add_zero] at h
    rw [h, fixed_PU hx3]
  set N₁ : Mat4 := y₁ + 1 with hN₁
  set N₂ : Mat4 := y₂ + 1 with hN₂
  have hN₁W : ∀ w, InW x w → N₁ *ᵥ w = 0 := fun w hw => by
    rw [hN₁, add_mulVec, one_mulVec, trivial_on_W hx3 hv hv0 hy₁ hxy₁ hw, vec4_add_self]
  have hN₂W : ∀ w, InW x w → N₂ *ᵥ w = 0 := fun w hw => by
    rw [hN₂, add_mulVec, one_mulVec, trivial_on_W hx3 hv hv0 hy₂ hxy₂ hw, vec4_add_self]
  have hNdet : ∀ N : Mat4, (∀ w, InW x w → N *ᵥ w = 0) →
      ∀ z, N *ᵥ z = N *ᵥ ((x * x + x + 1) *ᵥ z) := by
    intro N hN z
    conv_lhs => rw [decomp (x := x) z]
    rw [mulVec_add, hN _ (inW_PW hx3 z), add_zero]
  have hy_of_N : ∀ (y : Mat4), (∀ z, (y + 1) *ᵥ z = 0) → y = 1 := fun y hN =>
    eq_one_of_mulVec fun z => fixed_of_add_eq_zero (by
      have := hN z
      rwa [add_mulVec, one_mulVec] at this)
  obtain ⟨u, huU, hNu⟩ : ∃ u, x *ᵥ u = u ∧ N₁ *ᵥ u ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact h₁ (hy_of_N y₁ fun z => by rw [hNdet N₁ hN₁W z]; exact hcon _ (fixed_PU hx3 z))
  have hu0 : u ≠ 0 := fun h0 => hNu (by rw [h0, mulVec_zero])
  have hxN₁ : x * N₁ = N₁ * x := comm_add_one hxy₁
  have hxN₂ : x * N₂ = N₂ * x := comm_add_one hxy₂
  have hN₁N₁ : N₁ * N₁ = 0 := sq_add_one_eq_zero hy₁
  have hN₂N₂ : N₂ * N₂ = 0 := sq_add_one_eq_zero hy₂
  have hN₁N₂ : N₁ * N₂ = N₂ * N₁ := by
    simp only [hN₁, hN₂, add_mul, mul_add, one_mul, mul_one, hyy]
    abel
  set a := N₁ *ᵥ u with ha
  have haU : x *ᵥ a = a := by rw [ha, mulVec_mulVec, hxN₁, ← mulVec_mulVec, huU]
  have hNa : N₁ *ᵥ a = 0 := by rw [ha, mulVec_mulVec, hN₁N₁, zero_mulVec]
  have hfixU : ∀ M : Mat4, x * M = M * x → ∀ z, x *ᵥ z = z → x *ᵥ (M *ᵥ z) = M *ᵥ z :=
    fun M hM z hz => by rw [mulVec_mulVec, hM, ← mulVec_mulVec, hz]
  have hspan : ∀ z, x *ᵥ z = z → ∃ b₀ b₁ : ZMod 2, z = b₀ • a + b₁ • u := by
    intro z hz
    let c : Vec4 → Vec4 := fun b => b 0 • a + b 1 • u + b 2 • w₀ + b 3 • (x *ᵥ w₀)
    have hc_add : ∀ b b', c (b + b') = c b + c b' := by
      intro b b'
      simp only [c, Pi.add_apply, add_smul]
      abel
    have hPc : ∀ b, (x * x + x + 1) *ᵥ c b = b 0 • a + b 1 • u := by
      intro b
      have hw1 : (x * x + x + 1) *ᵥ w₀ = 0 := hw₀
      have hw2 : (x * x + x + 1) *ᵥ (x *ᵥ w₀) = 0 := hw₀.mulVec_x
      simp only [c, mulVec_add, mulVec_smul, PU_of_fixed haU, PU_of_fixed huU, hw1, hw2,
        smul_zero, add_zero]
    have hc0 : ∀ b, c b = 0 → b = 0 := by
      intro b hb
      have h1 := hPc b
      rw [hb, mulVec_zero] at h1
      have h2 : b 1 • a = 0 := by
        have := congrArg (N₁ *ᵥ ·) h1
        simp only [mulVec_zero, mulVec_add, mulVec_smul, hNa, ← ha, smul_zero, zero_add]
          at this
        exact this.symm
      have ha0 : a ≠ 0 := hNu
      have hb1 : b 1 = 0 := (smul_eq_zero.1 h2).resolve_right ha0
      have hb0 : b 0 = 0 := by
        rw [hb1, zero_smul, add_zero] at h1
        exact (smul_eq_zero.1 h1.symm).resolve_right ha0
      have h3 : b 2 • w₀ + b 3 • (x *ᵥ w₀) = 0 := by
        have h := hb
        simp only [c, hb0, hb1, zero_smul, zero_add] at h
        exact h
      obtain ⟨hb2, hb3⟩ := indep_W hx3 hw₀ hw₀0 (b 2) (b 3) h3
      funext i
      fin_cases i <;> simp [hb0, hb1, hb2, hb3]
    have hinj : Function.Injective c := by
      intro b b' hbb
      apply fixed_of_add_eq_zero
      apply hc0
      rw [hc_add, hbb, vec4_add_self]
    obtain ⟨b, hb⟩ := Finite.injective_iff_surjective.1 hinj z
    refine ⟨b 0, b 1, ?_⟩
    rw [← hPc b, hb, PU_of_fixed hz]
  obtain ⟨c₀, c₁, hc⟩ := hspan _ (hfixU N₂ hxN₂ u huU)
  have hN₂a : N₂ *ᵥ a = c₁ • a := by
    rw [ha, mulVec_mulVec, ← hN₁N₂, ← mulVec_mulVec, hc, mulVec_add, mulVec_smul, mulVec_smul,
      hNa, ← ha, smul_zero, zero_add]
  have hc₁ : c₁ = 0 := by
    have h := congrArg (N₂ *ᵥ ·) hc
    simp only [mulVec_mulVec, hN₂N₂, zero_mulVec, mulVec_add, mulVec_smul, hN₂a] at h
    rw [hc] at h
    rcases zmod2_cases c₀ with rfl | rfl <;> rcases zmod2_cases c₁ with rfl | rfl
    · rfl
    · exfalso
      simp only [zero_smul, one_smul, zero_add] at h
      exact hu0 h.symm
    · rfl
    · exfalso
      simp only [one_smul] at h
      rw [← add_assoc, vec4_add_self, zero_add] at h
      exact hu0 h.symm
  rw [hc₁, zero_smul, add_zero] at hc
  rw [hc₁, zero_smul] at hN₂a
  have hc₀ : c₀ = 1 := by
    rcases zmod2_cases c₀ with h0 | h0
    · exfalso
      rw [h0, zero_smul] at hc
      apply h₂
      apply hy_of_N y₂
      intro z
      rw [hNdet N₂ hN₂W z]
      obtain ⟨b₀, b₁, hb⟩ := hspan _ (fixed_PU hx3 z)
      rw [hb, mulVec_add, mulVec_smul, mulVec_smul, hN₂a, hc, smul_zero, smul_zero, add_zero]
    · exact h0
  rw [hc₀, one_smul] at hc
  apply h₁₂
  have hN : N₁ = N₂ := by
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro z
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hNdet N₁ hN₁W z, hNdet N₂ hN₂W z]
    obtain ⟨b₀, b₁, hb⟩ := hspan _ (fixed_PU hx3 z)
    rw [hb, mulVec_add, mulVec_add, mulVec_smul, mulVec_smul, mulVec_smul, mulVec_smul, hNa,
      ← ha, hN₂a, hc]
  have h := congrArg (· + 1) hN
  simp only [hN₁, hN₂, add_assoc, mat4_add_self, add_zero] at h
  exact h

end CFSG.Quasithin.SteinbergCB.I16
