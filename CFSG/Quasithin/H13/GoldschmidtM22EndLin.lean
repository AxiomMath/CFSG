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
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
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

namespace CFSG.Quasithin.H13.GM22

open Module

theorem zmod2_add_self (c : ZMod 2) : c + c = 0 := by revert c; decide

@[expose] noncomputable def tmap {A : Type} [AddCommGroup A] [Module (ZMod 2) A]
    (χ : A →ₗ[ZMod 2] ZMod 2) (u : A) : A →ₗ[ZMod 2] A :=
  LinearMap.id + (LinearMap.toSpanSingleton (ZMod 2) A u).comp χ

theorem tmap_apply {A : Type} [AddCommGroup A] [Module (ZMod 2) A]
    (χ : A →ₗ[ZMod 2] ZMod 2) (u : A) (y : A) : tmap χ u y = y + χ y • u := rfl

@[expose] noncomputable def tvec {A : Type} [AddCommGroup A] [Module (ZMod 2) A]
    (χ : A →ₗ[ZMod 2] ZMod 2) (u : A) (hχu : χ u = 0) : A ≃ₗ[ZMod 2] A :=
  LinearEquiv.ofInvolutive (tmap χ u) (by
      intro x
      rw [tmap_apply, tmap_apply, map_add, map_smul, hχu, smul_zero, add_zero, add_assoc,
        ← add_smul, zmod2_add_self, zero_smul, add_zero])

theorem tvec_apply {A : Type} [AddCommGroup A] [Module (ZMod 2) A]
    (χ : A →ₗ[ZMod 2] ZMod 2) (u : A) (hχu : χ u = 0) (x : A) :
    tvec χ u hχu x = x + χ x • u := rfl

theorem exists_tvec {A : Type} [AddCommGroup A] [Module (ZMod 2) A] [Module.Finite (ZMod 2) A]
    (hn : 3 ≤ finrank (ZMod 2) A) (w : A) (φ : A →ₗ[ZMod 2] ZMod 2) (hφ : φ ≠ 0) :
    ∃ g : A ≃ₗ[ZMod 2] A, g w = w ∧ ∃ x, φ (g x) ≠ φ x := by
  classical
  obtain ⟨u, hu⟩ : ∃ u, φ u ≠ 0 := by
    by_contra h
    push Not at h
    exact hφ (LinearMap.ext h)
  have hlt : Submodule.span (ZMod 2) {u, w} < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => ?_
    have h1 : finrank (ZMod 2) (Submodule.span (ZMod 2) {u, w}) ≤ 2 := by
      have := finrank_span_finset_le_card (R := ZMod 2) ({u, w} : Finset A)
      rw [Finset.coe_insert, Finset.coe_singleton] at this
      exact this.trans ((Finset.card_insert_le _ _).trans (by simp))
    rw [htop, finrank_top] at h1
    omega
  obtain ⟨χ, hχ0, hχle⟩ := Submodule.exists_le_ker_of_lt_top _ hlt
  have hχu : χ u = 0 := hχle (Submodule.subset_span (by simp))
  have hχw : χ w = 0 := hχle (Submodule.subset_span (by simp))
  obtain ⟨x, hx⟩ : ∃ x, χ x ≠ 0 := by
    by_contra h
    push Not at h
    exact hχ0 (LinearMap.ext h)
  refine ⟨tvec χ u hχu, ?_, x, ?_⟩
  · rw [tvec_apply, hχw, zero_smul, add_zero]
  · rw [tvec_apply, map_add, map_smul, smul_eq_mul]
    have h1 : φ u = 1 := by
      revert hu; generalize φ u = c; revert c; decide
    have h2 : χ x = 1 := by
      revert hx; generalize χ x = c; revert c; decide
    rw [h1, h2]
    generalize φ x = c
    revert c; decide

section Transfer

variable {V : Type} [CommGroup V]

@[expose, instance_reducible] noncomputable def zmodInst (hV : ∀ v : V, v ^ 2 = 1) :
    Module (ZMod 2) (Additive V) :=
  AddCommGroup.zmodModule (n := 2) fun x => by
    apply Additive.toMul.injective
    simpa using hV (Additive.toMul x)

variable [Module (ZMod 2) (Additive V)]

@[expose] noncomputable def toLin (f : MulAut V) : Additive V ≃ₗ[ZMod 2] Additive V :=
  (MulEquiv.toAdditive f).toLinearEquiv (fun c x => ZMod.map_smul (MulEquiv.toAdditive f) c x)

theorem toLin_apply (f : MulAut V) (x : Additive V) :
    toLin f x = Additive.ofMul (f (Additive.toMul x)) := rfl

@[expose] noncomputable def ofLin (g : Additive V ≃ₗ[ZMod 2] Additive V) : MulAut V :=
  MulEquiv.toAdditive.symm g.toAddEquiv

theorem ofLin_apply (g : Additive V ≃ₗ[ZMod 2] Additive V) (v : V) :
    ofLin g v = Additive.toMul (g (Additive.ofMul v)) := rfl

@[expose] noncomputable def mulAutEquivLin : MulAut V ≃ (Additive V ≃ₗ[ZMod 2] Additive V) where
  toFun := toLin
  invFun := ofLin
  left_inv _ := MulEquiv.ext fun _ => rfl
  right_inv _ := LinearEquiv.ext fun _ => rfl

omit [Module (ZMod 2) (Additive V)] in
theorem card_mulAut [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {n : ℕ} (hcard : Nat.card V = 2 ^ n) :
    Nat.card (MulAut V) = Nat.card (Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) := by
  let _ := zmodInst hV
  have hfin : finrank (ZMod 2) (Additive V) = n := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    have h2 : Nat.card (Additive V) = 2 ^ n := hcard
    rw [h2, Nat.card_zmod] at h
    exact (Nat.pow_right_injective (le_refl 2) h).symm
  let b : Additive V ≃ₗ[ZMod 2] (Fin n → ZMod 2) :=
    LinearEquiv.ofFinrankEq _ _ (by simp [hfin])
  let e1 : (Additive V ≃ₗ[ZMod 2] Additive V) ≃ ((Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2)) :=
    { toFun := fun g => b.symm.trans (g.trans b)
      invFun := fun h => b.trans (h.trans b.symm)
      left_inv := fun g => LinearEquiv.ext fun x => by simp
      right_inv := fun h => LinearEquiv.ext fun x => by simp }
  let e2 : Matrix.GeneralLinearGroup (Fin n) (ZMod 2) ≃* ((Fin n → ZMod 2) ≃ₗ[ZMod 2]
      (Fin n → ZMod 2)) :=
    Matrix.GeneralLinearGroup.toLin.trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin n → ZMod 2))
  exact Nat.card_congr (mulAutEquivLin.trans (e1.trans e2.toEquiv.symm))

omit [Module (ZMod 2) (Additive V)] in
theorem exists_not_comm [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {n : ℕ} (hn : 3 ≤ n)
    (hcard : Nat.card V = 2 ^ n) {a : MulAut V} {w : V} (hw : w ≠ 1)
    (hform : ∀ x, a x = x ∨ a x = x * w) (ha1 : a ≠ 1) :
    ∃ g : MulAut V, g w = w ∧ g * a ≠ a * g := by
  classical
  let _ := zmodInst hV
  have hfin : finrank (ZMod 2) (Additive V) = n := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    have h2 : Nat.card (Additive V) = 2 ^ n := hcard
    rw [h2, Nat.card_zmod] at h
    exact (Nat.pow_right_injective (le_refl 2) h).symm
  set w' : Additive V := Additive.ofMul w with hw'
  have hw'0 : w' ≠ 0 := fun h => hw (by simpa [hw'] using congrArg Additive.toMul h)
  set α := toLin a with hα
  let φ0 : Additive V → ZMod 2 := fun x => if α x = x then 0 else 1
  have hαx : ∀ x, α x = x + φ0 x • w' := by
    intro x
    by_cases h : α x = x
    · simp [φ0, h]
    · have h' : a (Additive.toMul x) = Additive.toMul x * w := by
        rcases hform (Additive.toMul x) with h1 | h1
        · exact absurd (by simpa [hα, toLin_apply] using congrArg Additive.ofMul h1) h
        · exact h1
      simp only [φ0, h, ↓reduceIte, one_smul]
      simp only [hα, toLin_apply, h', ofMul_mul]
      rfl
  have hφadd : ∀ x y, φ0 (x + y) = φ0 x + φ0 y := by
    intro x y
    have h1 := hαx (x + y)
    have h2 : α (x + y) = α x + α y := map_add α x y
    rw [h2, hαx x, hαx y] at h1
    have h3 : (φ0 (x + y)) • w' = (φ0 x + φ0 y) • w' := by
      rw [add_smul]
      have : x + φ0 x • w' + (y + φ0 y • w') = (x + y) + (φ0 x • w' + φ0 y • w') := by abel
      rw [this] at h1
      exact (add_left_cancel h1).symm
    exact smul_left_injective (ZMod 2) hw'0 h3
  have hφsmul : ∀ (c : ZMod 2) x, φ0 (c • x) = c • φ0 x := by
    intro c x
    have : c = 0 ∨ c = 1 := by revert c; decide
    rcases this with rfl | rfl
    · simp [φ0]
    · simp
  let φ : Additive V →ₗ[ZMod 2] ZMod 2 :=
    { toFun := φ0, map_add' := hφadd, map_smul' := fun c x => by simpa using hφsmul c x }
  have hφ : φ ≠ 0 := by
    intro h0
    apply ha1
    refine MulEquiv.ext fun v => ?_
    have := hαx (Additive.ofMul v)
    have h1 : φ0 (Additive.ofMul v) = 0 := congrFun (congrArg DFunLike.coe h0) (Additive.ofMul v)
    rw [h1, zero_smul, add_zero] at this
    simpa [hα, toLin_apply] using congrArg Additive.toMul this
  obtain ⟨g', hg'w, x, hx⟩ := exists_tvec (A := Additive V) (by omega) w' φ hφ
  refine ⟨ofLin g', hg'w, fun hcomm => hx ?_⟩
  have h1 : ofLin g' (a (Additive.toMul x)) = a (ofLin g' (Additive.toMul x)) :=
    congrArg (fun f : MulAut V => f (Additive.toMul x)) hcomm
  have h2 : g' (α x) = α (g' x) := by
    have := congrArg Additive.ofMul h1
    simpa [hα, toLin_apply, ofLin_apply] using this
  rw [hαx x, map_add, map_smul, hg'w, hαx (g' x)] at h2
  have h3 : φ0 x • w' = φ0 (g' x) • w' := add_left_cancel h2
  exact (smul_left_injective (ZMod 2) hw'0 h3).symm


omit [Module (ZMod 2) (Additive V)] in
theorem exists_mem_not_comm [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {n : ℕ} (hn : 3 ≤ n)
    (hcard : Nat.card V = 2 ^ n) {X : Subgroup (MulAut V)}
    (hX : Nonempty (X ≃* Matrix.GeneralLinearGroup (Fin n) (ZMod 2))) {a : MulAut V} {w : V}
    (hw : w ≠ 1) (hform : ∀ x, a x = x ∨ a x = x * w) (ha1 : a ≠ 1) :
    ∃ g ∈ X, g w = w ∧ g * a ≠ a * g := by
  obtain ⟨e⟩ := hX
  have hXtop : X = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_congr e.toEquiv, card_mulAut hV hcard]
  obtain ⟨g, hg, hga⟩ := exists_not_comm hV hn hcard hw hform ha1
  exact ⟨g, hXtop ▸ Subgroup.mem_top g, hg, hga⟩

end Transfer

end CFSG.Quasithin.H13.GM22
