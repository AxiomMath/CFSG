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
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
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

namespace CFSG.Sporadic.Recognition.JankoWong

structure Heis4Data {M : Type*} [Group M] (s f₁ f₂ f₃ f₄ : M) : Prop where
  card_eq : Nat.card M = 243
  s_cube : s ^ 3 = 1
  s_ne_one : s ≠ 1
  s_central : ∀ x : M, x * s = s * x
  cube : ∀ x : M, x ^ 3 = 1
  comm_mem : ∀ x y : M, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.zpowers s
  indep : ∀ p₁ p₂ p₃ p₄ : ℤ, f₁ ^ p₁ * f₂ ^ p₂ * f₃ ^ p₃ * f₄ ^ p₄ ∈ Subgroup.zpowers s →
    3 ∣ p₁ ∧ 3 ∣ p₂ ∧ 3 ∣ p₃ ∧ 3 ∣ p₄

theorem exists_mulEquiv_of_card_eq_81 {G : Type*} [CommGroup G] (hcard : Nat.card G = 81)
    (hcube : ∀ x : G, x ^ 3 = 1) (b : Fin 4 → G)
    (hind : ∀ p : Fin 4 → ℤ, ∏ i, b i ^ p i = 1 → ∀ i, (3 : ℤ) ∣ p i) :
    ∃ e : G ≃* Multiplicative (Fin 4 → ZMod 3),
      ∀ i, e (b i) = Multiplicative.ofAdd (Pi.single i 1) := by
  have : Finite G := Nat.finite_of_card_ne_zero (by omega)
  let _ : Module (ZMod 3) (Additive G) :=
    AddCommGroup.zmodModule fun x => Additive.toMul.injective (by simp [toMul_nsmul, hcube])
  have hli : LinearIndependent (ZMod 3) (fun i => Additive.ofMul (b i)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h1 : ∑ i, (g i).val • Additive.ofMul (b i) = 0 := by
      simpa only [← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val] using hg
    have h2 : ∏ i, b i ^ ((g i).val : ℤ) = 1 := by
      have h3 := congrArg Additive.toMul h1
      simp only [zpow_natCast]
      simpa only [toMul_sum, toMul_nsmul, toMul_ofMul, toMul_zero] using h3
    have h4 := hind (fun i => ((g i).val : ℤ)) h2 i
    have h5 : ((g i).val : ZMod 3) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      exact_mod_cast h4
    simpa using h5
  have hcard' : Nat.card (Additive G) = 81 := by
    rw [Nat.card_congr (Additive.toMul : Additive G ≃ G)]
    exact hcard
  have hrank : Module.finrank (ZMod 3) (Additive G) = 4 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := Additive G)
    rw [Nat.card_zmod, hcard'] at h
    have h' : 3 ^ Module.finrank (ZMod 3) (Additive G) = 3 ^ 4 := by
      rw [← h]
      norm_num
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h'
  let bs : Module.Basis (Fin 4) (ZMod 3) (Additive G) :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp [hrank])
  refine ⟨AddEquiv.toMultiplicativeRight bs.equivFun.toAddEquiv, fun i => ?_⟩
  have hbs : bs i = Additive.ofMul (b i) := by simp [bs]
  rw [AddEquiv.toMultiplicativeRight_apply_apply]
  show Multiplicative.ofAdd (bs.equivFun (Additive.ofMul (b i))) = _
  rw [← hbs]
  congr 1
  funext j
  simp [Pi.single_apply, eq_comm]

theorem sum_val_zsmul_single (w : Fin 4 → ZMod 3) :
    ((w 0).val : ℤ) • (Pi.single 0 1 : Fin 4 → ZMod 3) + ((w 1).val : ℤ) • Pi.single 1 1 +
      ((w 2).val : ℤ) • Pi.single 2 1 + ((w 3).val : ℤ) • Pi.single 3 1 = w := by
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, Pi.single_apply]
  fin_cases i <;> simp

theorem Heis4Data.exists_crd {M : Type*} [Group M] {s f₁ f₂ f₃ f₄ : M}
    (h : Heis4Data s f₁ f₂ f₃ f₄) :
    ∃ crd : M →* Multiplicative (Fin 4 → ZMod 3),
      Function.Surjective crd ∧ (∀ m, crd m = 1 ↔ m ∈ Subgroup.zpowers s) ∧
      crd f₁ = Multiplicative.ofAdd (Pi.single 0 1) ∧
      crd f₂ = Multiplicative.ofAdd (Pi.single 1 1) ∧
      crd f₃ = Multiplicative.ofAdd (Pi.single 2 1) ∧
      crd f₄ = Multiplicative.ofAdd (Pi.single 3 1) := by
  have hle : Subgroup.zpowers s ≤ Subgroup.center M := by
    rw [Subgroup.zpowers_le, Subgroup.mem_center_iff]
    exact h.s_central
  have hZ : (Subgroup.zpowers s).Normal := Subgroup.normal_of_le_center hle
  have hZcard : Nat.card (Subgroup.zpowers s) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime h.s_cube h.s_ne_one]
  have hQcard : Nat.card (M ⧸ Subgroup.zpowers s) = 81 := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.zpowers s)
    rw [h.card_eq, hZcard] at this
    omega
  have hcomm : ∀ x y : M ⧸ Subgroup.zpowers s, x * y = y * x := by
    intro x y
    induction x using QuotientGroup.induction_on with
    | H x =>
      induction y using QuotientGroup.induction_on with
      | H y =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
        simpa [mul_assoc] using h.comm_mem y⁻¹ x⁻¹
  have hcube : ∀ x : M ⧸ Subgroup.zpowers s, x ^ 3 = 1 := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H x => rw [← QuotientGroup.mk_pow, h.cube x, QuotientGroup.mk_one]
  let _ : CommGroup (M ⧸ Subgroup.zpowers s) :=
    { (inferInstance : Group (M ⧸ Subgroup.zpowers s)) with mul_comm := hcomm }
  let π : M →* M ⧸ Subgroup.zpowers s := QuotientGroup.mk' _
  let f : Fin 4 → M := ![f₁, f₂, f₃, f₄]
  obtain ⟨e, he⟩ := exists_mulEquiv_of_card_eq_81 hQcard hcube (fun i => π (f i)) (by
    intro p hp
    simp only [Fin.prod_univ_four] at hp
    simp only [f, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hp
    have hp' : π (f₁ ^ p 0 * f₂ ^ p 1 * f₃ ^ p 2 * f₄ ^ p 3) = 1 := by
      simpa only [map_mul, map_zpow] using hp
    obtain ⟨d₁, d₂, d₃, d₄⟩ := h.indep _ _ _ _ ((QuotientGroup.eq_one_iff _).1 hp')
    intro i
    fin_cases i
    exacts [d₁, d₂, d₃, d₄])
  refine ⟨(e : M ⧸ Subgroup.zpowers s →* Multiplicative (Fin 4 → ZMod 3)).comp π,
    e.surjective.comp (QuotientGroup.mk'_surjective _), fun m => ?_, he 0, he 1, he 2, he 3⟩
  show e (π m) = 1 ↔ _
  rw [MulEquiv.map_eq_one_iff]
  exact QuotientGroup.eq_one_iff m

theorem Heis4Data.exists_normal_form {M : Type*} [Group M] {s f₁ f₂ f₃ f₄ : M}
    (h : Heis4Data s f₁ f₂ f₃ f₄) (m : M) :
    ∃ k p₁ p₂ p₃ p₄ : ℤ, m = s ^ k * f₁ ^ p₁ * f₂ ^ p₂ * f₃ ^ p₃ * f₄ ^ p₄ := by
  obtain ⟨crd, -, hker, h₁, h₂, h₃, h₄⟩ := h.exists_crd
  let v : Fin 4 → ZMod 3 := Multiplicative.toAdd (crd m)
  let p : Fin 4 → ℤ := fun i => ((v i).val : ℤ)
  have hn : crd (f₁ ^ p 0 * f₂ ^ p 1 * f₃ ^ p 2 * f₄ ^ p 3) = crd m := by
    rw [map_mul, map_mul, map_mul, map_zpow, map_zpow, map_zpow, map_zpow, h₁, h₂, h₃, h₄,
      ← ofAdd_zsmul, ← ofAdd_zsmul, ← ofAdd_zsmul, ← ofAdd_zsmul, ← ofAdd_add, ← ofAdd_add,
      ← ofAdd_add]
    refine (congrArg Multiplicative.ofAdd ?_).trans (ofAdd_toAdd _)
    exact sum_val_zsmul_single _
  have hmem : (f₁ ^ p 0 * f₂ ^ p 1 * f₃ ^ p 2 * f₄ ^ p 3)⁻¹ * m ∈ Subgroup.zpowers s := by
    rw [← hker, map_mul, map_inv]
    exact inv_mul_eq_one.2 hn
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
  refine ⟨k, p 0, p 1, p 2, p 3, ?_⟩
  have hc : (f₁ ^ p 0 * f₂ ^ p 1 * f₃ ^ p 2 * f₄ ^ p 3) * s ^ k =
      s ^ k * (f₁ ^ p 0 * f₂ ^ p 1 * f₃ ^ p 2 * f₄ ^ p 3) :=
    Commute.zpow_right (show Commute (f₁ ^ p 0 * f₂ ^ p 1 * f₃ ^ p 2 * f₄ ^ p 3) s from
      h.s_central _) k
  calc m = (f₁ ^ p 0 * f₂ ^ p 1 * f₃ ^ p 2 * f₄ ^ p 3) * s ^ k := by
        rw [hk, mul_inv_cancel_left]
    _ = s ^ k * (f₁ ^ p 0 * f₂ ^ p 1 * f₃ ^ p 2 * f₄ ^ p 3) := hc
    _ = s ^ k * f₁ ^ p 0 * f₂ ^ p 1 * f₃ ^ p 2 * f₄ ^ p 3 := by simp only [mul_assoc]

end CFSG.Sporadic.Recognition.JankoWong
