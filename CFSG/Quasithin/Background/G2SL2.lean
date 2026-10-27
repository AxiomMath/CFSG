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
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
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


open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups commutatorElement

namespace CFSG.Quasithin.SL2Model

variable {F : Type*} [Field F]

abbrev Wm (F : Type*) [Field F] : Type _ := Multiplicative (Fin 2 → F)

@[expose] def natAct : SL(2, F) →* MulAut (Wm F) where
  toFun A :=
    { toFun := fun w => Multiplicative.ofAdd (A • Multiplicative.toAdd w)
      invFun := fun w => Multiplicative.ofAdd (A⁻¹ • Multiplicative.toAdd w)
      left_inv := fun w => by simp
      right_inv := fun w => by simp
      map_mul' := fun a b => by simp [smul_add] }
  map_one' := by
    ext w
    simp
  map_mul' := fun A B => by
    ext w
    simp [mul_smul]

theorem natAct_apply (A : SL(2, F)) (w : Wm F) :
    natAct A w = Multiplicative.ofAdd (A • Multiplicative.toAdd w) := rfl

@[expose] def e12 (c : F) : SL(2, F) := ⟨!![1, c; 0, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def e21 (c : F) : SL(2, F) := ⟨!![1, 0; c, 1], by simp [Matrix.det_fin_two]⟩

theorem smul_eq_mulVec' (A : SL(2, F)) (w : Fin 2 → F) :
    A • w = (A : Matrix (Fin 2) (Fin 2) F).mulVec w := rfl

@[simp] theorem e12_coe (c : F) : (e12 c : Matrix (Fin 2) (Fin 2) F) = !![1, c; 0, 1] := rfl

@[simp] theorem e21_coe (c : F) : (e21 c : Matrix (Fin 2) (Fin 2) F) = !![1, 0; c, 1] := rfl

theorem e12_smul (c : F) (w : Fin 2 → F) : e12 c • w = ![w 0 + c * w 1, w 1] := by
  rw [smul_eq_mulVec']
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem e21_smul (c : F) (w : Fin 2 → F) : e21 c • w = ![w 0, w 1 + c * w 0] := by
  rw [smul_eq_mulVec']
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, add_comm]

theorem e12_add (a b : F) : e12 (a + b) = e12 a * e12 b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem e21_add (a b : F) : e21 (a + b) = e21 a * e21 b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem e12_zero : e12 (0 : F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e12]

theorem e12_injective : Function.Injective (e12 : F → SL(2, F)) := by
  intro a b h
  have := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simpa [e12] using this


section Normalizing

@[expose] def fcoord (ρ : MulAut (Wm F)) (x : F) : F :=
  Multiplicative.toAdd (ρ (Multiplicative.ofAdd ![x, 0])) 0

@[expose] def gcoord (ρ : MulAut (Wm F)) (y : F) : F :=
  Multiplicative.toAdd (ρ (Multiplicative.ofAdd ![0, y])) 0

theorem normalizing_aux (ρ : MulAut (Wm F))
    (ha : ∀ w : Wm F, Multiplicative.toAdd (ρ w) 1 = Multiplicative.toAdd w 1) (x y : F) :
    Multiplicative.toAdd (ρ (Multiplicative.ofAdd ![x, y])) = ![fcoord ρ x + gcoord ρ y, y] := by
  have h1 : (Multiplicative.ofAdd ![x, y] : Wm F) =
      Multiplicative.ofAdd ![x, 0] * Multiplicative.ofAdd ![0, y] := by
    ext i
    fin_cases i <;> simp
  have h2 := ha (Multiplicative.ofAdd ![x, 0])
  have h3 := ha (Multiplicative.ofAdd ![0, y])
  simp only [toAdd_ofAdd] at h2 h3
  rw [h1, map_mul, toAdd_mul]
  ext i
  fin_cases i
  · simp [fcoord, gcoord]
  · simp [h2, h3]

theorem smul_vec (A : SL(2, F)) (u v : F) :
    A • (![u, v] : Fin 2 → F) =
      ![A.1 0 0 * u + A.1 0 1 * v, A.1 1 0 * u + A.1 1 1 * v] := by
  rw [smul_eq_mulVec']
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem det_eq_one' (A : SL(2, F)) : A.1 0 0 * A.1 1 1 - A.1 0 1 * A.1 1 0 = 1 := by
  have := A.2
  rwa [Matrix.det_fin_two] at this

theorem normalizing_coord (ρ : MulAut (Wm F))
    (ha : ∀ w : Wm F, Multiplicative.toAdd (ρ w) 1 = Multiplicative.toAdd w 1)
    (A A' : SL(2, F)) (hA : ∀ w : Wm F, ρ (natAct A w) = natAct A' (ρ w)) (x y : F) :
    fcoord ρ (A.1 0 0 * x + A.1 0 1 * y) + gcoord ρ (A.1 1 0 * x + A.1 1 1 * y) =
        A'.1 0 0 * (fcoord ρ x + gcoord ρ y) + A'.1 0 1 * y ∧
      A.1 1 0 * x + A.1 1 1 * y = A'.1 1 0 * (fcoord ρ x + gcoord ρ y) + A'.1 1 1 * y := by
  have h := congrArg Multiplicative.toAdd (hA (Multiplicative.ofAdd ![x, y]))
  have hL : Multiplicative.toAdd (ρ (natAct A (Multiplicative.ofAdd ![x, y]))) =
      ![fcoord ρ (A.1 0 0 * x + A.1 0 1 * y) + gcoord ρ (A.1 1 0 * x + A.1 1 1 * y),
        A.1 1 0 * x + A.1 1 1 * y] := by
    rw [natAct_apply, toAdd_ofAdd, smul_vec]
    exact normalizing_aux ρ ha _ _
  have hR : Multiplicative.toAdd (natAct A' (ρ (Multiplicative.ofAdd ![x, y]))) =
      ![A'.1 0 0 * (fcoord ρ x + gcoord ρ y) + A'.1 0 1 * y,
        A'.1 1 0 * (fcoord ρ x + gcoord ρ y) + A'.1 1 1 * y] := by
    rw [natAct_apply, toAdd_ofAdd, normalizing_aux ρ ha, smul_vec]
  rw [hL, hR] at h
  have h2 := congrFun h 0
  have h3 := congrFun h 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h2 h3
  exact ⟨h2, h3⟩

theorem fcoord_add (ρ : MulAut (Wm F)) (x x' : F) :
    fcoord ρ (x + x') = fcoord ρ x + fcoord ρ x' := by
  have h : (Multiplicative.ofAdd ![x + x', 0] : Wm F) =
      Multiplicative.ofAdd ![x, 0] * Multiplicative.ofAdd ![x', 0] := by
    ext i
    fin_cases i <;> simp
  simp [fcoord, h, map_mul]

theorem gcoord_add (ρ : MulAut (Wm F)) (y y' : F) :
    gcoord ρ (y + y') = gcoord ρ y + gcoord ρ y' := by
  have h : (Multiplicative.ofAdd ![0, y + y'] : Wm F) =
      Multiplicative.ofAdd ![0, y] * Multiplicative.ofAdd ![0, y'] := by
    ext i
    fin_cases i <;> simp
  simp [gcoord, h, map_mul]

theorem fcoord_zero (ρ : MulAut (Wm F)) : fcoord ρ 0 = 0 := by
  have : (Multiplicative.ofAdd ![0, 0] : Wm F) = 1 := by
    ext i
    fin_cases i <;> simp
  simp [fcoord, this]

theorem gcoord_zero (ρ : MulAut (Wm F)) : gcoord ρ 0 = 0 := by
  have : (Multiplicative.ofAdd ![0, 0] : Wm F) = 1 := by
    ext i
    fin_cases i <;> simp
  simp [gcoord, this]

theorem fcoord_injective (ρ : MulAut (Wm F))
    (ha : ∀ w : Wm F, Multiplicative.toAdd (ρ w) 1 = Multiplicative.toAdd w 1) :
    Function.Injective (fcoord ρ) := by
  intro x x' h
  have h1 := normalizing_aux ρ ha x 0
  have h2 := normalizing_aux ρ ha x' 0
  rw [gcoord_zero, add_zero, h] at h1
  rw [gcoord_zero, add_zero] at h2
  have h3 : ρ (Multiplicative.ofAdd ![x, 0]) = ρ (Multiplicative.ofAdd ![x', 0]) := by
    apply Multiplicative.toAdd.injective
    rw [h1, h2]
  have h4 := ρ.injective h3
  have h5 := congrFun (Multiplicative.ofAdd.injective h4) 0
  simpa using h5

variable [CharP F 2]

theorem eq_one_of_pow_two_pow_eq_one {a : F} {k : ℕ} (h : a ^ 2 ^ k = 1) : a = 1 := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : (a - 1) ^ 2 ^ k = 0 := by
    rw [sub_pow_char_pow (p := 2), h, one_pow, sub_self]
  exact sub_eq_zero.1 ((pow_eq_zero_iff (by positivity)).1 h1)

theorem normalizing_lemma (ρ : MulAut (Wm F))
    (ha : ∀ w : Wm F, Multiplicative.toAdd (ρ w) 1 = Multiplicative.toAdd w 1)
    (hb : ∀ A : SL(2, F), ∃ A' : SL(2, F), ∀ w : Wm F, ρ (natAct A w) = natAct A' (ρ w))
    (hc : ∃ k : ℕ, ρ ^ (2 ^ k) = 1) :
    ∃ b : F, ∀ w : Wm F, ρ w = natAct (e12 b) w := by
  have hf1 : fcoord ρ 1 ≠ 0 := by
    intro h
    have := fcoord_injective ρ ha (h.trans (fcoord_zero ρ).symm)
    exact one_ne_zero this
  have hfmul : ∀ c y : F, fcoord ρ (c * y) = fcoord ρ c * y := by
    intro c y
    obtain ⟨A', hA'⟩ := hb (e12 c)
    have h := normalizing_coord ρ ha (e12 c) A' hA'
    have h10 : A'.1 1 0 = 0 := by
      have h1 := (h 1 0).2
      simp [gcoord_zero] at h1
      rcases h1 with h1 | h1
      · exact h1
      · exact absurd h1 hf1
    have h11 : A'.1 1 1 = 1 := by
      have h1 := (h 0 1).2
      simp [h10] at h1
      exact h1.symm
    have h00 : A'.1 0 0 = 1 := by
      have := det_eq_one' A'
      rw [h10, h11] at this
      simpa using this
    have h2 := (h 0 y).1
    simp [h00, fcoord_zero] at h2
    have h3 := (h 0 1).1
    simp [h00, fcoord_zero] at h3
    have h4 : fcoord ρ (c * y) = A'.1 0 1 * y := by linear_combination h2
    have h5 : fcoord ρ c = A'.1 0 1 := by linear_combination h3
    rw [h4, h5]
  have hfx : ∀ x, fcoord ρ x = fcoord ρ 1 * x := fun x => by
    have := hfmul 1 x
    simpa using this
  obtain ⟨A', hA'⟩ := hb (e21 1)
  have h := normalizing_coord ρ ha (e21 1) A' hA'
  have hc' : A'.1 1 0 * fcoord ρ 1 = 1 := by
    have h1 := (h 1 0).2
    simp [gcoord_zero] at h1
    exact h1.symm
  have hg : ∀ y, gcoord ρ y = fcoord ρ 1 * (1 - A'.1 1 1) * y := by
    intro y
    have h1 := (h 0 y).2
    simp [fcoord_zero] at h1
    have h2 : A'.1 1 0 * gcoord ρ y = (1 - A'.1 1 1) * y := by linear_combination h1.symm
    calc gcoord ρ y = (A'.1 1 0 * fcoord ρ 1) * gcoord ρ y := by rw [hc']; ring
      _ = fcoord ρ 1 * (A'.1 1 0 * gcoord ρ y) := by ring
      _ = fcoord ρ 1 * ((1 - A'.1 1 1) * y) := by rw [h2]
      _ = fcoord ρ 1 * (1 - A'.1 1 1) * y := by ring
  have hpow : ∀ m : ℕ, (ρ ^ m) (Multiplicative.ofAdd ![1, 0]) =
      Multiplicative.ofAdd ![fcoord ρ 1 ^ m, 0] := by
    intro m
    induction m with
    | zero =>
      simp
    | succ m ih =>
      rw [pow_succ', MulAut.mul_apply, ih]
      apply Multiplicative.toAdd.injective
      rw [normalizing_aux ρ ha, gcoord_zero, hfx, pow_succ']
      ext i
      fin_cases i <;> simp
  obtain ⟨k, hk⟩ := hc
  have ha1 : fcoord ρ 1 = 1 := by
    have h1 := hpow (2 ^ k)
    rw [hk, MulAut.one_apply] at h1
    have h2 := congrFun (Multiplicative.ofAdd.injective h1) 0
    simp at h2
    exact eq_one_of_pow_two_pow_eq_one h2.symm
  have hg' : ∀ y, gcoord ρ y = gcoord ρ 1 * y := fun y => by
    rw [hg y, hg 1]
    ring
  refine ⟨gcoord ρ 1, fun w => ?_⟩
  have hw : w = Multiplicative.ofAdd ![Multiplicative.toAdd w 0, Multiplicative.toAdd w 1] := by
    apply Multiplicative.toAdd.injective
    ext i
    fin_cases i <;> simp
  apply Multiplicative.toAdd.injective
  rw [hw, natAct_apply, toAdd_ofAdd, e12_smul, normalizing_aux ρ ha, hfx, hg', ha1]
  simp

end Normalizing

section Subgroups

@[expose] def e12hom : Multiplicative F →* SL(2, F) where
  toFun c := e12 (Multiplicative.toAdd c)
  map_one' := e12_zero
  map_mul' _ _ := e12_add _ _

@[expose] def Rg (F : Type*) [Field F] : Subgroup SL(2, F) := (e12hom (F := F)).range

theorem mem_Rg {A : SL(2, F)} : A ∈ Rg F ↔ ∃ b : F, e12 b = A := by
  unfold Rg
  rw [MonoidHom.mem_range]
  exact ⟨fun ⟨c, hc⟩ => ⟨Multiplicative.toAdd c, hc⟩, fun ⟨b, hb⟩ => ⟨Multiplicative.ofAdd b, hb⟩⟩

theorem e12_mem_Rg (b : F) : e12 b ∈ Rg F := mem_Rg.2 ⟨b, rfl⟩

theorem e12_mul_self [CharP F 2] (b : F) : e12 b * e12 b = 1 := by
  rw [← e12_add, CharTwo.add_self_eq_zero, e12_zero]

theorem Rg_card : Nat.card (Rg F) = Nat.card F := by
  have h : Function.Injective (e12hom (F := F)) := fun _ _ hab => by
    exact Multiplicative.toAdd.injective (e12_injective hab)
  exact (Nat.card_congr (MonoidHom.ofInjective h).toEquiv).symm.trans
    (Nat.card_congr Multiplicative.toAdd)

theorem Rg_isPGroup [CharP F 2] : IsPGroup 2 (Rg F) := by
  intro x
  refine ⟨1, ?_⟩
  obtain ⟨b, hb⟩ := mem_Rg.1 x.2
  apply Subtype.ext
  simp only [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
  rw [pow_two, ← hb, e12_mul_self]


end Subgroups

section Cardinality

variable [Finite F]

theorem card_SL2 : Nat.card SL(2, F) = Nat.card F * (Nat.card F ^ 2 - 1) := by
  have : Fintype F := Fintype.ofFinite F
  rw [Matrix.card_SL_field 2, Nat.card_eq_fintype_card]
  simp only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  set q := Fintype.card F with hq
  have hq1 : 1 < q := Fintype.one_lt_card
  have h1 : q ^ 2 - q = q * (q - 1) := by
    rw [Nat.mul_sub, mul_one, pow_two]
  rw [h1]
  exact Nat.div_eq_of_eq_mul_left (by omega) (by ring)

theorem card_F_even [CharP F 2] : Even (Nat.card F) := by
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨n, -, hn⟩ := FiniteField.card F 2
  rw [Nat.card_eq_fintype_card, hn]
  exact (Nat.even_pow.2 ⟨even_two, n.pos.ne'⟩)

theorem Rg_index_odd [CharP F 2] : ¬ 2 ∣ (Rg F).index := by
  have h := Subgroup.card_mul_index (Rg F)
  rw [Rg_card, card_SL2] at h
  have hq : 0 < Nat.card F := Nat.card_pos
  have h2 : (Rg F).index = Nat.card F ^ 2 - 1 := by
    refine Nat.eq_of_mul_eq_mul_left hq ?_
    exact h
  rw [h2]
  have hev := card_F_even (F := F)
  have h3 : Even (Nat.card F ^ 2) := Nat.even_pow.2 ⟨hev, two_ne_zero⟩
  have h4 : 1 ≤ Nat.card F ^ 2 := Nat.one_le_pow _ _ hq
  intro hd
  obtain ⟨k, hk⟩ := h3
  omega

end Cardinality


section Generation

variable [CharP F 2]

omit [CharP F 2] in
theorem transvection_zero_one (c : F) :
    (SpecialLinearGroup.transvection (zero_ne_one : (0 : Fin 2) ≠ 1) c) = e12 c := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [SpecialLinearGroup.transvection, Matrix.transvection]

omit [CharP F 2] in
theorem transvection_one_zero (c : F) :
    (SpecialLinearGroup.transvection (one_ne_zero : (1 : Fin 2) ≠ 0) c) = e21 c := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [SpecialLinearGroup.transvection, Matrix.transvection]

theorem gen_identity (a b c d t : F) (hc : c ≠ 0) (hdet : a * d - b * c = 1) :
    (!![1, d / c; 0, 1] * (Matrix.adjugate !![a, b; c, d] * !![1, t; 0, 1] * !![a, b; c, d]) *
      !![1, d / c; 0, 1] : Matrix (Fin 2) (Fin 2) F) = !![1, 0; t * c ^ 2, 1] := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> ring_nf
  · linear_combination hdet
  · linear_combination (2 * d) * hdet + d * h2
  · linear_combination (-c * t) * h2
  · linear_combination hdet + (-c * t * d) * h2

theorem e12_mul_conj_e12 (A : SL(2, F)) (hA : A.1 1 0 ≠ 0) (t : F) :
    e12 (A.1 1 1 / A.1 1 0) * (A⁻¹ * e12 t * A) * e12 (A.1 1 1 / A.1 1 0) =
      e21 (t * A.1 1 0 ^ 2) := by
  have hdet : A.1 0 0 * A.1 1 1 - A.1 0 1 * A.1 1 0 = 1 := det_eq_one' A
  apply Subtype.ext
  have := gen_identity (A.1 0 0) (A.1 0 1) (A.1 1 0) (A.1 1 1) t hA hdet
  simp only [coe_mul, coe_inv, e12_coe, e21_coe]
  rw [Matrix.eta_fin_two (A.1)]
  exact this

theorem Rg_sup_conj_eq_top (A : SL(2, F)) (hA : A.1 1 0 ≠ 0) :
    Rg F ⊔ (Rg F).map (MulAut.conj A⁻¹).toMonoidHom = ⊤ := by
  set X := Rg F ⊔ (Rg F).map (MulAut.conj A⁻¹).toMonoidHom with hX
  have h12 : ∀ b, e12 b ∈ X := fun b => Subgroup.mem_sup_left (e12_mem_Rg b)
  have h21 : ∀ s, e21 s ∈ X := by
    intro s
    have hc2 : A.1 1 0 ^ 2 ≠ 0 := pow_ne_zero 2 hA
    have h := e12_mul_conj_e12 A hA (s / A.1 1 0 ^ 2)
    rw [div_mul_cancel₀ _ hc2] at h
    rw [← h]
    refine X.mul_mem (X.mul_mem (h12 _) ?_) (h12 _)
    refine Subgroup.mem_sup_right ⟨e12 (s / A.1 1 0 ^ 2), e12_mem_Rg _, ?_⟩
    simp
  rw [eq_top_iff]
  intro A' _
  refine SL2.transvection_induction (fun B => B ∈ X) (fun i j hij c => ?_)
    (fun B C hB hC => X.mul_mem hB hC) A'
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · rw [show (⟨0, by decide⟩ : Fin 2) = 0 from rfl, show (⟨1, by decide⟩ : Fin 2) = 1 from rfl] at *
    simp only [Fin.zero_eta, Fin.mk_one]
    rw [transvection_zero_one]
    exact h12 c
  · simp only [Fin.zero_eta, Fin.mk_one]
    rw [transvection_one_zero]
    exact h21 c
  · exact absurd rfl hij

end Generation


section Torus

@[expose] def dgm (d : Fˣ) : SL(2, F) :=
  ⟨!![(d : F), 0; 0, ((d⁻¹ : Fˣ) : F)], by simp [Matrix.det_fin_two]⟩

@[simp] theorem dgm_coe (d : Fˣ) :
    (dgm d : Matrix (Fin 2) (Fin 2) F) = !![(d : F), 0; 0, ((d⁻¹ : Fˣ) : F)] := rfl

theorem dgm_mul (d d' : Fˣ) : dgm d * dgm d' = dgm (d * d') := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem dgm_one : dgm (1 : Fˣ) = (1 : SL(2, F)) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp

@[expose] def dghom : Fˣ →* SL(2, F) where
  toFun := dgm
  map_one' := dgm_one
  map_mul' a b := (dgm_mul a b).symm

theorem dgm_inv (d : Fˣ) : (dgm d)⁻¹ = dgm d⁻¹ := (map_inv (dghom (F := F)) d).symm

theorem dgm_smul (d : Fˣ) (w : Fin 2 → F) : dgm d • w = ![(d : F) * w 0, ((d⁻¹ : Fˣ) : F) * w 1] := by
  rw [smul_eq_mulVec']
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem dgm_conj_e12 (d : Fˣ) (c : F) :
    dgm d * e12 c * (dgm d)⁻¹ = e12 ((d : F) ^ 2 * c) := by
  rw [dgm_inv]
  apply Subtype.ext
  have h1 : (d : F) * ((d⁻¹ : Fˣ) : F) = 1 := by simp
  have h2 : ((d⁻¹ : Fˣ) : F) * (d : F) = 1 := by simp
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  all_goals ring_nf

theorem odd_orderOf_dgm [Finite F] [CharP F 2] (d : Fˣ) : Odd (orderOf (dgm d)) := by
  have h1 : orderOf (dghom (F := F) d) ∣ orderOf d := orderOf_map_dvd dghom d
  have h2 : orderOf d ∣ Nat.card Fˣ := orderOf_dvd_natCard d
  have hodd : Odd (Nat.card Fˣ) := by
    rw [Nat.card_units]
    obtain ⟨k, hk⟩ := card_F_even (F := F)
    have : 0 < Nat.card F := Nat.card_pos
    exact ⟨k - 1, by omega⟩
  exact Odd.of_dvd_nat hodd (h1.trans h2)

theorem Rg_torus_irreducible [Finite F] [CharP F 2] (X : Subgroup SL(2, F)) (hXR : X ≤ Rg F)
    (hX : ∀ d : Fˣ, ∀ x ∈ X, dgm d * x * (dgm d)⁻¹ ∈ X) : X = ⊥ ∨ X = Rg F := by
  by_cases hbot : X = ⊥
  · exact Or.inl hbot
  refine Or.inr (le_antisymm hXR ?_)
  obtain ⟨⟨x, hxX⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hbot
  obtain ⟨c, rfl⟩ := mem_Rg.1 (hXR hxX)
  have hc : c ≠ 0 := by
    rintro rfl
    exact hx1 (Subtype.ext (by simp [e12_zero]))
  intro y hy
  obtain ⟨b, rfl⟩ := mem_Rg.1 hy
  by_cases hb : b = 0
  · rw [hb, e12_zero]
    exact X.one_mem
  have hsq : IsSquare (b / c) := FiniteField.isSquare_of_char_two (ringChar.eq F 2) _
  obtain ⟨d, hd⟩ := hsq
  have hd0 : d ≠ 0 := by
    rintro rfl
    apply hb
    have : b / c = 0 := by simpa using hd
    simpa [hc] using this
  have h := hX (Units.mk0 d hd0) _ hxX
  rw [dgm_conj_e12] at h
  have e : ((Units.mk0 d hd0 : Fˣ) : F) ^ 2 * c = b := by
    rw [Units.val_mk0, pow_two, ← hd]
    field_simp
  rwa [e] at h

theorem Rg_commutator [CharP F 2] (hq : ∃ a : F, a ≠ 0 ∧ a ^ 2 ≠ 1) {r : SL(2, F)}
    (hr : r ∈ Rg F) : ∃ r' ∈ Rg F, ∃ d : Fˣ, r = r' * dgm d * r'⁻¹ * (dgm d)⁻¹ := by
  obtain ⟨a, ha0, ha1⟩ := hq
  obtain ⟨b, rfl⟩ := mem_Rg.1 hr
  have h1 : (1 : F) + a ^ 2 ≠ 0 := by
    intro h
    apply ha1
    have : a ^ 2 = -1 := by linear_combination h
    rw [this, CharTwo.neg_eq]
  refine ⟨e12 (b / (1 + a ^ 2)), e12_mem_Rg _, Units.mk0 a ha0, ?_⟩
  have hinv : ∀ t : F, (e12 t)⁻¹ = e12 t := fun t => inv_eq_of_mul_eq_one_right (e12_mul_self t)
  have h2 := dgm_conj_e12 (Units.mk0 a ha0) (b / (1 + a ^ 2))
  rw [Units.val_mk0] at h2
  symm
  calc e12 (b / (1 + a ^ 2)) * dgm (Units.mk0 a ha0) * (e12 (b / (1 + a ^ 2)))⁻¹ *
        (dgm (Units.mk0 a ha0))⁻¹
      = e12 (b / (1 + a ^ 2)) * (dgm (Units.mk0 a ha0) * (e12 (b / (1 + a ^ 2)))⁻¹ *
          (dgm (Units.mk0 a ha0))⁻¹) := by group
    _ = e12 (b / (1 + a ^ 2)) * (dgm (Units.mk0 a ha0) * e12 (b / (1 + a ^ 2)) *
          (dgm (Units.mk0 a ha0))⁻¹)⁻¹ := by group
    _ = e12 b := by
      rw [h2, hinv, ← e12_add]
      congr 1
      field_simp

end Torus


section Transitivity

theorem exists_smul_eq_e0 (w : Fin 2 → F) (hw : w ≠ 0) :
    ∃ g : SL(2, F), g • w = Pi.single 0 1 := by
  have hw' : w 0 ≠ 0 ∨ w 1 ≠ 0 := by
    by_contra h
    apply hw
    ext i
    fin_cases i
    · exact not_not.1 fun h0 => h (Or.inl h0)
    · exact not_not.1 fun h1 => h (Or.inr h1)
  obtain ⟨a, b, hab⟩ : ∃ a b : F, a * w 0 + b * w 1 = 1 := by
    rcases hw' with h | h
    · exact ⟨(w 0)⁻¹, 0, by simp [h]⟩
    · exact ⟨0, (w 1)⁻¹, by simp [h]⟩
  refine ⟨⟨!![a, b; -w 1, w 0], by simp [Matrix.det_fin_two]; linear_combination hab⟩, ?_⟩
  change (!![a, b; -w 1, w 0] : Matrix (Fin 2) (Fin 2) F).mulVec w = _
  ext i
  fin_cases i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hab]
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring

theorem exists_smul_eq (w v : Fin 2 → F) (hw : w ≠ 0) (hv : v ≠ 0) :
    ∃ A : SL(2, F), A • w = v := by
  obtain ⟨g, hg⟩ := exists_smul_eq_e0 w hw
  obtain ⟨g', hg'⟩ := exists_smul_eq_e0 v hv
  refine ⟨g'⁻¹ * g, ?_⟩
  rw [mul_smul, hg, ← hg', inv_smul_smul]

theorem natAct_irreducible (X : Subgroup (Wm F))
    (hX : ∀ A : SL(2, F), ∀ x ∈ X, natAct A x ∈ X) : X = ⊥ ∨ X = ⊤ := by
  by_cases hbot : X = ⊥
  · exact Or.inl hbot
  refine Or.inr (eq_top_iff.2 fun v _ => ?_)
  obtain ⟨⟨x, hxX⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hbot
  by_cases hv : Multiplicative.toAdd v = 0
  · have : v = 1 := Multiplicative.toAdd.injective (by simpa using hv)
    rw [this]
    exact X.one_mem
  have hx0 : Multiplicative.toAdd x ≠ 0 := fun h =>
    hx1 (Subtype.ext (Multiplicative.toAdd.injective (by simpa using h)))
  obtain ⟨A, hA⟩ := exists_smul_eq (Multiplicative.toAdd x) (Multiplicative.toAdd v) hx0 hv
  have := hX A x hxX
  rwa [natAct_apply, hA, ofAdd_toAdd] at this

end Transitivity


section Two

variable [CharP F 2]

omit [CharP F 2] in
theorem eq_zero_or_one_of_card_two [Finite F] (hF : Nat.card F = 2) (x : F) : x = 0 ∨ x = 1 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  by_contra h
  push Not at h
  have h3 : ({0, 1, x} : Finset F).card = 3 := by
    have h01 : (0 : F) ≠ 1 := zero_ne_one
    rw [Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm h.2)]
    simp [h01, Ne.symm h.1]
  have := Finset.card_le_univ ({0, 1, x} : Finset F)
  rw [h3, ← Nat.card_eq_fintype_card, hF] at this
  omega

@[expose] def c3 (F : Type*) [Field F] : SL(2, F) := e12 1 * e21 1

omit [CharP F 2] in
theorem c3_coe : (c3 F : Matrix (Fin 2) (Fin 2) F) = !![1 + 1, 1; 1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [c3, Matrix.mul_apply, Fin.sum_univ_two]

theorem c3_pow_three : c3 F ^ 3 = 1 := by
  apply Subtype.ext
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have h11 : (1 : F) + 1 = 0 := by linear_combination h2
  rw [pow_succ, pow_two]
  simp only [coe_mul, c3_coe, h11]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h11]

omit [CharP F 2] in
theorem c3_ne_one : c3 F ≠ 1 := by
  intro h
  have := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simp [c3_coe] at this

theorem orderOf_c3 : orderOf (c3 F) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime c3_pow_three c3_ne_one

omit [CharP F 2] in
theorem card_SL2_of_card_two [Finite F] (hF : Nat.card F = 2) : Nat.card SL(2, F) = 6 := by
  rw [card_SL2, hF]
  norm_num

theorem index_zpowers_c3 [Finite F] (hF : Nat.card F = 2) :
    (Subgroup.zpowers (c3 F)).index = 2 := by
  have h := Subgroup.card_mul_index (Subgroup.zpowers (c3 F))
  rw [Nat.card_zpowers, orderOf_c3, card_SL2_of_card_two hF] at h
  omega


theorem e21_mul_self (b : F) : e21 b * e21 b = 1 := by
  rw [← e21_add, CharTwo.add_self_eq_zero]
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem e21_mem_sup_of_card_two [Finite F] (hF : Nat.card F = 2) (s : F) :
    e21 s ∈ Subgroup.zpowers (c3 F) ⊔ Rg F := by
  rcases eq_zero_or_one_of_card_two hF s with rfl | rfl
  · have : e21 (0 : F) = 1 := by
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    rw [this]
    exact Subgroup.one_mem _
  · have h : e21 (1 : F) = (e12 1)⁻¹ * c3 F := by
      rw [inv_eq_of_mul_eq_one_right (e12_mul_self (1 : F)), c3, ← mul_assoc, e12_mul_self, one_mul]
    rw [h]
    exact Subgroup.mul_mem _
      (Subgroup.mem_sup_right (Subgroup.inv_mem _ (e12_mem_Rg 1)))
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))

theorem zpowers_c3_sup_Rg [Finite F] (hF : Nat.card F = 2) :
    Subgroup.zpowers (c3 F) ⊔ Rg F = ⊤ := by
  rw [eq_top_iff]
  intro A _
  refine SL2.transvection_induction (fun B => B ∈ Subgroup.zpowers (c3 F) ⊔ Rg F)
    (fun i j hij c => ?_) (fun B C hB hC => Subgroup.mul_mem _ hB hC) A
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · simp only [Fin.zero_eta, Fin.mk_one]
    rw [transvection_zero_one]
    exact Subgroup.mem_sup_right (e12_mem_Rg c)
  · simp only [Fin.zero_eta, Fin.mk_one]
    rw [transvection_one_zero]
    exact e21_mem_sup_of_card_two hF c
  · exact absurd rfl hij

omit [CharP F 2] in
theorem Rg_isMulCommutative : IsMulCommutative (Rg F) :=
  ⟨⟨fun a b => by
    obtain ⟨x, hx⟩ := mem_Rg.1 a.2
    obtain ⟨y, hy⟩ := mem_Rg.1 b.2
    apply Subtype.ext
    show (a : SL(2, F)) * b = b * a
    rw [← hx, ← hy, ← e12_add, ← e12_add, add_comm]⟩⟩

theorem commutator_eq_zpowers_c3 [Finite F] (hF : Nat.card F = 2) :
    commutator SL(2, F) = Subgroup.zpowers (c3 F) := by
  have hN : (Subgroup.zpowers (c3 F)).Normal := Subgroup.normal_of_index_eq_two (index_zpowers_c3 hF)
  have := Rg_isMulCommutative (F := F)
  apply le_antisymm
  · exact Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top (zpowers_c3_sup_Rg hF)
      inferInstance
  · rw [Subgroup.zpowers_le]
    have h1 := Subgroup.commutator_mem_commutator (H₁ := ⊤) (H₂ := ⊤) (Subgroup.mem_top (e12 (1 : F)))
      (Subgroup.mem_top (e21 (1 : F)))
    have h2 : c3 F ^ 2 ∈ commutator SL(2, F) := by
      have e : ⁅e12 (1 : F), e21 (1 : F)⁆ = c3 F ^ 2 := by
        rw [commutatorElement_def, inv_eq_of_mul_eq_one_right (e12_mul_self (1 : F)),
          inv_eq_of_mul_eq_one_right (e21_mul_self (1 : F)), c3, pow_two]
        group
      rw [← e]
      exact h1
    have h3 : c3 F = (c3 F ^ 2) ^ 2 := by
      rw [← pow_mul]
      have := c3_pow_three (F := F)
      calc c3 F = c3 F ^ 3 * c3 F := by rw [this, one_mul]
        _ = c3 F ^ (2 * 2) := by rw [← pow_succ]
    rw [h3]
    exact Subgroup.pow_mem _ h2 2


theorem c3_smul (w : Fin 2 → F) : c3 F • w = ![w 1, w 0 + w 1] := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have h11 : (1 : F) + 1 = 0 := by linear_combination h2
  rw [smul_eq_mulVec']
  ext i
  fin_cases i <;> simp [c3_coe, Matrix.mulVec, dotProduct, Fin.sum_univ_two, h11]

theorem natAct_irreducible_two [Finite F] (hF : Nat.card F = 2) (X : Subgroup (Wm F))
    (hX : ∀ A ∈ commutator SL(2, F), ∀ x ∈ X, natAct A x ∈ X) : X = ⊥ ∨ X = ⊤ := by
  have hc3 : ∀ x ∈ X, natAct (c3 F) x ∈ X := fun x hx =>
    hX _ (by rw [commutator_eq_zpowers_c3 hF]; exact Subgroup.mem_zpowers _) x hx
  have hstep : ∀ u v : F, Multiplicative.ofAdd ![u, v] ∈ X →
      Multiplicative.ofAdd ![v, u + v] ∈ X := fun u v h => by
    have := hc3 _ h
    rwa [natAct_apply, toAdd_ofAdd, c3_smul] at this
  by_cases hbot : X = ⊥
  · exact Or.inl hbot
  refine Or.inr (eq_top_iff.2 fun v _ => ?_)
  obtain ⟨⟨x, hxX⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hbot
  have hxx : x = Multiplicative.ofAdd ![Multiplicative.toAdd x 0, Multiplicative.toAdd x 1] := by
    apply Multiplicative.toAdd.injective
    ext i
    fin_cases i <;> simp
  have h01 : (0 : F) + 1 = 1 := zero_add 1
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have h11 : (1 : F) + 1 = 0 := by linear_combination h2
  have he0 : Multiplicative.ofAdd ![(1 : F), 0] ∈ X ∧ Multiplicative.ofAdd ![(0 : F), 1] ∈ X := by
    rcases eq_zero_or_one_of_card_two hF (Multiplicative.toAdd x 0) with h0 | h0 <;>
      rcases eq_zero_or_one_of_card_two hF (Multiplicative.toAdd x 1) with h1 | h1
    · exfalso
      have hx1' : x = 1 := by
        rw [hxx, h0, h1]
        apply Multiplicative.toAdd.injective
        ext i
        fin_cases i <;> simp
      exact hx1 (Subtype.ext hx1')
    · rw [hxx, h0, h1] at hxX
      have h' := hstep _ _ hxX
      simp only [zero_add] at h'
      have h'' := hstep _ _ h'
      simp only [h11] at h''
      exact ⟨h'', hxX⟩
    · rw [hxx, h0, h1] at hxX
      exact ⟨hxX, by
        have h' := hstep _ _ hxX
        simpa using h'⟩
    · rw [hxx, h0, h1] at hxX
      have h' := hstep _ _ hxX
      simp only [h11] at h'
      have h'' := hstep _ _ h'
      simp only [add_zero] at h''
      exact ⟨h', h''⟩
  have hvv : v = Multiplicative.ofAdd ![Multiplicative.toAdd v 0, Multiplicative.toAdd v 1] := by
    apply Multiplicative.toAdd.injective
    ext i
    fin_cases i <;> simp
  have hprod : ∀ u w : F, Multiplicative.ofAdd ![u, w] =
      Multiplicative.ofAdd ![u, 0] * Multiplicative.ofAdd ![0, w] := fun u w => by
    apply Multiplicative.toAdd.injective
    ext i
    fin_cases i <;> simp
  have h1' : (1 : F) ≠ 0 := one_ne_zero
  rw [hvv, hprod]
  refine X.mul_mem ?_ ?_
  · rcases eq_zero_or_one_of_card_two hF (Multiplicative.toAdd v 0) with h0 | h0
    · rw [h0]
      have : (Multiplicative.ofAdd ![(0 : F), 0] : Wm F) = 1 := by
        apply Multiplicative.toAdd.injective
        ext i
        fin_cases i <;> simp
      rw [this]
      exact X.one_mem
    · rw [h0]
      exact he0.1
  · rcases eq_zero_or_one_of_card_two hF (Multiplicative.toAdd v 1) with h0 | h0
    · rw [h0]
      have : (Multiplicative.ofAdd ![(0 : F), 0] : Wm F) = 1 := by
        apply Multiplicative.toAdd.injective
        ext i
        fin_cases i <;> simp
      rw [this]
      exact X.one_mem
    · rw [h0]
      exact he0.2

omit [CharP F 2] in
theorem normalizing_lemma_two [Finite F] (hF : Nat.card F = 2) (ρ : MulAut (Wm F))
    (ha : ∀ w : Wm F, Multiplicative.toAdd (ρ w) 1 = Multiplicative.toAdd w 1) :
    ∃ b : F, ∀ w : Wm F, ρ w = natAct (e12 b) w := by
  have hf1 : fcoord ρ 1 = 1 := by
    rcases eq_zero_or_one_of_card_two hF (fcoord ρ 1) with h | h
    · exfalso
      exact one_ne_zero (fcoord_injective ρ ha (h.trans (fcoord_zero ρ).symm))
    · exact h
  have hfx : ∀ x, fcoord ρ x = x := fun x => by
    rcases eq_zero_or_one_of_card_two hF x with rfl | rfl
    · exact fcoord_zero ρ
    · exact hf1
  have hgy : ∀ y, gcoord ρ y = gcoord ρ 1 * y := fun y => by
    rcases eq_zero_or_one_of_card_two hF y with rfl | rfl
    · rw [gcoord_zero, mul_zero]
    · rw [mul_one]
  refine ⟨gcoord ρ 1, fun w => ?_⟩
  have hw : w = Multiplicative.ofAdd ![Multiplicative.toAdd w 0, Multiplicative.toAdd w 1] := by
    apply Multiplicative.toAdd.injective
    ext i
    fin_cases i <;> simp
  apply Multiplicative.toAdd.injective
  rw [hw, natAct_apply, toAdd_ofAdd, e12_smul, normalizing_aux ρ ha, hfx, hgy]
  simp

end Two


section Lines

abbrev e0 (F : Type*) [Field F] : Fin 2 → F := Pi.single 0 1

theorem smul_e0 (A : SL(2, F)) : A • e0 F = ![A.1 0 0, A.1 1 0] := by
  rw [smul_eq_mulVec']
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem stab_iff (A : SL(2, F)) : A.1 1 0 = 0 ↔ ∃ c : F, A • e0 F = c • e0 F := by
  constructor
  · intro h
    refine ⟨A.1 0 0, ?_⟩
    rw [smul_e0]
    ext i
    fin_cases i <;> simp [h]
  · rintro ⟨c, hc⟩
    have := congrFun hc 1
    rw [smul_e0] at this
    simpa [Pi.single_apply] using this

theorem e12_smul_e0 (b : F) : e12 b • e0 F = e0 F := by
  rw [smul_e0]
  ext i
  fin_cases i <;> simp

theorem dgm_smul_e0 (d : Fˣ) : dgm d • e0 F = (d : F) • e0 F := by
  rw [smul_e0]
  ext i
  fin_cases i <;> simp

theorem TI_line (B : SL(2, F)) (hB : B.1 1 0 ≠ 0) (c c' : F)
    (h : c • e0 F = c' • (B • e0 F)) : c • e0 F = 0 := by
  have h1 := congrFun h 1
  rw [smul_e0] at h1
  simp at h1
  rcases h1 with h1 | h1
  · rw [h1] at h
    simpa using h
  · exact absurd h1 hB

end Lines


section Extra

theorem natAct_injective : Function.Injective (natAct : SL(2, F) →* MulAut (Wm F)) := by
  intro A B h
  apply Subtype.ext
  ext i j
  have h1 := congrArg (fun ρ : MulAut (Wm F) => Multiplicative.toAdd (ρ (Multiplicative.ofAdd (Pi.single j 1)))) h
  have h2 := congrFun h1 i
  simp only [natAct_apply, toAdd_ofAdd, smul_eq_mulVec'] at h2
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h2

variable [Finite F] [CharP F 2]

theorem card_two_or_exists_sq_ne_one : Nat.card F = 2 ∨ ∃ a : F, a ≠ 0 ∧ a ^ 2 ≠ 1 := by
  by_cases h : ∀ a : F, a ≠ 0 → a ^ 2 = 1
  · left
    have hF : ∀ a : F, a = 0 ∨ a = 1 := fun a => by
      by_cases ha : a = 0
      · exact Or.inl ha
      · right
        have h1 : (a - 1) ^ 2 = 0 := by
          have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
          linear_combination h a ha + (1 - a) * h2
        exact sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 h1)
    classical
    have : Fintype F := Fintype.ofFinite F
    have hle : Fintype.card F ≤ 2 := by
      have : (Finset.univ : Finset F) ⊆ {0, 1} := fun a _ => by
        rcases hF a with h | h <;> simp [h]
      exact (Finset.card_le_card this).trans (Finset.card_le_two)
    have hge : 1 < Fintype.card F := Fintype.one_lt_card
    rw [Nat.card_eq_fintype_card]
    omega
  · right
    push Not at h
    exact h

theorem natAct_irreducible_comm (X : Subgroup (Wm F))
    (hX : ∀ A ∈ commutator SL(2, F), ∀ x ∈ X, natAct A x ∈ X) : X = ⊥ ∨ X = ⊤ := by
  rcases card_two_or_exists_sq_ne_one (F := F) with h2 | ⟨a, ha0, ha1⟩
  · exact natAct_irreducible_two h2 X hX
  · have hc : commutator SL(2, F) = ⊤ := SL2.commutator_eq_top ha0 ha1
    exact natAct_irreducible X fun A x hx => hX A (hc ▸ Subgroup.mem_top A) x hx

theorem commutator_sup_Rg : commutator SL(2, F) ⊔ Rg F = ⊤ := by
  rcases card_two_or_exists_sq_ne_one (F := F) with h2 | ⟨a, ha0, ha1⟩
  · rw [commutator_eq_zpowers_c3 h2]
    exact zpowers_c3_sup_Rg h2
  · rw [SL2.commutator_eq_top ha0 ha1]
    exact top_sup_eq _

omit [Finite F] [CharP F 2] in
theorem inv_lower_left (A : SL(2, F)) : (A⁻¹).1 1 0 = -A.1 1 0 := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  simp

end Extra

end CFSG.Quasithin.SL2Model
