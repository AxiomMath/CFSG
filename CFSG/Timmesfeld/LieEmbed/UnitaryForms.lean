module

public import CFSG.LieType.Universal.Unitary.Basic
public import CFSG.Timmesfeld.ARS.Defs
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Timmesfeld.LieEmbed

open Matrix CFSG.LieType.Universal.Unitary
open scoped commutatorElement

variable {F : Type*} [Field F] (σ : F ≃+* F) {n : ℕ}

@[expose] def uForm (x y : Fin n → F) : F := (fun i => σ (x i)) ⬝ᵥ (antidiag n *ᵥ y)

@[expose] def uRow (v : Fin n → F) : Fin n → F := (fun i => σ (v i)) ᵥ* antidiag n

@[expose] def uNil (v : Fin n → F) : Matrix (Fin n) (Fin n) F := vecMulVec v (uRow σ v)

@[expose] def uTrans (v : Fin n → F) (c : F) : Matrix (Fin n) (Fin n) F := 1 + c • uNil σ v

theorem antidiag_mulVec (y : Fin n → F) (i : Fin n) : (antidiag n *ᵥ y) i = y (Fin.rev i) := by
  simp [antidiag, mulVec, dotProduct, Matrix.of_apply]

theorem vecMul_antidiag (y : Fin n → F) (i : Fin n) : (y ᵥ* antidiag n) i = y (Fin.rev i) := by
  simp only [vecMul, dotProduct, antidiag, Matrix.of_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (Fin.rev i)]
  · simp
  · intro b _ hb
    simp [show ¬i = Fin.rev b from fun h => hb (by rw [h, Fin.rev_rev])]
  · simp

theorem uForm_eq (x y : Fin n → F) : uForm σ x y = ∑ i, σ (x i) * y (Fin.rev i) := by
  simp only [uForm, dotProduct, antidiag_mulVec]

theorem uRow_apply (v : Fin n → F) (i : Fin n) : uRow σ v i = σ (v (Fin.rev i)) := by
  rw [uRow, vecMul_antidiag]

theorem uRow_dotProduct (v w : Fin n → F) : uRow σ v ⬝ᵥ w = uForm σ v w := by
  rw [uRow, ← dotProduct_mulVec, uForm]

theorem uForm_conj (hσ : ∀ c, σ (σ c) = c) (x y : Fin n → F) :
    σ (uForm σ x y) = uForm σ y x := by
  rw [uForm_eq, uForm_eq, map_sum]
  refine Fintype.sum_equiv Fin.revPerm _ _ fun i => ?_
  simp only [map_mul, hσ, Fin.revPerm_apply, Fin.rev_rev]
  ring

theorem uForm_smul_left (l : F) (x y : Fin n → F) : uForm σ (l • x) y = σ l * uForm σ x y := by
  simp only [uForm_eq, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

theorem uForm_smul_right (l : F) (x y : Fin n → F) : uForm σ x (l • y) = l * uForm σ x y := by
  simp only [uForm_eq, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem uRow_smul (l : F) (v : Fin n → F) : uRow σ (l • v) = σ l • uRow σ v := by
  funext i
  simp [uRow_apply, map_mul]

theorem uNil_mul_uNil (v w : Fin n → F) :
    uNil σ v * uNil σ w = uForm σ v w • vecMulVec v (uRow σ w) := by
  rw [uNil, uNil, vecMulVec_mul_vecMulVec, uRow_dotProduct]
  ext a b
  simp [vecMulVec_apply, mul_left_comm]

theorem uTrans_mul_uTrans {v : Fin n → F} (hv : uForm σ v v = 0) (a b : F) :
    uTrans σ v a * uTrans σ v b = uTrans σ v (a + b) := by
  simp only [uTrans, add_mul, mul_add, one_mul, mul_one, smul_mul_smul, uNil_mul_uNil, hv,
    zero_smul, smul_zero, add_zero, add_smul]
  abel

theorem uTrans_zero (v : Fin n → F) : uTrans σ v 0 = 1 := by
  simp [uTrans]

theorem uTrans_commute_of_uForm_eq_zero (hσ : ∀ c, σ (σ c) = c) {v w : Fin n → F}
    (h : uForm σ v w = 0) (a b : F) :
    uTrans σ v a * uTrans σ w b = uTrans σ w b * uTrans σ v a := by
  have h' : uForm σ w v = 0 := by rw [← uForm_conj σ hσ, h, map_zero]
  simp only [uTrans, add_mul, mul_add, one_mul, mul_one, smul_mul_smul, uNil_mul_uNil, h, h',
    zero_smul, smul_zero, add_zero]
  abel

theorem uRow_ne_zero {v : Fin n → F} (hv : v ≠ 0) : uRow σ v ≠ 0 := by
  intro h
  apply hv
  funext i
  have := congrFun h (Fin.rev i)
  rw [uRow_apply, Fin.rev_rev, Pi.zero_apply, map_eq_zero] at this
  exact this

theorem uForm_eq_zero_of_commute (hσ : ∀ c, σ (σ c) = c) {v w : Fin n → F} (hv : v ≠ 0)
    {a b : F} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : uTrans σ v a * uTrans σ w b = uTrans σ w b * uTrans σ v a) :
    uForm σ v w = 0 ∨ ∃ l : F, w = l • v := by
  by_contra hc
  push Not at hc
  obtain ⟨hB, hprop⟩ := hc
  have hN : uNil σ v * uNil σ w = uNil σ w * uNil σ v := by
    simp only [uTrans, add_mul, mul_add, one_mul, mul_one, smul_mul_smul] at h
    have h' := congrArg (fun M => M - 1 - a • uNil σ v - b • uNil σ w) h
    have h'' : (a * b) • (uNil σ v * uNil σ w) = (b * a) • (uNil σ w * uNil σ v) := by
      convert h' using 1 <;> abel
    rw [mul_comm b a] at h''
    exact smul_right_injective _ (mul_ne_zero ha hb) h''
  rw [uNil_mul_uNil, uNil_mul_uNil, ← uForm_conj σ hσ v w] at hN
  have hvJ := uRow_ne_zero σ hv
  obtain ⟨e, he⟩ := Function.ne_iff.1 hvJ
  have he' : uRow σ v e ≠ 0 := by simpa using he
  have hB' : σ (uForm σ v w) ≠ 0 := by rwa [map_ne_zero]
  refine hprop (uForm σ v w * uRow σ w e / (σ (uForm σ v w) * uRow σ v e)) ?_
  ext x
  have hxe := congrFun (congrFun hN x) e
  simp only [Matrix.smul_apply, vecMulVec_apply, smul_eq_mul] at hxe
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [div_mul_eq_mul_div, eq_div_iff (mul_ne_zero hB' he')]
  linear_combination -hxe

variable (n) in
@[expose] def suMat : SU σ n →* Matrix (Fin n) (Fin n) F :=
  (Units.coeHom _).comp (SU σ n).subtype

theorem suMat_apply (g : SU σ n) :
    suMat σ n g = ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := rfl

theorem suMat_injective : Function.Injective (suMat σ n) := fun _ _ h =>
  Subtype.ext (Units.ext h)

theorem suMat_isometry (g : SU σ n) :
    conjTr σ (suMat σ n g) * antidiag n * suMat σ n g = antidiag n :=
  (mem_SU.1 g.2).2

theorem map_mulVec_sigma (M : Matrix (Fin n) (Fin n) F) (v : Fin n → F) :
    (fun i => σ ((M *ᵥ v) i)) = M.map σ *ᵥ fun i => σ (v i) := by
  funext i
  simp [mulVec, dotProduct, map_sum, map_mul]

theorem uRow_mulVec_vecMul (g : SU σ n) (v : Fin n → F) :
    uRow σ (suMat σ n g *ᵥ v) ᵥ* suMat σ n g = uRow σ v := by
  rw [uRow, uRow, map_mulVec_sigma, ← vecMul_transpose, vecMul_vecMul, vecMul_vecMul]
  congr 1
  have h := suMat_isometry σ g
  rw [conjTr, Matrix.mul_assoc] at h
  exact h

theorem uForm_mulVec (g : SU σ n) (x y : Fin n → F) :
    uForm σ (suMat σ n g *ᵥ x) (suMat σ n g *ᵥ y) = uForm σ x y := by
  rw [← uRow_dotProduct, dotProduct_mulVec, uRow_mulVec_vecMul, uRow_dotProduct]

theorem suMat_mul_uNil (g : SU σ n) (v : Fin n → F) :
    suMat σ n g * uNil σ v = uNil σ (suMat σ n g *ᵥ v) * suMat σ n g := by
  rw [uNil, uNil, mul_vecMulVec, vecMulVec_mul, uRow_mulVec_vecMul]

theorem suMat_conj_of_eq {x : SU σ n} {v : Fin n → F} {c : F}
    (hx : suMat σ n x = uTrans σ v c) (g : SU σ n) :
    suMat σ n (g * x * g⁻¹) = uTrans σ (suMat σ n g *ᵥ v) c := by
  have h1 : suMat σ n g * uTrans σ v c = uTrans σ (suMat σ n g *ᵥ v) c * suMat σ n g := by
    rw [uTrans, uTrans, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_smul, Matrix.smul_mul, suMat_mul_uNil]
  rw [map_mul, map_mul, hx, h1, Matrix.mul_assoc, ← map_mul, mul_inv_cancel, map_one,
    Matrix.mul_one]

theorem suMat_mulVec_ne_zero (g : SU σ n) {v : Fin n → F} (hv : v ≠ 0) :
    suMat σ n g *ᵥ v ≠ 0 := by
  intro h
  apply hv
  have h' := congrArg (fun w => suMat σ n g⁻¹ *ᵥ w) h
  simp only [mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, one_mulVec, mulVec_zero] at h'
  exact h'

@[expose] def IsUTransGroup (v : Fin n → F) (X : Subgroup (SU σ n)) : Prop :=
  (∀ x, x ∈ X ↔ ∃ c, c + σ c = 0 ∧ suMat σ n x = uTrans σ v c) ∧
    ∀ c, c + σ c = 0 → ∃ x : SU σ n, suMat σ n x = uTrans σ v c

variable {σ}

theorem IsUTransGroup.eq {v : Fin n → F} {X Y : Subgroup (SU σ n)} (hX : IsUTransGroup σ v X)
    (hY : IsUTransGroup σ v Y) : X = Y := by
  ext x
  rw [hX.1, hY.1]

theorem uNil_smul (l : F) (v : Fin n → F) : uNil σ (l • v) = (l * σ l) • uNil σ v := by
  rw [uNil, uNil, uRow_smul, smul_vecMulVec, vecMulVec_smul, smul_smul]

theorem uTrans_smul (l : F) (v : Fin n → F) (c : F) :
    uTrans σ (l • v) c = uTrans σ v (l * σ l * c) := by
  rw [uTrans, uTrans, uNil_smul, smul_smul, mul_comm c]

theorem traceZero_mul_norm (hσ : ∀ c, σ (σ c) = c) (l : F) {c : F} (hc : c + σ c = 0) :
    l * σ l * c + σ (l * σ l * c) = 0 := by
  rw [map_mul, map_mul, hσ]
  linear_combination l * σ l * hc

theorem IsUTransGroup.of_smul (hσ : ∀ c, σ (σ c) = c) {v : Fin n → F} {l : F} (hl : l ≠ 0)
    {X : Subgroup (SU σ n)} (h : IsUTransGroup σ (l • v) X) : IsUTransGroup σ v X := by
  have hll : l * σ l ≠ 0 := mul_ne_zero hl ((map_ne_zero σ).2 hl)
  have hll' : (l * σ l)⁻¹ * σ (l * σ l)⁻¹ * 1 = (l * σ l)⁻¹ * (l * σ l)⁻¹ := by
    rw [map_inv₀, map_mul, hσ, mul_comm (σ l) l, mul_one]
  have key : ∀ {c : F}, c + σ c = 0 → (l * σ l)⁻¹ * c + σ ((l * σ l)⁻¹ * c) = 0 := fun hc => by
    rw [map_mul, map_inv₀, map_mul, hσ, mul_comm (σ l) l]
    linear_combination (l * σ l)⁻¹ * hc
  refine ⟨fun x => ?_, fun c hc => ?_⟩
  · rw [h.1]
    constructor
    · rintro ⟨c, hc, hx⟩
      exact ⟨l * σ l * c, traceZero_mul_norm hσ l hc, by rw [hx, uTrans_smul]⟩
    · rintro ⟨c, hc, hx⟩
      refine ⟨(l * σ l)⁻¹ * c, key hc, ?_⟩
      rw [hx, uTrans_smul, ← mul_assoc, mul_inv_cancel₀ hll, one_mul]
  · obtain ⟨x, hx⟩ := h.2 ((l * σ l)⁻¹ * c) (key hc)
    exact ⟨x, by rw [hx, uTrans_smul, ← mul_assoc, mul_inv_cancel₀ hll, one_mul]⟩

theorem IsUTransGroup.conjSub {v : Fin n → F} {X : Subgroup (SU σ n)}
    (h : IsUTransGroup σ v X) (g : SU σ n) :
    IsUTransGroup σ (suMat σ n g *ᵥ v) (CFSG.Timmesfeld.ARS.conjSub X g) := by
  refine ⟨fun x => ?_, fun c hc => ?_⟩
  · constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨c, hc, hyc⟩ := (h.1 y).1 hy
      exact ⟨c, hc, suMat_conj_of_eq σ hyc g⟩
    · rintro ⟨c, hc, hxc⟩
      refine ⟨g⁻¹ * x * g, (h.1 _).2 ⟨c, hc, ?_⟩, by simp [mul_assoc]⟩
      have := suMat_conj_of_eq σ hxc g⁻¹
      rwa [show g⁻¹ * x * g⁻¹⁻¹ = g⁻¹ * x * g by group, mulVec_mulVec, ← map_mul,
        inv_mul_cancel, map_one, one_mulVec] at this
  · obtain ⟨x, hx⟩ := h.2 c hc
    exact ⟨g * x * g⁻¹, suMat_conj_of_eq σ hx g⟩

theorem IsUTransGroup.commuting (hσ : ∀ c, σ (σ c) = c) {v w : Fin n → F}
    {X Y : Subgroup (SU σ n)} (hX : IsUTransGroup σ v X) (hY : IsUTransGroup σ w Y)
    (h : uForm σ v w = 0) : CFSG.Timmesfeld.ARS.Commuting X Y := by
  intro x hx y hy
  obtain ⟨a, -, ha⟩ := (hX.1 x).1 hx
  obtain ⟨b, -, hb⟩ := (hY.1 y).1 hy
  apply suMat_injective σ
  rw [map_mul, map_mul, ha, hb, uTrans_commute_of_uForm_eq_zero σ hσ h]

theorem IsUTransGroup.uForm_eq_zero (hσ : ∀ c, σ (σ c) = c) {c₀ : F} (hc₀ : c₀ ≠ 0)
    (hc₀' : c₀ + σ c₀ = 0) {v w : Fin n → F} {X Y : Subgroup (SU σ n)}
    (hX : IsUTransGroup σ v X) (hY : IsUTransGroup σ w Y) (hv : v ≠ 0)
    (hc : CFSG.Timmesfeld.ARS.Commuting X Y) :
    uForm σ v w = 0 ∨ ∃ l : F, w = l • v := by
  obtain ⟨x, hx⟩ := hX.2 c₀ hc₀'
  obtain ⟨y, hy⟩ := hY.2 c₀ hc₀'
  refine uForm_eq_zero_of_commute σ hσ hv hc₀ hc₀ ?_
  have := congrArg (suMat σ n)
    (hc x ((hX.1 x).2 ⟨c₀, hc₀', hx⟩) y ((hY.1 y).2 ⟨c₀, hc₀', hy⟩)).eq
  rwa [map_mul, map_mul, hx, hy] at this

theorem uNil_mulVec (v u : Fin n → F) : uNil σ v *ᵥ u = uForm σ v u • v := by
  funext i
  simp only [uNil, mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
    ← uRow_dotProduct, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem uTrans_mulVec (v u : Fin n → F) (c : F) :
    uTrans σ v c *ᵥ u = u + (c * uForm σ v u) • v := by
  rw [uTrans, add_mulVec, one_mulVec, smul_mulVec, uNil_mulVec, smul_smul]

theorem exists_eq_smul_of_uNil_eq {v w : Fin n → F} {l : F}
    (h : uNil σ v = l • uNil σ w) : ∃ m : F, v = m • w := by
  by_cases hv : v = 0
  · exact ⟨0, by rw [hv, zero_smul]⟩
  obtain ⟨c, hc⟩ := Function.ne_iff.1 (uRow_ne_zero σ hv)
  have hc' : uRow σ v c ≠ 0 := by simpa using hc
  refine ⟨l * uRow σ w c / uRow σ v c, ?_⟩
  funext a
  have h1 := congrFun (congrFun h a) c
  simp only [uNil, vecMulVec_apply, Matrix.smul_apply, smul_eq_mul] at h1
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp
  linear_combination h1

theorem IsUTransGroup.exists_eq_smul {c₀ : F} (hc₀ : c₀ ≠ 0) (hc₀' : c₀ + σ c₀ = 0)
    {u w : Fin n → F} {X : Subgroup (SU σ n)} (hu : IsUTransGroup σ u X)
    (hw : IsUTransGroup σ w X) : ∃ m : F, u = m • w := by
  obtain ⟨x, hx⟩ := hu.2 c₀ hc₀'
  obtain ⟨c, -, hc⟩ := (hw.1 x).1 ((hu.1 x).2 ⟨c₀, hc₀', hx⟩)
  rw [hx, uTrans, uTrans] at hc
  have h := add_left_cancel hc
  refine exists_eq_smul_of_uNil_eq (σ := σ) (l := c₀⁻¹ * c) ?_
  rw [mul_smul, ← h, smul_smul, inv_mul_cancel₀ hc₀, one_smul]

theorem uForm_add_right (v x y : Fin n → F) :
    uForm σ v (x + y) = uForm σ v x + uForm σ v y := by
  rw [uForm, mulVec_add, dotProduct_add, uForm, uForm]

theorem suMat_inv_of_eq {v : Fin n → F} (hv : uForm σ v v = 0) {x : SU σ n} {c : F}
    (hx : suMat σ n x = uTrans σ v c) : suMat σ n x⁻¹ = uTrans σ v (-c) := by
  have h1 : suMat σ n x * uTrans σ v (-c) = 1 := by
    rw [hx, uTrans_mul_uTrans σ hv, add_neg_cancel, uTrans_zero]
  calc suMat σ n x⁻¹ = suMat σ n x⁻¹ * (suMat σ n x * uTrans σ v (-c)) := by rw [h1, mul_one]
    _ = uTrans σ v (-c) := by rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]

theorem IsUTransGroup.uForm_eq_zero_of_center (hσ : ∀ c, σ (σ c) = c) {c₀ : F} (hc₀ : c₀ ≠ 0)
    (hc₀' : c₀ + σ c₀ = 0) {v w : Fin n → F} {X Y : Subgroup (SU σ n)}
    (hX : IsUTransGroup σ v X) (hY : IsUTransGroup σ w Y) (hv : v ≠ 0)
    (hvv : uForm σ v v = 0) (hww : uForm σ w w = 0)
    (hc : ∀ x ∈ X, ∀ y ∈ Y, ⁅x, y⁆ ∈ Subgroup.center (SU σ n)) :
    uForm σ v w = 0 ∨ ∃ l : F, w = l • v := by
  obtain ⟨x, hx⟩ := hX.2 c₀ hc₀'
  obtain ⟨y, hy⟩ := hY.2 c₀ hc₀'
  have hz := hc x ((hX.1 x).2 ⟨c₀, hc₀', hx⟩) y ((hY.1 y).2 ⟨c₀, hc₀', hy⟩)
  set z := ⁅x, y⁆ with hzdef
  have hYz : CFSG.Timmesfeld.ARS.conjSub Y z = Y := by
    ext g
    constructor
    · rintro ⟨g', hg', rfl⟩
      show z * g' * z⁻¹ ∈ Y
      rw [(Subgroup.mem_center_iff.1 hz g').symm, mul_inv_cancel_right]
      exact hg'
    · intro hg
      refine ⟨g, hg, ?_⟩
      show z * g * z⁻¹ = g
      rw [(Subgroup.mem_center_iff.1 hz g).symm, mul_inv_cancel_right]
  have hYz' := hY.conjSub z
  rw [hYz] at hYz'
  obtain ⟨m, hm⟩ := hYz'.exists_eq_smul hc₀ hc₀' hY
  set h := uForm σ v w with hhdef
  have hwv : uForm σ w v = σ h := by rw [hhdef, uForm_conj σ hσ]
  have s1 : uTrans σ w (-c₀) *ᵥ w = w := by rw [uTrans_mulVec, hww, mul_zero, zero_smul, add_zero]
  have s2 : uTrans σ v (-c₀) *ᵥ w = w + (-c₀ * h) • v := by rw [uTrans_mulVec]
  have s3 : uTrans σ w c₀ *ᵥ (w + (-c₀ * h) • v) =
      w + (-c₀ * h) • v + (c₀ * (-c₀ * h * σ h)) • w := by
    rw [uTrans_mulVec, uForm_add_right, uForm_smul_right, hww, hwv, zero_add]
  have s4 : uTrans σ v c₀ *ᵥ (w + (-c₀ * h) • v + (c₀ * (-c₀ * h * σ h)) • w) =
      w + (-c₀ * h) • v + (c₀ * (-c₀ * h * σ h)) • w +
        (c₀ * (h + (-c₀ * h) * 0 + c₀ * (-c₀ * h * σ h) * h)) • v := by
    rw [uTrans_mulVec, uForm_add_right, uForm_add_right, uForm_smul_right, uForm_smul_right, hvv]
  have hzw : suMat σ n z *ᵥ w = ((1 : F) - c₀ * c₀ * (h * σ h)) • w +
      (-(c₀ * c₀ * c₀ * (h * σ h) * h)) • v := by
    rw [hzdef, commutatorElement_def, map_mul, map_mul, map_mul, hx, hy,
      suMat_inv_of_eq hvv hx, suMat_inv_of_eq hww hy, ← mulVec_mulVec, ← mulVec_mulVec,
      ← mulVec_mulVec, s1, s2, s3, s4]
    funext a
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hzw] at hm
  by_cases hα : c₀ * c₀ * c₀ * (h * σ h) * h = 0
  · left
    rcases mul_eq_zero.1 hα with h1 | h1
    · rcases mul_eq_zero.1 h1 with h2 | h2
      · exact absurd h2 (by simp [hc₀])
      · rcases mul_eq_zero.1 h2 with h3 | h3
        · exact h3
        · exact (map_eq_zero σ).1 h3
    · exact h1
  · right
    have hvw : v =
        ((c₀ * c₀ * c₀ * (h * σ h) * h)⁻¹ * ((1 : F) - c₀ * c₀ * (h * σ h) - m)) • w := by
      funext a
      have := congrFun hm a
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
      rw [mul_assoc, eq_inv_mul_iff_mul_eq₀ hα]
      linear_combination -this
    by_cases hβ : (1 : F) - c₀ * c₀ * (h * σ h) - m = 0
    · exfalso
      apply hv
      rw [hvw, hβ, mul_zero, zero_smul]
    · refine ⟨((c₀ * c₀ * c₀ * (h * σ h) * h)⁻¹ * ((1 : F) - c₀ * c₀ * (h * σ h) - m))⁻¹, ?_⟩
      rw [hvw, smul_smul, inv_mul_cancel₀ (mul_ne_zero (inv_ne_zero hα) hβ), one_smul]

end CFSG.Timmesfeld.LieEmbed
