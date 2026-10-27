module

public import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalCoord
public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField

import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryNorm
import CFSG.ClassicalGroups.PCoreSection
import CFSG.Quasithin.Recognition.St84.Gen.AmalVertexLocal

public section

namespace CFSG.Quasithin.F112R.St84

open Matrix CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalGroups.PCoreSection
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {f : ℕ}

theorem U4qCoordLeft.commutator {F : Type*} [Field F] (c₁ : U4qCoordLeft L1 L2 S f F)
    {c : ↥L1} {t : F} (hc : (c₁.α c : Matrix (Fin 2) (Fin 2) F) = !![1, t; 0, 1])
    (a w : ↥(pCoreOf 2 L1)) (hw : (w : G) = c * a * c⁻¹ * a⁻¹) :
    Multiplicative.toAdd (c₁.β w) 0 = t • Multiplicative.toAdd (c₁.β a) 1 ∧
      Multiplicative.toAdd (c₁.β w) 1 = 0 := by
  let v : ↥(pCoreOf 2 L1) := ⟨c * a * c⁻¹, conj_mem_pCoreOf c.2 a.2⟩
  have hwv : w = v * a⁻¹ := Subtype.ext hw
  have hv := c₁.equivariant c a v rfl
  rw [hc] at hv
  have h0 := unitriangular_mul_row_zero t (Multiplicative.toAdd (c₁.β a))
  have h1 := unitriangular_mul_row_one t (Multiplicative.toAdd (c₁.β a))
  rw [hwv, map_mul, map_inv, toAdd_mul, toAdd_inv, hv]
  refine ⟨?_, ?_⟩
  · funext j
    have hj := congrFun h0 j
    simp only [Pi.add_apply, Pi.smul_apply] at hj
    rw [Matrix.add_apply, Matrix.neg_apply, hj, Pi.smul_apply]
    ring
  · funext j
    have hj := congrFun h1 j
    rw [Matrix.add_apply, Matrix.neg_apply, hj, Pi.zero_apply, add_neg_cancel]

theorem U4qCoordRight.commutator {K : Type*} [Field K] (c₂ : U4qCoordRight L1 L2 S f K)
    {a : ↥L2} {s : K} (ha : (c₂.α a : Matrix (Fin 2) (Fin 2) K) = !![1, s; 0, 1])
    (c w : ↥(pCoreOf 2 L2)) (hw : (w : G) = a * c * a⁻¹ * c⁻¹) :
    Multiplicative.toAdd (c₂.β w) 0 1 = s * Multiplicative.toAdd (c₂.β c) 1 1 := by
  let v : ↥(pCoreOf 2 L2) := ⟨a * c * a⁻¹, conj_mem_pCoreOf a.2 c.2⟩
  have hwv : w = v * c⁻¹ := Subtype.ext hw
  have hv := c₂.equivariant a c v rfl
  rw [ha, unitriangular_mul_mul_map_transpose] at hv
  rw [hwv, map_mul, map_inv, toAdd_mul, toAdd_inv, Matrix.add_apply, Matrix.neg_apply, hv]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
  ring

section Total

variable {F K : Type} [Field F] [Field K]

open scoped Classical in
private noncomputable def bL (c₁ : U4qCoordLeft L1 L2 S f F) (x : G) :
    Matrix (Fin 2) (Fin 2) F :=
  if h : x ∈ pCoreOf 2 L1 then Multiplicative.toAdd (c₁.β ⟨x, h⟩) else 0

open scoped Classical in
private noncomputable def bR (c₂ : U4qCoordRight L1 L2 S f K) (x : G) :
    Matrix (Fin 2) (Fin 2) K :=
  if h : x ∈ pCoreOf 2 L2 then Multiplicative.toAdd (c₂.β ⟨x, h⟩) else 0

open scoped Classical in
private noncomputable def pL (c₁ : U4qCoordLeft L1 L2 S f F) (x : G) : F :=
  if h : x ∈ L1 then (c₁.α ⟨x, h⟩ : Matrix (Fin 2) (Fin 2) F) 0 1 else 0

open scoped Classical in
private noncomputable def pR (c₂ : U4qCoordRight L1 L2 S f K) (x : G) : K :=
  if h : x ∈ L2 then (c₂.α ⟨x, h⟩ : Matrix (Fin 2) (Fin 2) K) 0 1 else 0

variable (c₁ : U4qCoordLeft L1 L2 S f F) (c₂ : U4qCoordRight L1 L2 S f K)

private theorem bL_of_mem {x : G} (h : x ∈ pCoreOf 2 L1) :
    bL c₁ x = Multiplicative.toAdd (c₁.β ⟨x, h⟩) := by
  rw [bL, dif_pos h]

private theorem bR_of_mem {x : G} (h : x ∈ pCoreOf 2 L2) :
    bR c₂ x = Multiplicative.toAdd (c₂.β ⟨x, h⟩) := by
  rw [bR, dif_pos h]

private theorem pL_of_mem {x : G} (h : x ∈ L1) :
    pL c₁ x = (c₁.α ⟨x, h⟩ : Matrix (Fin 2) (Fin 2) F) 0 1 := by
  rw [pL, dif_pos h]

private theorem pR_of_mem {x : G} (h : x ∈ L2) :
    pR c₂ x = (c₂.α ⟨x, h⟩ : Matrix (Fin 2) (Fin 2) K) 0 1 := by
  rw [pR, dif_pos h]

private theorem bL_mul {x y : G} (hx : x ∈ pCoreOf 2 L1) (hy : y ∈ pCoreOf 2 L1) :
    bL c₁ (x * y) = bL c₁ x + bL c₁ y := by
  rw [bL_of_mem c₁ (mul_mem hx hy), bL_of_mem c₁ hx, bL_of_mem c₁ hy, ← toAdd_mul, ← map_mul]
  rfl

private theorem bL_inv {x : G} (hx : x ∈ pCoreOf 2 L1) : bL c₁ x⁻¹ = -bL c₁ x := by
  rw [bL_of_mem c₁ (inv_mem hx), bL_of_mem c₁ hx, ← toAdd_inv, ← map_inv]
  rfl

private theorem bR_mul {x y : G} (hx : x ∈ pCoreOf 2 L2) (hy : y ∈ pCoreOf 2 L2) :
    bR c₂ (x * y) = bR c₂ x + bR c₂ y := by
  rw [bR_of_mem c₂ (mul_mem hx hy), bR_of_mem c₂ hx, bR_of_mem c₂ hy, ← toAdd_mul, ← map_mul]
  rfl

private theorem bR_inv {x : G} (hx : x ∈ pCoreOf 2 L2) : bR c₂ x⁻¹ = -bR c₂ x := by
  rw [bR_of_mem c₂ (inv_mem hx), bR_of_mem c₂ hx, ← toAdd_inv, ← map_inv]
  rfl

private theorem bL_eq_zero_iff {x : G} (hx : x ∈ pCoreOf 2 L1) :
    bL c₁ x = 0 ↔ x ∈ centerOf (pCoreOf 2 L1) := by
  rw [bL_of_mem c₁ hx]
  have hk : (⟨x, hx⟩ : ↥(pCoreOf 2 L1)) ∈ c₁.β.ker ↔ x ∈ centerOf (pCoreOf 2 L1) := by
    rw [c₁.ker_β, Subgroup.mem_subgroupOf]
  rw [← hk, MonoidHom.mem_ker]
  constructor
  · intro h0
    exact Multiplicative.toAdd.injective (by rw [h0, toAdd_one])
  · intro h1
    rw [h1, toAdd_one]

private theorem bL_one_eq_zero_iff {x : G} (hx : x ∈ pCoreOf 2 L1) :
    bL c₁ x 1 = 0 ↔ x ∈ pCoreOf 2 L2 := by
  rw [bL_of_mem c₁ hx]
  exact (c₁.mem_inf_iff ⟨x, hx⟩).symm

private theorem bL_surj (M : Matrix (Fin 2) (Fin 2) F) :
    ∃ x, x ∈ pCoreOf 2 L1 ∧ bL c₁ x = M := by
  obtain ⟨u, hu⟩ := c₁.surjective_β (Multiplicative.ofAdd M)
  exact ⟨u, u.2, by rw [bL_of_mem c₁ u.2, hu, toAdd_ofAdd]⟩

private theorem bR_herm {x : G} (hx : x ∈ pCoreOf 2 L2) :
    (bR c₂ x).map (· ^ 2 ^ f) = (bR c₂ x).transpose := by
  rw [bR_of_mem c₂ hx]
  exact (c₂.range_iff _).mp ⟨_, rfl⟩

private theorem bR_center_iff {x : G} (hx : x ∈ pCoreOf 2 L2) :
    bR c₂ x 0 1 = 0 ∧ bR c₂ x 1 1 = 0 ↔ x ∈ centerOf (pCoreOf 2 L1) := by
  rw [bR_of_mem c₂ hx]
  exact (c₂.mem_center_iff ⟨x, hx⟩).symm

private theorem bR_one_one_eq_zero_iff {x : G} (hx : x ∈ pCoreOf 2 L2) :
    bR c₂ x 1 1 = 0 ↔ x ∈ pCoreOf 2 L1 := by
  rw [bR_of_mem c₂ hx]
  exact (c₂.mem_inf_iff ⟨x, hx⟩).symm

private theorem alpha_eq_pL {x : G} (hx : x ∈ L1) (hxS : x ∈ S) :
    (c₁.α ⟨x, hx⟩ : Matrix (Fin 2) (Fin 2) F) = !![1, pL c₁ x; 0, 1] := by
  obtain ⟨t, ht⟩ := (c₁.mem_iff ⟨x, hx⟩).mp hxS
  rw [pL_of_mem c₁ hx, ht]
  simp

private theorem alpha_eq_pR {x : G} (hx : x ∈ L2) (hxS : x ∈ S) :
    (c₂.α ⟨x, hx⟩ : Matrix (Fin 2) (Fin 2) K) = !![1, pR c₂ x; 0, 1] := by
  obtain ⟨t, ht⟩ := (c₂.mem_iff ⟨x, hx⟩).mp hxS
  rw [pR_of_mem c₂ hx, ht]
  simp

private theorem pL_mul {x y : G} (hx : x ∈ L1) (hy : y ∈ L1) (hxS : x ∈ S) (hyS : y ∈ S) :
    pL c₁ (x * y) = pL c₁ x + pL c₁ y := by
  rw [pL_of_mem c₁ (mul_mem hx hy)]
  change (c₁.α (⟨x, hx⟩ * ⟨y, hy⟩) : Matrix (Fin 2) (Fin 2) F) 0 1 = _
  rw [map_mul, Matrix.SpecialLinearGroup.coe_mul, alpha_eq_pL c₁ hx hxS, alpha_eq_pL c₁ hy hyS]
  simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

private theorem pR_mul {x y : G} (hx : x ∈ L2) (hy : y ∈ L2) (hxS : x ∈ S) (hyS : y ∈ S) :
    pR c₂ (x * y) = pR c₂ x + pR c₂ y := by
  rw [pR_of_mem c₂ (mul_mem hx hy)]
  change (c₂.α (⟨x, hx⟩ * ⟨y, hy⟩) : Matrix (Fin 2) (Fin 2) K) 0 1 = _
  rw [map_mul, Matrix.SpecialLinearGroup.coe_mul, alpha_eq_pR c₂ hx hxS, alpha_eq_pR c₂ hy hyS]
  simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

private theorem pL_eq_zero_iff {x : G} (hx : x ∈ L1) (hxS : x ∈ S) :
    pL c₁ x = 0 ↔ x ∈ pCoreOf 2 L1 := by
  rw [← c₁.eq_one_iff ⟨x, hx⟩]
  constructor
  · intro h0
    apply Subtype.ext
    rw [alpha_eq_pL c₁ hx hxS, h0, Matrix.SpecialLinearGroup.coe_one, Matrix.one_fin_two]
  · intro h1
    rw [pL_of_mem c₁ hx, h1]
    simp

private theorem pR_eq_zero_iff {x : G} (hx : x ∈ L2) (hxS : x ∈ S) :
    pR c₂ x = 0 ↔ x ∈ pCoreOf 2 L2 := by
  rw [← c₂.eq_one_iff ⟨x, hx⟩]
  constructor
  · intro h0
    apply Subtype.ext
    rw [alpha_eq_pR c₂ hx hxS, h0, Matrix.SpecialLinearGroup.coe_one, Matrix.one_fin_two]
  · intro h1
    rw [pR_of_mem c₂ hx, h1]
    simp

private theorem bL_inv_mul_apply {x y : G} (hx : x ∈ pCoreOf 2 L1) (hy : y ∈ pCoreOf 2 L1)
    (i j : Fin 2) : bL c₁ (y⁻¹ * x) i j = bL c₁ x i j - bL c₁ y i j := by
  rw [bL_mul c₁ (inv_mem hy) hx, bL_inv c₁ hy, Matrix.add_apply, Matrix.neg_apply]
  ring

private theorem bR_inv_mul_apply {x y : G} (hx : x ∈ pCoreOf 2 L2) (hy : y ∈ pCoreOf 2 L2)
    (i j : Fin 2) : bR c₂ (y⁻¹ * x) i j = bR c₂ x i j - bR c₂ y i j := by
  rw [bR_mul c₂ (inv_mem hy) hx, bR_inv c₂ hy, Matrix.add_apply, Matrix.neg_apply]
  ring

private theorem pL_inv_mul {x y : G} (hx : x ∈ L1) (hy : y ∈ L1) (hxS : x ∈ S) (hyS : y ∈ S) :
    pL c₁ (y⁻¹ * x) = pL c₁ x - pL c₁ y := by
  have h1 := pL_mul c₁ (inv_mem hy) hy (inv_mem hyS) hyS
  rw [inv_mul_cancel, pL_of_mem c₁ (one_mem _)] at h1
  have h0 : (c₁.α ⟨1, one_mem _⟩ : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
    rw [show (⟨1, one_mem _⟩ : ↥L1) = 1 from rfl, map_one, Matrix.SpecialLinearGroup.coe_one]
    simp
  rw [pL_mul c₁ (inv_mem hy) hx (inv_mem hyS) hxS]
  linear_combination h0 - h1

private theorem pR_eq_of_inv_mul_mem {x y : G} (hx : x ∈ L2) (hy : y ∈ L2)
    (h : y⁻¹ * x ∈ pCoreOf 2 L2) : pR c₂ x = pR c₂ y := by
  have h1 : c₂.α ⟨y⁻¹ * x, mul_mem (inv_mem hy) hx⟩ = 1 := (c₂.eq_one_iff _).mpr h
  have h2 : c₂.α ⟨x, hx⟩ = c₂.α ⟨y, hy⟩ := by
    have he : (⟨y⁻¹ * x, mul_mem (inv_mem hy) hx⟩ : ↥L2) = (⟨y, hy⟩ : ↥L2)⁻¹ * ⟨x, hx⟩ := rfl
    rw [he, map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1.symm
  rw [pR_of_mem c₂ hx, pR_of_mem c₂ hy, h2]

end Total

section Pairing

variable {F K : Type} [Field F] [Field K]

private theorem pairing (hH : Hyp111 L1 L2 S) (hD : U4qLocalData L1 L2 S f)
    (hS : Nat.card S = 2 ^ (6 * f)) (c₁ : U4qCoordLeft L1 L2 S f F)
    (c₂ : U4qCoordRight L1 L2 S f K) {a c : G} (ha : a ∈ pCoreOf 2 L1)
    (hc : c ∈ pCoreOf 2 L2) :
    c * a * c⁻¹ * a⁻¹ ∈ pCoreOf 2 L1 ⊓ pCoreOf 2 L2 ∧
      bL c₁ (c * a * c⁻¹ * a⁻¹) 0 = pL c₁ c • bL c₁ a 1 ∧
      bR c₂ (c * a * c⁻¹ * a⁻¹) 0 1 = pR c₂ a * bR c₂ c 1 1 := by
  have hcS : c ∈ S := hH.pCoreOf_le_right hc
  have haS : a ∈ S := hH.pCoreOf_le_left ha
  have hcL1 : c ∈ L1 := hD.le_left hH hS hcS
  have haL2 : a ∈ L2 := hD.le_right hH hS haS
  have hw1 : c * a * c⁻¹ * a⁻¹ ∈ pCoreOf 2 L1 := mul_mem (conj_mem_pCoreOf hcL1 ha) (inv_mem ha)
  have hw' : a * c * a⁻¹ * c⁻¹ ∈ pCoreOf 2 L2 := mul_mem (conj_mem_pCoreOf haL2 hc) (inv_mem hc)
  have hww' : c * a * c⁻¹ * a⁻¹ = a * c * a⁻¹ * c⁻¹ := by
    have hsq := hD.isElemAbelian_right.2 _ hw'
    have hinv : (a * c * a⁻¹ * c⁻¹)⁻¹ = a * c * a⁻¹ * c⁻¹ :=
      inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hsq)
    rw [← hinv]
    group
  have hw2 : c * a * c⁻¹ * a⁻¹ ∈ pCoreOf 2 L2 := hww' ▸ hw'
  refine ⟨⟨hw1, hw2⟩, ?_, ?_⟩
  · have h := (c₁.commutator (alpha_eq_pL c₁ hcL1 hcS) ⟨a, ha⟩ ⟨_, hw1⟩ rfl).1
    rw [bL_of_mem c₁ hw1, bL_of_mem c₁ ha]
    exact h
  · have h := c₂.commutator (alpha_eq_pR c₂ haL2 haS) ⟨c, hc⟩ ⟨_, hw'⟩ rfl
    rw [bR_of_mem c₂ hw2, bR_of_mem c₂ hc]
    have he : (⟨c * a * c⁻¹ * a⁻¹, hw2⟩ : ↥(pCoreOf 2 L2)) = ⟨_, hw'⟩ := Subtype.ext hww'
    rw [he]
    exact h

end Pairing

private theorem exists_ringHom_of_pairing {F K V : Type*} [Field F] [Field K] [AddCommGroup V]
    [Module F V] (φA φℓ : V →+ K) (φC : F →+ K) (hA : ∀ v, φA v = 0 → v = 0)
    (hC : ∀ τ, φC τ = 0 → τ = 0) (v₀ : V) (hv₀ : v₀ ≠ 0)
    (h : ∀ (τ : F) (v : V), φℓ (τ • v) = φA v * φC τ) :
    ∃ ρ : F →+* K, (∀ τ, φC τ = φC 1 * ρ τ) ∧ (∀ τ v, φA (τ • v) = ρ τ * φA v) ∧
      (∀ τ v, φℓ (τ • v) = ρ τ * φℓ v) := by
  have hκ : φC 1 ≠ 0 := fun h0 => one_ne_zero (hC 1 h0)
  have hA0 : φA v₀ ≠ 0 := fun h0 => hv₀ (hA v₀ h0)
  have hℓ1 : ∀ v, φℓ v = φA v * φC 1 := fun v => by rw [← h 1 v, one_smul]
  have hAτ : ∀ τ v, φA (τ • v) = φC τ / φC 1 * φA v := by
    intro τ v
    have h1 := hℓ1 (τ • v)
    rw [h τ v] at h1
    rw [div_mul_eq_mul_div, eq_div_iff hκ, ← h1]
    ring
  let ρ : F →+* K :=
    { toFun := fun τ => φC τ / φC 1
      map_one' := div_self hκ
      map_mul' := by
        intro a b
        apply mul_right_cancel₀ hA0
        change φC (a * b) / φC 1 * φA v₀ = φC a / φC 1 * (φC b / φC 1) * φA v₀
        rw [← hAτ, mul_smul, hAτ, hAτ]
        ring
      map_zero' := by simp
      map_add' := by
        intro a b
        change φC (a + b) / φC 1 = φC a / φC 1 + φC b / φC 1
        rw [map_add, add_div] }
  refine ⟨ρ, fun τ => ?_, fun τ v => hAτ τ v, fun τ v => ?_⟩
  · change φC τ = φC 1 * (φC τ / φC 1)
    field_simp
  · change φℓ (τ • v) = φC τ / φC 1 * φℓ v
    rw [hℓ1, hℓ1, hAτ]
    ring

theorem U4qLocalData.exists_ringHom_field {F K : Type} [Field F] [Field K]
    (hH : Hyp111 L1 L2 S) (hD : U4qLocalData L1 L2 S f) (hS : Nat.card S = 2 ^ (6 * f))
    (c₁ : U4qCoordLeft L1 L2 S f F) (c₂ : U4qCoordRight L1 L2 S f K) :
    ∃ (ρ : F →+* K) (κ : K), κ ≠ 0 ∧ κ ^ 2 ^ f = κ ∧ (∀ τ : F, ρ τ ^ 2 ^ f = ρ τ) ∧
      (∀ x : K, x ^ 2 ^ f = x → ∃ τ : F, ρ τ = x) ∧
      (∀ (a : G) (ha : a ∈ pCoreOf 2 L1) (ha' : a ∈ L2) (b : G) (hb : b ∈ pCoreOf 2 L1)
        (hb' : b ∈ L2) (τ : F),
        Multiplicative.toAdd (c₁.β ⟨b, hb⟩) 1 = τ • Multiplicative.toAdd (c₁.β ⟨a, ha⟩) 1 →
          (c₂.α ⟨b, hb'⟩ : Matrix (Fin 2) (Fin 2) K) 0 1 =
            ρ τ * (c₂.α ⟨a, ha'⟩ : Matrix (Fin 2) (Fin 2) K) 0 1) ∧
      (∀ (z : G) (hz : z ∈ pCoreOf 2 L1 ⊓ pCoreOf 2 L2) (w : G)
        (hw : w ∈ pCoreOf 2 L1 ⊓ pCoreOf 2 L2) (τ : F),
        Multiplicative.toAdd (c₁.β ⟨w, hw.1⟩) 0 = τ • Multiplicative.toAdd (c₁.β ⟨z, hz.1⟩) 0 →
          Multiplicative.toAdd (c₂.β ⟨w, hw.2⟩) 0 1 =
            ρ τ * Multiplicative.toAdd (c₂.β ⟨z, hz.2⟩) 0 1) ∧
      (∀ (c : G) (hc : c ∈ pCoreOf 2 L2) (hc' : c ∈ L1),
        Multiplicative.toAdd (c₂.β ⟨c, hc⟩) 1 1 =
          κ * ρ ((c₁.α ⟨c, hc'⟩ : Matrix (Fin 2) (Fin 2) F) 0 1)) := by
  classical
  haveI : Finite F := Nat.finite_of_card_ne_zero (by rw [c₁.card]; positivity)
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [c₂.card]; positivity)
  have hU : UnitaryFieldData 2 f K := ⟨Nat.prime_two, hD.one_le, c₂.card⟩
  have hSL1 : S ≤ L1 := hD.le_left hH hS
  have hSL2 : S ≤ L2 := hD.le_right hH hS
  have hQ1S : pCoreOf 2 L1 ≤ S := hH.pCoreOf_le_left
  have hQ2S : pCoreOf 2 L2 ≤ S := hH.pCoreOf_le_right
  have hsecA : ∀ v : Fin 2 → F, ∃ a, a ∈ pCoreOf 2 L1 ∧ bL c₁ a 1 = v := by
    intro v
    obtain ⟨a, ha, haM⟩ := bL_surj c₁ (Matrix.of ![0, v])
    exact ⟨a, ha, by rw [haM]; rfl⟩
  choose secA hsecA_mem hsecA_spec using hsecA
  have hsecC : ∀ τ : F, ∃ c, c ∈ pCoreOf 2 L2 ∧ pL c₁ c = τ := by
    intro τ
    obtain ⟨x, hx, hxα⟩ := c₁.exists_pCoreOf_right hH hD hS τ
    refine ⟨x, hx, ?_⟩
    rw [pL_of_mem c₁ x.2, hxα]
    simp
  choose secC hsecC_mem hsecC_spec using hsecC
  have hsecL : ∀ w : Fin 2 → F, ∃ z, z ∈ pCoreOf 2 L1 ⊓ pCoreOf 2 L2 ∧ bL c₁ z 0 = w := by
    intro w
    obtain ⟨z, hz, hzM⟩ := bL_surj c₁ (Matrix.of ![w, 0])
    refine ⟨z, ⟨hz, (bL_one_eq_zero_iff c₁ hz).mp (by rw [hzM]; rfl)⟩, by rw [hzM]; rfl⟩
  choose secL hsecL_mem hsecL_spec using hsecL
  have hA_spec : ∀ a, a ∈ pCoreOf 2 L1 → pR c₂ (secA (bL c₁ a 1)) = pR c₂ a := by
    intro a ha
    have ha' := hsecA_mem (bL c₁ a 1)
    have hk : (secA (bL c₁ a 1))⁻¹ * a ∈ pCoreOf 2 L2 := by
      rw [← bL_one_eq_zero_iff c₁ (mul_mem (inv_mem ha') ha)]
      funext j
      rw [bL_inv_mul_apply c₁ ha ha', hsecA_spec, sub_self, Pi.zero_apply]
    exact (pR_eq_of_inv_mul_mem c₂ (hSL2 (hQ1S ha)) (hSL2 (hQ1S ha')) hk).symm
  have hC_spec : ∀ c, c ∈ pCoreOf 2 L2 → bR c₂ (secC (pL c₁ c)) 1 1 = bR c₂ c 1 1 := by
    intro c hc
    have hc' := hsecC_mem (pL c₁ c)
    have hk2 : (secC (pL c₁ c))⁻¹ * c ∈ pCoreOf 2 L2 := mul_mem (inv_mem hc') hc
    have hk1 : (secC (pL c₁ c))⁻¹ * c ∈ pCoreOf 2 L1 := by
      rw [← pL_eq_zero_iff c₁ (hSL1 (hQ2S hk2)) (hQ2S hk2),
        pL_inv_mul c₁ (hSL1 (hQ2S hc)) (hSL1 (hQ2S hc')) (hQ2S hc) (hQ2S hc'), hsecC_spec,
        sub_self]
    have h := (bR_one_one_eq_zero_iff c₂ hk2).mpr hk1
    rw [bR_inv_mul_apply c₂ hc hc'] at h
    exact (sub_eq_zero.mp h).symm
  have hL_spec : ∀ z, z ∈ pCoreOf 2 L1 ⊓ pCoreOf 2 L2 →
      bR c₂ (secL (bL c₁ z 0)) 0 1 = bR c₂ z 0 1 := by
    intro z hz
    have hz' := hsecL_mem (bL c₁ z 0)
    have hk1 : (secL (bL c₁ z 0))⁻¹ * z ∈ pCoreOf 2 L1 := mul_mem (inv_mem hz'.1) hz.1
    have hk2 : (secL (bL c₁ z 0))⁻¹ * z ∈ pCoreOf 2 L2 := mul_mem (inv_mem hz'.2) hz.2
    have hz1 : bL c₁ z 1 = 0 := (bL_one_eq_zero_iff c₁ hz.1).mpr hz.2
    have hz'1 : bL c₁ (secL (bL c₁ z 0)) 1 = 0 := (bL_one_eq_zero_iff c₁ hz'.1).mpr hz'.2
    have hkZ : (secL (bL c₁ z 0))⁻¹ * z ∈ centerOf (pCoreOf 2 L1) := by
      rw [← bL_eq_zero_iff c₁ hk1]
      ext i j
      rw [bL_inv_mul_apply c₁ hz.1 hz'.1]
      fin_cases i
      · simp [hsecL_spec]
      · simp [hz1, hz'1]
    have h := ((bR_center_iff c₂ hk2).mpr hkZ).1
    rw [bR_inv_mul_apply c₂ hz.2 hz'.2] at h
    exact (sub_eq_zero.mp h).symm
  let φA : (Fin 2 → F) →+ K := AddMonoidHom.mk' (fun v => pR c₂ (secA v)) (by
    intro v v'
    have ha := hsecA_mem v
    have ha' := hsecA_mem v'
    have h := hA_spec _ (mul_mem ha ha')
    have hrow : bL c₁ (secA v * secA v') 1 = v + v' := by
      rw [bL_mul c₁ ha ha']
      funext j
      rw [Pi.add_apply, Matrix.add_apply, hsecA_spec, hsecA_spec]
    rw [hrow] at h
    change pR c₂ (secA (v + v')) = pR c₂ (secA v) + pR c₂ (secA v')
    rw [h, pR_mul c₂ (hSL2 (hQ1S ha)) (hSL2 (hQ1S ha')) (hQ1S ha) (hQ1S ha')])
  let φC : F →+ K := AddMonoidHom.mk' (fun τ => bR c₂ (secC τ) 1 1) (by
    intro τ τ'
    have hc := hsecC_mem τ
    have hc' := hsecC_mem τ'
    have h := hC_spec _ (mul_mem hc hc')
    rw [pL_mul c₁ (hSL1 (hQ2S hc)) (hSL1 (hQ2S hc')) (hQ2S hc) (hQ2S hc'), hsecC_spec,
      hsecC_spec, bR_mul c₂ hc hc', Matrix.add_apply] at h
    exact h)
  let φℓ : (Fin 2 → F) →+ K := AddMonoidHom.mk' (fun w => bR c₂ (secL w) 0 1) (by
    intro w w'
    have hz := hsecL_mem w
    have hz' := hsecL_mem w'
    have h := hL_spec _ (mul_mem hz hz')
    have hrow : bL c₁ (secL w * secL w') 0 = w + w' := by
      rw [bL_mul c₁ hz.1 hz'.1]
      funext j
      rw [Pi.add_apply, Matrix.add_apply, hsecL_spec, hsecL_spec]
    rw [hrow, bR_mul c₂ hz.2 hz'.2, Matrix.add_apply] at h
    exact h)
  have hφA : ∀ a, a ∈ pCoreOf 2 L1 → φA (bL c₁ a 1) = pR c₂ a := hA_spec
  have hφC : ∀ c, c ∈ pCoreOf 2 L2 → φC (pL c₁ c) = bR c₂ c 1 1 := hC_spec
  have hφℓ : ∀ z, z ∈ pCoreOf 2 L1 ⊓ pCoreOf 2 L2 → φℓ (bL c₁ z 0) = bR c₂ z 0 1 := hL_spec
  have hpair : ∀ (τ : F) (v : Fin 2 → F), φℓ (τ • v) = φA v * φC τ := by
    intro τ v
    have ha := hsecA_mem v
    have hc := hsecC_mem τ
    obtain ⟨hw, h0, h1⟩ := pairing hH hD hS c₁ c₂ ha hc
    rw [hsecC_spec, hsecA_spec] at h0
    rw [← h0, hφℓ _ hw, h1]
    rfl
  have hAker : ∀ v, φA v = 0 → v = 0 := by
    intro v hv
    have ha := hsecA_mem v
    have h2 : secA v ∈ pCoreOf 2 L2 :=
      (pR_eq_zero_iff c₂ (hSL2 (hQ1S ha)) (hQ1S ha)).mp hv
    rw [← hsecA_spec v]
    exact (bL_one_eq_zero_iff c₁ ha).mpr h2
  have hCker : ∀ τ, φC τ = 0 → τ = 0 := by
    intro τ hτ
    have hc := hsecC_mem τ
    have h1 : secC τ ∈ pCoreOf 2 L1 := (bR_one_one_eq_zero_iff c₂ hc).mp hτ
    rw [← hsecC_spec τ]
    exact (pL_eq_zero_iff c₁ (hSL1 (hQ2S hc)) (hQ2S hc)).mpr h1
  have hv₀ : (Pi.single 0 1 : Fin 2 → F) ≠ 0 := by
    intro h
    have := congrFun h 0
    simp at this
  obtain ⟨ρ, hρC, hρA, hρℓ⟩ := exists_ringHom_of_pairing φA φℓ φC hAker hCker _ hv₀ hpair
  have hκ : φC 1 ≠ 0 := fun h0 => one_ne_zero (hCker 1 h0)
  have hCfix : ∀ τ, φC τ ^ 2 ^ f = φC τ := by
    intro τ
    have h := congrFun (congrFun (bR_herm c₂ (hsecC_mem τ)) 1) 1
    simp only [Matrix.map_apply, Matrix.transpose_apply] at h
    exact h
  have hρfix : ∀ τ, ρ τ ^ 2 ^ f = ρ τ := by
    intro τ
    have h := hCfix τ
    rw [hρC τ, mul_pow, hCfix 1] at h
    exact mul_left_cancel₀ hκ h
  have hρsurj : ∀ x : K, x ^ 2 ^ f = x → ∃ τ : F, ρ τ = x := by
    intro x hx
    let ρ' : F → hU.fixedField := fun τ =>
      ⟨ρ τ, by rw [hU.mem_fixedField, hU.bar_apply]; exact hρfix τ⟩
    have hinj : Function.Injective ρ' := by
      intro a b hab
      exact ρ.injective (congrArg Subtype.val hab)
    have hbij := hinj.bijective_of_nat_card_le (by rw [hU.card_fixedField, c₁.card])
    obtain ⟨τ, hτ⟩ := hbij.2 ⟨x, by rw [hU.mem_fixedField, hU.bar_apply]; exact hx⟩
    exact ⟨τ, congrArg Subtype.val hτ⟩
  refine ⟨ρ, φC 1, hκ, hCfix 1, hρfix, hρsurj, ?_, ?_, ?_⟩
  · intro a ha ha' b hb hb' τ hab
    have h := hρA τ (bL c₁ a 1)
    rw [← bL_of_mem c₁ ha, ← bL_of_mem c₁ hb] at hab
    rw [← hab, hφA b hb, hφA a ha] at h
    rw [← pR_of_mem c₂ hb', ← pR_of_mem c₂ ha']
    exact h
  · intro z hz w hw τ hzw
    have h := hρℓ τ (bL c₁ z 0)
    rw [← bL_of_mem c₁ hz.1, ← bL_of_mem c₁ hw.1] at hzw
    rw [← hzw, hφℓ w hw, hφℓ z hz] at h
    rw [← bR_of_mem c₂ hw.2, ← bR_of_mem c₂ hz.2]
    exact h
  · intro c hc hc'
    have h := hρC (pL c₁ c)
    rw [hφC c hc] at h
    rw [← bR_of_mem c₂ hc, ← pL_of_mem c₁ hc']
    exact h

theorem U4qLocalData.exists_ringEquiv_fixedField {F K : Type} [Field F] [Field K]
    (hH : Hyp111 L1 L2 S) (hD : U4qLocalData L1 L2 S f) (hS : Nat.card S = 2 ^ (6 * f))
    (c₁ : U4qCoordLeft L1 L2 S f F) (c₂ : U4qCoordRight L1 L2 S f K)
    (hU : UnitaryFieldData 2 f K) :
    ∃ (ρ : F ≃+* hU.fixedField) (κ : hU.fixedField), κ ≠ 0 ∧
      (∀ (a : G) (ha : a ∈ pCoreOf 2 L1) (ha' : a ∈ L2) (b : G) (hb : b ∈ pCoreOf 2 L1)
        (hb' : b ∈ L2) (τ : F),
        Multiplicative.toAdd (c₁.β ⟨b, hb⟩) 1 = τ • Multiplicative.toAdd (c₁.β ⟨a, ha⟩) 1 →
          (c₂.α ⟨b, hb'⟩ : Matrix (Fin 2) (Fin 2) K) 0 1 =
            (ρ τ : K) * (c₂.α ⟨a, ha'⟩ : Matrix (Fin 2) (Fin 2) K) 0 1) ∧
      (∀ (z : G) (hz : z ∈ pCoreOf 2 L1 ⊓ pCoreOf 2 L2) (w : G)
        (hw : w ∈ pCoreOf 2 L1 ⊓ pCoreOf 2 L2) (τ : F),
        Multiplicative.toAdd (c₁.β ⟨w, hw.1⟩) 0 = τ • Multiplicative.toAdd (c₁.β ⟨z, hz.1⟩) 0 →
          Multiplicative.toAdd (c₂.β ⟨w, hw.2⟩) 0 1 =
            (ρ τ : K) * Multiplicative.toAdd (c₂.β ⟨z, hz.2⟩) 0 1) ∧
      (∀ (c : G) (hc : c ∈ pCoreOf 2 L2) (hc' : c ∈ L1),
        Multiplicative.toAdd (c₂.β ⟨c, hc⟩) 1 1 =
          (κ : K) * (ρ ((c₁.α ⟨c, hc'⟩ : Matrix (Fin 2) (Fin 2) F) 0 1) : K)) := by
  obtain ⟨ρ, κ, hκ, hκfix, hρfix, hρsurj, hA, hℓ, hC⟩ :=
    hD.exists_ringHom_field hH hS c₁ c₂
  have hmem : ∀ τ : F, ρ τ ∈ hU.fixedField := fun τ => by
    rw [hU.mem_fixedField, hU.bar_apply]
    exact hρfix τ
  let ρ' : F →+* hU.fixedField := ρ.codRestrict hU.fixedField hmem
  have hbij : Function.Bijective ρ' := by
    refine ⟨fun a b hab => ρ.injective (congrArg Subtype.val hab), fun x => ?_⟩
    obtain ⟨τ, hτ⟩ := hρsurj x (by rw [← hU.bar_apply]; exact (hU.mem_fixedField).mp x.2)
    exact ⟨τ, Subtype.ext hτ⟩
  refine ⟨RingEquiv.ofBijective ρ' hbij,
    ⟨κ, by rw [hU.mem_fixedField, hU.bar_apply]; exact hκfix⟩,
    fun h0 => hκ (congrArg Subtype.val h0), hA, hℓ, hC⟩

end CFSG.Quasithin.F112R.St84

end
