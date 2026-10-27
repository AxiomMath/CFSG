module

public import CFSG.Quasithin.Recognition.St84.Gen.NatSecDefs
public import Mathlib.GroupTheory.Commutator.Basic

import CFSG.Quasithin.Recognition.St84.Gen.SL2Semilinear
import CFSG.CGT.Timmesfeld75.L2Defs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin.F112R.St84

open Matrix CFSG.CGT.Timmesfeld75
open scoped MatrixGroups commutatorElement

variable {G : Type*} [Group G] {F : Type} [Field F]

structure IsNatSecCoord (L E N : Subgroup G) (α : ↥L →* SL(2, F)) (v : G → Fin 2 → F) :
    Prop where
  map_mul : ∀ x ∈ E, ∀ y ∈ E, v (x * y) = v x + v y
  eq_zero_iff : ∀ x ∈ E, v x = 0 ↔ x ∈ N
  surj : ∀ u : Fin 2 → F, ∃ x ∈ E, v x = u
  conj_mem : ∀ ℓ : ↥L, ∀ x ∈ E, (ℓ : G) * x * (ℓ : G)⁻¹ ∈ E
  conj : ∀ ℓ : ↥L, ∀ x ∈ E,
    v ((ℓ : G) * x * (ℓ : G)⁻¹) = (α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ v x

theorem IsNatSecOf.exists_isNatSecCoord {L E N : Subgroup G} {α : ↥L →* SL(2, F)}
    (h : IsNatSecOf L E N α) (hE : ∀ ℓ ∈ L, ∀ x ∈ E, ℓ * x * ℓ⁻¹ ∈ E) :
    ∃ v : G → Fin 2 → F, IsNatSecCoord L E N α v := by
  classical
  obtain ⟨β, hsurj, hker, heq⟩ := h
  let v : G → Fin 2 → F := fun x =>
    if hx : x ∈ E then Multiplicative.toAdd (β ⟨x, hx⟩) else 0
  have hv : ∀ x (hx : x ∈ E), v x = Multiplicative.toAdd (β ⟨x, hx⟩) := fun x hx => dif_pos hx
  refine ⟨v, ⟨fun x hx y hy => ?_, fun x hx => ?_, fun u => ?_,
    fun ℓ x hx => hE ℓ ℓ.2 x hx, fun ℓ x hx => ?_⟩⟩
  · rw [hv x hx, hv y hy, hv (x * y) (mul_mem hx hy), ← toAdd_mul, ← map_mul]
    rfl
  · rw [hv x hx, toAdd_eq_zero, ← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  · obtain ⟨y, hy⟩ := hsurj (Multiplicative.ofAdd u)
    exact ⟨y, y.2, by rw [hv y y.2, hy, toAdd_ofAdd]⟩
  · rw [hv x hx, hv _ (hE ℓ ℓ.2 x hx)]
    exact heq ℓ ⟨x, hx⟩ ⟨_, hE ℓ ℓ.2 x hx⟩ rfl

private theorem utriElt_mulVec (r : F) (w : Fin 2 → F) :
    (utriElt r : Matrix (Fin 2) (Fin 2) F) *ᵥ w = ![w 0 + r * w 1, w 1] := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, utriElt_apply_00,
    utriElt_apply_01, utriElt_apply_10, utriElt_apply_11]

private theorem ltriElt_mulVec (r : F) (w : Fin 2 → F) :
    (ltriElt r : Matrix (Fin 2) (Fin 2) F) *ᵥ w = ![w 0, r * w 0 + w 1] := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, ltriElt_apply_00,
    ltriElt_apply_01, ltriElt_apply_10, ltriElt_apply_11]

namespace IsNatSecCoord

variable {L E N : Subgroup G} {α : ↥L →* SL(2, F)} {v : G → Fin 2 → F}

theorem map_one (hv : IsNatSecCoord L E N α v) : v 1 = 0 := by
  have h := hv.map_mul 1 (one_mem E) 1 (one_mem E)
  rw [one_mul] at h
  exact left_eq_add.mp h

theorem map_inv (hv : IsNatSecCoord L E N α v) {x : G} (hx : x ∈ E) : v x⁻¹ = -v x := by
  have h := hv.map_mul x hx x⁻¹ (inv_mem hx)
  rw [mul_inv_cancel, hv.map_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem map_inv_mul (hv : IsNatSecCoord L E N α v) {x y : G} (hx : x ∈ E) (hy : y ∈ E) :
    v (x⁻¹ * y) = v y - v x := by
  rw [hv.map_mul _ (inv_mem hx) _ hy, hv.map_inv hx, neg_add_eq_sub]

theorem inv_mul_mem (hv : IsNatSecCoord L E N α v) {x y : G} (hx : x ∈ E) (hy : y ∈ E)
    (h : v x = v y) : x⁻¹ * y ∈ N :=
  (hv.eq_zero_iff _ (mul_mem (inv_mem hx) hy)).mp (by rw [hv.map_inv_mul hx hy, h, sub_self])

theorem eq_of_eq (hv : IsNatSecCoord L E ⊥ α v) {x y : G} (hx : x ∈ E) (hy : y ∈ E)
    (h : v x = v y) : x = y := by
  have h1 := hv.inv_mul_mem hx hy h
  rw [Subgroup.mem_bot, inv_mul_eq_one] at h1
  exact h1

theorem exists_eq_smul (hv : IsNatSecCoord L E N α v) (hα : Function.Surjective α)
    {φ : G → Fin 2 → F} (hφmul : ∀ x ∈ E, ∀ y ∈ E, φ (x * y) = φ x + φ y)
    (hφN : ∀ x ∈ E, x ∈ N → φ x = 0)
    (hφconj : ∀ ℓ : ↥L, ∀ x ∈ E,
      φ ((ℓ : G) * x * (ℓ : G)⁻¹) = (α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ φ x) :
    ∃ s : F, ∀ x ∈ E, φ x = s • v x := by
  classical
  choose sec hsecE hsecv using hv.surj
  have hdep : ∀ x ∈ E, φ (sec (v x)) = φ x := by
    intro x hx
    have hs := hsecE (v x)
    have hN := hv.inv_mul_mem hx hs (hsecv (v x)).symm
    have h := hφmul x hx _ (mul_mem (inv_mem hx) hs)
    rw [mul_inv_cancel_left, hφN _ (mul_mem (inv_mem hx) hs) hN, add_zero] at h
    exact h
  let M : (Fin 2 → F) →+ (Fin 2 → F) :=
    { toFun := fun u => φ (sec u)
      map_zero' := hφN _ (hsecE 0) ((hv.eq_zero_iff _ (hsecE 0)).mp (hsecv 0))
      map_add' := fun u u' => by
        have h := hdep _ (mul_mem (hsecE u) (hsecE u'))
        rw [hv.map_mul _ (hsecE u) _ (hsecE u'), hsecv, hsecv] at h
        rw [h, hφmul _ (hsecE u) _ (hsecE u')] }
  have hMapp : ∀ u, M u = φ (sec u) := fun _ => rfl
  have hM : ∀ (A : SL(2, F)) (w : Fin 2 → F),
      M ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ w) = (A : Matrix (Fin 2) (Fin 2) F) *ᵥ M w := by
    intro A w
    obtain ⟨ℓ, rfl⟩ := hα A
    have hx := hsecE w
    have h1 : (α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ w = v ((ℓ : G) * sec w * (ℓ : G)⁻¹) := by
      rw [hv.conj ℓ _ hx, hsecv]
    rw [hMapp, hMapp, h1, hdep _ (hv.conj_mem ℓ _ hx), hφconj ℓ _ hx]
  obtain ⟨s, hs⟩ := exists_eq_smul_of_commute_SL2 M hM
  refine ⟨s, fun x hx => ?_⟩
  rw [← hdep x hx, ← hMapp]
  exact hs (v x)

theorem smul_injective (hv : IsNatSecCoord L E N α v) {s t : F}
    (h : ∀ x ∈ E, s • v x = t • v x) : s = t := by
  obtain ⟨x, hx, hvx⟩ := hv.surj ![1, 0]
  have h0 := congrFun (h x hx) 0
  rw [hvx] at h0
  simpa using h0

theorem mem_of_conj_eq (hv : IsNatSecCoord L E N α v) (hα : Function.Surjective α) {x : G}
    (hx : x ∈ E) (h : ∀ ℓ : ↥L, v ((ℓ : G) * x * (ℓ : G)⁻¹) = v x) : x ∈ N := by
  refine (hv.eq_zero_iff x hx).mp ?_
  obtain ⟨ℓ₁, hℓ₁⟩ := hα (utriElt 1)
  obtain ⟨ℓ₂, hℓ₂⟩ := hα (ltriElt 1)
  have h1 := h ℓ₁
  have h2 := h ℓ₂
  rw [hv.conj ℓ₁ x hx, hℓ₁, utriElt_mulVec] at h1
  rw [hv.conj ℓ₂ x hx, hℓ₂, ltriElt_mulVec] at h2
  have e1 := congrFun h1 0
  have e2 := congrFun h2 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_mul] at e1 e2
  funext i
  fin_cases i
  · simpa using e2
  · simpa using e1

theorem commutator_mem (hv : IsNatSecCoord L E N α v) {x : G} (hx : x ∈ E) (ℓ : ↥L) :
    ⁅x, (ℓ : G)⁆ ∈ E := by
  rw [commutatorElement_def,
    show x * ℓ * x⁻¹ * (ℓ : G)⁻¹ = x * ((ℓ : G) * x⁻¹ * (ℓ : G)⁻¹) by group]
  exact mul_mem hx (hv.conj_mem ℓ _ (inv_mem hx))

theorem map_commutator (hv : IsNatSecCoord L E N α v) {x : G} (hx : x ∈ E) (ℓ : ↥L) :
    v ⁅x, (ℓ : G)⁆ = v x - (α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ v x := by
  rw [commutatorElement_def,
    show x * ℓ * x⁻¹ * (ℓ : G)⁻¹ = x * ((ℓ : G) * x⁻¹ * (ℓ : G)⁻¹) by group,
    hv.map_mul _ hx _ (hv.conj_mem ℓ _ (inv_mem hx)), hv.conj ℓ _ (inv_mem hx), hv.map_inv hx,
    Matrix.mulVec_neg, sub_eq_add_neg]

theorem exists_mem_commutator (hv : IsNatSecCoord L E N α v) (hα : Function.Surjective α)
    (u : Fin 2 → F) : ∃ y ∈ ⁅E, L⁆, y ∈ E ∧ v y = u := by
  obtain ⟨ℓ₁, hℓ₁⟩ := hα (utriElt 1)
  obtain ⟨ℓ₂, hℓ₂⟩ := hα (ltriElt 1)
  obtain ⟨x₁, hx₁, hv₁⟩ := hv.surj ![0, -u 0]
  obtain ⟨x₂, hx₂, hv₂⟩ := hv.surj ![-u 1, 0]
  refine ⟨⁅x₁, (ℓ₁ : G)⁆ * ⁅x₂, (ℓ₂ : G)⁆,
    mul_mem (Subgroup.commutator_mem_commutator hx₁ ℓ₁.2)
      (Subgroup.commutator_mem_commutator hx₂ ℓ₂.2),
    mul_mem (hv.commutator_mem hx₁ ℓ₁) (hv.commutator_mem hx₂ ℓ₂), ?_⟩
  rw [hv.map_mul _ (hv.commutator_mem hx₁ ℓ₁) _ (hv.commutator_mem hx₂ ℓ₂),
    hv.map_commutator hx₁, hv.map_commutator hx₂, hℓ₁, hℓ₂, hv₁, hv₂, utriElt_mulVec,
    ltriElt_mulVec]
  ext i
  fin_cases i <;> simp

end IsNatSecCoord

end CFSG.Quasithin.F112R.St84

end
