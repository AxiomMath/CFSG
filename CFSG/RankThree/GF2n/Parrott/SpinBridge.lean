module

public import CFSG.RankThree.GF2n.Parrott.Section4SpinGlue
public import CFSG.RankThree.GF2n.Parrott.SpinE27Fixed

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.LinearAlgebra.F2Cube (fixedCount)
open scoped Matrix

variable {G : Type} [Group G] [Finite G] {z : G}

set_option quotPrecheck false in
local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)
set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "Mat8" => Matrix (Fin 8) (Fin 8) (ZMod 2)

@[expose] noncomputable def spinVecToV (h : Tim79a.ParrottHyp z) (P : GL8) (w : V) :
    QuotientV.V z :=
  (mulEquivV h).symm (Multiplicative.ofAdd ((P : Mat8) *ᵥ w))

theorem toAdd_mulEquivV_spinVecToV (h : Tim79a.ParrottHyp z) (P : GL8) (w : V) :
    Multiplicative.toAdd (mulEquivV h (spinVecToV h P w)) = (P : Mat8) *ᵥ w := by
  simp [spinVecToV]

theorem spinVecToV_add (h : Tim79a.ParrottHyp z) (P : GL8) (u w : V) :
    spinVecToV h P (u + w) = spinVecToV h P u * spinVecToV h P w := by
  apply (mulEquivV h).injective
  rw [map_mul]
  apply Multiplicative.toAdd.injective
  rw [toAdd_mul, toAdd_mulEquivV_spinVecToV, toAdd_mulEquivV_spinVecToV,
    toAdd_mulEquivV_spinVecToV, Matrix.mulVec_add]

theorem spinVecToV_injective (h : Tim79a.ParrottHyp z) (P : GL8) :
    Function.Injective (spinVecToV h P) := by
  intro w w' hww
  have h1 := congrArg (fun v => Multiplicative.toAdd (mulEquivV h v)) hww
  simp only [toAdd_mulEquivV_spinVecToV] at h1
  have h2 := congrArg (fun u => ((P⁻¹ : GL8) : Mat8) *ᵥ u) h1
  simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.one_mulVec] at h2
  exact h2

theorem spinVecToV_surjective (h : Tim79a.ParrottHyp z) (P : GL8) :
    Function.Surjective (spinVecToV h P) := by
  intro v
  refine ⟨((P⁻¹ : GL8) : Mat8) *ᵥ Multiplicative.toAdd (mulEquivV h v), ?_⟩
  apply (mulEquivV h).injective
  apply Multiplicative.toAdd.injective
  rw [toAdd_mulEquivV_spinVecToV, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, Matrix.one_mulVec]

theorem spinVecToV_zero (h : Tim79a.ParrottHyp z) (P : GL8) : spinVecToV h P 0 = 1 := by
  apply (mulEquivV h).injective
  apply Multiplicative.toAdd.injective
  simp [toAdd_mulEquivV_spinVecToV]

section Certified

variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

theorem qVZMod_seven_eq (h : Tim79a.ParrottHyp z) (a b c : QuotientV.V z) :
    qVZMod h (a * b * c) + qVZMod h (a * b) + qVZMod h (a * c) + qVZMod h (b * c) +
      qVZMod h a + qVZMod h b + qVZMod h c = 0 := by
  rw [qVZMod_mul_add h (a * b) c, polarVZMod_add h a b c, qVZMod_mul_add h a c,
    qVZMod_mul_add h b c]
  have key : ∀ x1 x2 x3 x4 x5 x6 : ZMod 2,
      (x1 + x2 + (x3 + x4)) + x1 + (x5 + x2 + x3) + (x6 + x2 + x4) + x5 + x6 + x2 = 0 := by
    decide
  exact key _ _ _ _ _ _


theorem conjV_spinVecToV (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹) (y : ↥(H z)) (w : V) :
    conjV h y (spinVecToV h P w) = spinVecToV h P ((rhoA (qH D y) : Mat8) *ᵥ w) := by
  apply (mulEquivV h).injective
  apply Multiplicative.toAdd.injective
  rw [← mulVec_mulAutVEquivGL h (conjV h y) (spinVecToV h P w), toAdd_mulEquivV_spinVecToV,
    ← actionQA45_qH D h y, hP, toAdd_mulEquivV_spinVecToV]
  have key : (P * rhoA (qH D y) * P⁻¹ * P : GL8) = P * rhoA (qH D y) := by group
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, key, Units.val_mul, ← Matrix.mulVec_mulVec]

theorem qVZMod_spinVecToV_eq_q (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹) (w : V) :
    qVZMod h (spinVecToV h P w) = q w := by
  have hQ : (fun w : V => qVZMod h (spinVecToV h P w)) = 0 ∨
      (fun w : V => qVZMod h (spinVecToV h P w)) = q := by
    refine spinInvariantQuadratic_unique _ ?_ ?_
    · intro u u' w
      have h1 := qVZMod_seven_eq h (spinVecToV h P u) (spinVecToV h P u') (spinVecToV h P w)
      rwa [← spinVecToV_add, ← spinVecToV_add, ← spinVecToV_add, ← spinVecToV_add] at h1
    · intro a w
      obtain ⟨y, rfl⟩ := qH_surjective D a
      show qVZMod h (spinVecToV h P _) = qVZMod h (spinVecToV h P w)
      rw [← conjV_spinVecToV D h P hP y w, qVZMod_conj]
  rcases hQ with h0 | hq
  · exfalso
    have hall : ∀ v : QuotientV.V z, qVZMod h v = 0 := by
      intro v
      obtain ⟨w', rfl⟩ := spinVecToV_surjective h P v
      exact congrFun h0 w'
    have hone : ∀ v : QuotientV.V z, v = 1 := by
      intro v
      refine polarVZMod_nondegenerate h v (fun w' => ?_)
      have h1 := qVZMod_mul_add h v w'
      rw [hall, hall, hall] at h1
      simpa using h1.symm
    have hcard := QuotientV.card_V h
    have hsub : Subsingleton (QuotientV.V z) := ⟨fun a b => (hone a).trans (hone b).symm⟩
    have h1 : Nat.card (QuotientV.V z) = 1 := Nat.card_unique
    rw [hcard] at h1
    norm_num at h1
  · exact congrFun hq w

theorem polarVZMod_spinVecToV_eq_b (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹) (v w : V) :
    polarVZMod h (spinVecToV h P v) (spinVecToV h P w) = b v w := by
  have h1 := qVZMod_mul_add h (spinVecToV h P v) (spinVecToV h P w)
  rw [← spinVecToV_add, qVZMod_spinVecToV_eq_q D h P hP, qVZMod_spinVecToV_eq_q D h P hP,
    qVZMod_spinVecToV_eq_q D h P hP] at h1
  unfold b
  rw [h1]
  have key : ∀ x y p : ZMod 2, p = (x + y + p) + x + y := by decide
  exact key _ _ _

theorem fixed_point_free_of_fixedCount (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹) {r : ↥(H z)}
    (hr : fixedCount ((rhoA (qH D r) : GL8) : Mat8) = 1) (v : QuotientV.V z)
    (hv : conjV h r v = v) : v = 1 := by
  obtain ⟨w, rfl⟩ := spinVecToV_surjective h P v
  rw [conjV_spinVecToV D h P hP] at hv
  have h1 := spinVecToV_injective h P hv
  have h2 := eq_zero_of_fixedCount_eq_one hr h1
  rw [h2, spinVecToV_zero]

end Certified

end CFSG.RankThree.GF2n.Parrott
