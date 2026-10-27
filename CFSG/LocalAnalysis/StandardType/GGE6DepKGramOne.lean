module

public import CFSG.LocalAnalysis.StandardType.GGE6DepKGlueDefs
public import CFSG.LocalAnalysis.StandardType.GGE6DepModelShapeDefs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

public section

namespace CFSG.StandardType

namespace E6Dep

open Matrix

private lemma dot_gbetaR {M : Mat6} {c r : ZMod 3} (hG : Mᵀ * gram6 * M = gbetaR c r)
    (v : Vec6) : v ⬝ᵥ (gbetaR c r).mulVec v = norm6 (M.mulVec v) := by
  rw [← hG, ← mulVec_mulVec, ← mulVec_mulVec, Matrix.dotProduct_transpose_mulVec,
    dotProduct_comm]
  rfl

private lemma gbetaR_quad (c r : ZMod 3) (v : Vec6) :
    v ⬝ᵥ (gbetaR c r).mulVec v =
      v 0 * v 0 + v 1 * v 1 + v 2 * v 2 + v 3 * v 3
        + 2 * (v 0 * v 1 + v 1 * v 2 + v 2 * v 3)
        + r * ((c * v 4 - v 5) * (c * v 4 - v 5)) := by
  simp [gbetaR, Matrix.mulVec, Fin.sum_univ_six, Matrix.vecHead, Matrix.vecTail]
  ring

private lemma fibre_card {M : Mat6} {c : ZMod 3} {w : Vec6}
    (hMonto : ∀ v : Vec6, v 5 = 0 → ∃ u, M.mulVec u = v)
    (hMy : M.mulVec (kY c) = 0)
    (hMker : ∀ v, M.mulVec v = 0 → ∃ j : ZMod 3, v = j • kY c)
    (hw5 : w 5 = 0) :
    (Finset.univ.filter fun v : Vec6 => M.mulVec v = w).card = 3 := by
  obtain ⟨u₀, hu₀⟩ := hMonto w hw5
  have hmem : Set.MapsTo (fun j : ZMod 3 => u₀ + j • kY c)
      (Finset.univ : Finset (ZMod 3))
      (Finset.univ.filter (fun v : Vec6 => M.mulVec v = w)) := by
    intro j _
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, hu₀, hMy, smul_zero, add_zero]
  have hinj : Set.InjOn (fun j : ZMod 3 => u₀ + j • kY c)
      (Finset.univ : Finset (ZMod 3)) := by
    intro j₁ _ j₂ _ h
    have h4 := congrFun h 4
    simpa [kY, smul_eq_mul] using h4
  have hsurj : Set.SurjOn (fun j : ZMod 3 => u₀ + j • kY c)
      (Finset.univ : Finset (ZMod 3))
      (Finset.univ.filter (fun v : Vec6 => M.mulVec v = w)) := by
    intro v hv
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    have hker : M.mulVec (v - u₀) = 0 := by
      rw [Matrix.mulVec_sub, hv, hu₀, sub_self]
    obtain ⟨j, hj⟩ := hMker (v - u₀) hker
    refine ⟨j, Finset.mem_univ j, ?_⟩
    change u₀ + j • kY c = v
    rw [← hj]
    abel
  have hcard := Finset.card_nbij (fun j : ZMod 3 => u₀ + j • kY c) hmem hinj hsurj
  rw [← hcard]
  simp [ZMod.card]

private lemma normOne_card {M : Mat6} {c : ZMod 3}
    (hMonto : ∀ v : Vec6, v 5 = 0 → ∃ u, M.mulVec u = v) (hM5 : ∀ v, M.mulVec v 5 = 0)
    (hMy : M.mulVec (kY c) = 0)
    (hMker : ∀ v, M.mulVec v = 0 → ∃ j : ZMod 3, v = j • kY c) :
    (Finset.univ.filter fun v : Vec6 => norm6 (M.mulVec v) = 1).card = 216 := by
  have hmap : Set.MapsTo (fun v : Vec6 => M.mulVec v)
      (Finset.univ.filter (fun v : Vec6 => norm6 (M.mulVec v) = 1))
      (Finset.univ.filter (fun w : Vec6 => w 5 = 0 ∧ norm6 w = 1)) := by
    intro v hv
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    exact ⟨hM5 v, hv⟩
  have hsum := Finset.card_eq_sum_card_fiberwise hmap
  have hN : (Finset.univ.filter (fun w : Vec6 => w 5 = 0 ∧ norm6 w = 1)).card = 72 := by
    decide +kernel
  have hfib : ∀ w ∈ Finset.univ.filter (fun w : Vec6 => w 5 = 0 ∧ norm6 w = 1),
      ((Finset.univ.filter (fun v : Vec6 => norm6 (M.mulVec v) = 1)).filter
        (fun v => M.mulVec v = w)).card = 3 := by
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    obtain ⟨hw5, hwn⟩ := hw
    have hEq : (Finset.univ.filter (fun v : Vec6 => norm6 (M.mulVec v) = 1)).filter
        (fun v => M.mulVec v = w)
        = Finset.univ.filter (fun v : Vec6 => M.mulVec v = w) := by
      rw [Finset.filter_filter]
      apply Finset.filter_congr
      intro v _
      constructor
      · rintro ⟨_, hv⟩; exact hv
      · intro hv; exact ⟨by rw [hv]; exact hwn, hv⟩
    rw [hEq]
    exact fibre_card hMonto hMy hMker hw5
  calc
    (Finset.univ.filter fun v : Vec6 => norm6 (M.mulVec v) = 1).card
        = ∑ w ∈ Finset.univ.filter (fun w : Vec6 => w 5 = 0 ∧ norm6 w = 1),
            ((Finset.univ.filter (fun v : Vec6 => norm6 (M.mulVec v) = 1)).filter
              (fun v => M.mulVec v = w)).card := hsum
    _ = ∑ w ∈ Finset.univ.filter (fun w : Vec6 => w 5 = 0 ∧ norm6 w = 1), 3 :=
          Finset.sum_congr rfl hfib
    _ = 72 * 3 := by
          rw [Finset.sum_const_nat (m := 3) (fun _ _ => rfl), hN]
    _ = 216 := by norm_num

private lemma poly_count (c r : ZMod 3) :
    (Finset.univ.filter fun v : Vec6 =>
      v 0 * v 0 + v 1 * v 1 + v 2 * v 2 + v 3 * v 3
        + 2 * (v 0 * v 1 + v 1 * v 2 + v 2 * v 3)
        + r * ((c * v 4 - v 5) * (c * v 4 - v 5)) = 1).card
      = if r = 1 then 216 else 270 := by
  fin_cases c <;> fin_cases r <;> decide +kernel

theorem gbetaR_scale {M : Mat6} {c r : ZMod 3} (hG : Mᵀ * gram6 * M = gbetaR c r)
    (hMonto : ∀ v : Vec6, v 5 = 0 → ∃ u, M.mulVec u = v) (hM5 : ∀ v, M.mulVec v 5 = 0)
    (hMy : M.mulVec (kY c) = 0) (hMker : ∀ v, M.mulVec v = 0 → ∃ j : ZMod 3, v = j • kY c) :
    r = 1 := by
  have hquad : ∀ v : Vec6, norm6 (M.mulVec v) =
      v 0 * v 0 + v 1 * v 1 + v 2 * v 2 + v 3 * v 3
        + 2 * (v 0 * v 1 + v 1 * v 2 + v 2 * v 3)
        + r * ((c * v 4 - v 5) * (c * v 4 - v 5)) := by
    intro v
    rw [← dot_gbetaR hG v, gbetaR_quad]
  have hAcard := normOne_card hMonto hM5 hMy hMker
  have hAeq : (Finset.univ.filter fun v : Vec6 => norm6 (M.mulVec v) = 1)
      = Finset.univ.filter fun v : Vec6 =>
          v 0 * v 0 + v 1 * v 1 + v 2 * v 2 + v 3 * v 3
            + 2 * (v 0 * v 1 + v 1 * v 2 + v 2 * v 3)
            + r * ((c * v 4 - v 5) * (c * v 4 - v 5)) = 1 := by
    apply Finset.filter_congr
    intro v _
    rw [hquad v]
  have hpc := poly_count c r
  rw [hAeq, hpc] at hAcard
  by_cases hr : r = 1
  · exact hr
  · exfalso
    have h216 : (270 : Nat) = 216 := by simpa [hr] using hAcard
    omega

end E6Dep

end CFSG.StandardType

end
