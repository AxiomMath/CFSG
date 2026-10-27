module

public import CFSG.Quasithin.Vol2.Ch6H11Main

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatOm4mA.HermCoords

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NatOm4mA

open CFSG.Quasithin (IsElemAbelian2 frobPow)
open CFSG.Quasithin.JonesParshall (sig)
open CFSG.Quasithin.H13.H11P (Mat uu coe_uu coe_slFieldAut mapMatrix_uu card_eq_two_mul)
open CFSG.Quasithin.H13.H11M (VH LH UH NH FormS rhoH rhoH_injective SigInv hm sigE sigE_apply
  mapMatrix_sigE conj_of_form mem_LH_or_formS mul_mem_LH_of_formS)
open CFSG.RankThree.PartOne.KCRootAxis (SL₂ slFieldAut)

open scoped Matrix

variable {F : Type} [Field F] [CharP F 2] {a : ℕ} (hσ : SigInv a F)

include hσ in
private theorem formS_conj_uu_A05 {f : MulAut (VH a F)} {M : SL₂ F} (hf : FormS f M) {t : F}
    (ht : f * rhoH hσ (uu t) = rhoH hσ (uu t) * f) :
    M * slFieldAut F (sigE hσ) (uu t) = uu t * M := by
  have hx : ∀ v, hm (f v) = (1 : F) • ((M : Mat F) * (sigE hσ).mapMatrix (hm v) *
      (frobPow a (M : Mat F))ᵀ) := fun v => by
    rw [hf.2 v, one_smul, mapMatrix_sigE]
  have hconj := conj_of_form hσ hx (uu t)
  have ht' : f * rhoH hσ (uu t) * f⁻¹ = rhoH hσ (uu t) := by
    rw [ht, mul_assoc, mul_inv_cancel, mul_one]
  rw [ht'] at hconj
  have heq : uu t = M * slFieldAut F (sigE hσ) (uu t) * M⁻¹ := rhoH_injective hσ hconj
  calc M * slFieldAut F (sigE hσ) (uu t)
      = (M * slFieldAut F (sigE hσ) (uu t) * M⁻¹) * M := by group
    _ = uu t * M := by rw [← heq]

include hσ in
private theorem formS_conj_uu_mat_A05 {f : MulAut (VH a F)} {M : SL₂ F} (hf : FormS f M)
    {t : F} (ht : f * rhoH hσ (uu t) = rhoH hσ (uu t) * f) :
    (M : Mat F) * !![1, sig a t; (0 : F), 1] = !![1, t; (0 : F), 1] * (M : Mat F) := by
  have hslmat : ((slFieldAut F (sigE hσ) (uu t) : SL₂ F) : Mat F) =
      !![1, sig a t; (0 : F), 1] := by
    rw [coe_slFieldAut, mapMatrix_uu, sigE_apply hσ, coe_uu]
  have hh := congrArg (fun g : SL₂ F => (g : Mat F)) (formS_conj_uu_A05 hσ hf ht)
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at hh
  rwa [hslmat, coe_uu] at hh

theorem formS_comm_collinear {f : MulAut (VH a F)} {M : SL₂ F} (hf : FormS f M) {s₀ s : F}
    (hs₀ : s₀ ≠ 0) (h₀ : f * rhoH hσ (uu s₀) = rhoH hσ (uu s₀) * f)
    (h : f * rhoH hσ (uu s) = rhoH hσ (uu s) * f) : s * sig a s₀ = sig a s * s₀ := by
  have h0 := formS_conj_uu_mat_A05 hσ hf h₀
  have hs := formS_conj_uu_mat_A05 hσ hf h
  have h00 := congrFun (congrFun h0 0) 0
  have h01 := congrFun (congrFun h0 0) 1
  have h00' := congrFun (congrFun hs 0) 0
  have h01' := congrFun (congrFun hs 0) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    one_mul, mul_one, zero_mul, mul_zero, add_zero, zero_add] at h00 h01 h00' h01'
  have hM10 : (M : Mat F) 1 0 = 0 := by
    have hz : s₀ * (M : Mat F) 1 0 = 0 := by linear_combination -h00
    exact (mul_eq_zero.mp hz).resolve_left hs₀
  have hrel0 : (M : Mat F) 0 0 * sig a s₀ = s₀ * (M : Mat F) 1 1 := by
    linear_combination h01
  have hrel : (M : Mat F) 0 0 * sig a s = s * (M : Mat F) 1 1 := by
    linear_combination h01'
  have hM00 : (M : Mat F) 0 0 ≠ 0 := by
    have hdet : (M : Mat F) 0 0 * (M : Mat F) 1 1 = 1 := by
      have h := M.2
      rw [Matrix.det_fin_two, hM10, mul_zero, sub_zero] at h
      exact h
    exact left_ne_zero_of_mul_eq_one hdet
  have hcoll : (M : Mat F) 0 0 * (sig a s * s₀ - sig a s₀ * s) = 0 := by
    linear_combination s₀ * hrel - s * hrel0
  rcases mul_eq_zero.mp hcoll with h | h
  · exact absurd h hM00
  · have : sig a s * s₀ = sig a s₀ * s := sub_eq_zero.mp h
    rw [this]
    ring

theorem card_inf_LH_le [Fintype F] (ha : 1 ≤ a) (hF : Fintype.card F = 2 ^ (2 * a))
    {A : Subgroup (MulAut (VH a F))} (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hstd : A ⊓ LH hσ ≤ UH hσ) {f : MulAut (VH a F)} (hfA : f ∈ A) {M : SL₂ F}
    (hf : FormS f M) : Nat.card ↥(A ⊓ LH hσ) ≤ 2 ^ a := by
  by_cases hB1 : A ⊓ LH hσ = ⊥
  · rw [hB1, Subgroup.card_bot]
    exact Nat.one_le_two_pow
  · obtain ⟨s₀, hs₀W, hs₀0⟩ := exists_ne_zero_mem_Ws hσ hstd hB1
    refine card_le_of_collinear hσ ha hF hstd hs₀0 ?_
    intro s hs
    exact formS_comm_collinear hσ hf hs₀0 (hA f hfA _ hs₀W.1) (hA f hfA _ hs.1)

theorem card_eq_two_mul_inf_LH [Fintype F] (ha : 1 ≤ a) (hF : Fintype.card F = 2 ^ (2 * a))
    {θ₀ : F} (hθ₀ : sig a θ₀ ≠ θ₀) {A : Subgroup (MulAut (VH a F))} (hAN : A ≤ NH hσ)
    (hA : IsElemAbelian2 A) {f : MulAut (VH a F)} (hfA : f ∈ A) (hfL : f ∉ LH hσ) :
    Nat.card A = 2 * Nat.card ↥(A ⊓ LH hσ) := by
  have hsq : ∀ x ∈ A, x * x = 1 := fun x hx => by rw [← sq]; exact hA.2 x hx
  have hform : ∀ x ∈ A, x ∉ LH hσ → ∃ M, FormS x M := fun x hx hxL =>
    (mem_LH_or_formS hσ ha hF hθ₀ (hAN hx) (hsq x hx)).resolve_left hxL
  obtain ⟨Mf, hMf⟩ := hform f hfA hfL
  have hfB : f ∉ A ⊓ LH hσ := fun h => hfL h.2
  have hout : ∀ g ∈ A, g ∉ A ⊓ LH hσ → f * g ∈ A ⊓ LH hσ := by
    intro g hg hgB
    obtain ⟨Mg, hMg⟩ := hform g hg (fun h => hgB ⟨hg, h⟩)
    exact ⟨A.mul_mem hfA hg, mul_mem_LH_of_formS hσ hMf hMg⟩
  exact card_eq_two_mul inf_le_left hfA hfB (fun g hg => hA.1 f hfA g hg) hout

end CFSG.LocalAnalysis.UniquenessCase.UC22.NatOm4mA
