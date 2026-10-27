module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3SL24ModelNA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3SL24IDAAA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.GH74.KGroups CFSG.Open CFSG.Quasithin CFSG.Quasithin.H
open scoped Matrix

@[expose] def s16h_frobGF4 : GF4 →+* GF4 where
  toFun x := x ^ 2
  map_one' := by decide
  map_mul' := by decide
  map_zero' := by decide
  map_add' := by decide

theorem s16h_orth3Phi_conj (γ : ↥(StatedSL 2 GF4)) :
    orth3Phi * s16h_orth3AutHom γ * orth3Phi⁻¹ =
      s16h_orth3AutHom (s16h_sl24_statedSLMap s16h_frobGF4 γ) := by
  apply MulEquiv.ext
  intro v
  have hinv : ∀ w : Orth3, orth3Phi⁻¹ w = orth3Phi w := fun w => rfl
  have h4 : ∀ x : GF4, (x ^ 2) ^ 2 = x := by decide
  have hadd : ∀ x y : GF4, (x + y) ^ 2 = x ^ 2 + y ^ 2 := by decide
  rw [MulAut.mul_apply, MulAut.mul_apply, hinv, s16h_orth3AutHom_apply, s16h_orth3AutHom_apply]
  apply Multiplicative.toAdd.injective
  have e00 := s16h_sl24_statedSLMap_apply s16h_frobGF4 γ 0 0
  have e01 := s16h_sl24_statedSLMap_apply s16h_frobGF4 γ 0 1
  have e10 := s16h_sl24_statedSLMap_apply s16h_frobGF4 γ 1 0
  have e11 := s16h_sl24_statedSLMap_apply s16h_frobGF4 γ 1 1
  have hphi : ∀ w : Orth3, orth3Phi w = Multiplicative.ofAdd
      ((Multiplicative.toAdd w).1 ^ 2, (Multiplicative.toAdd w).2.1 ^ 2,
        (Multiplicative.toAdd w).2.2 ^ 2) := fun w => rfl
  have hfrob : ∀ x : GF4, s16h_frobGF4 x = x ^ 2 := fun x => rfl
  simp only [hphi, hfrob, orth3Act, e00, e01, e10, e11, toAdd_ofAdd, hadd, mul_pow, h4]

theorem s16h_orth3Phi_mem_normalizer :
    orth3Phi ∈ Subgroup.normalizer (orth3L : Set (MulAut Orth3)) := by
  have hfwd : ∀ σ ∈ orth3L, orth3Phi * σ * orth3Phi⁻¹ ∈ orth3L := by
    intro σ hσ
    rw [s16h_orth3L_eq_range] at hσ ⊢
    obtain ⟨γ, rfl⟩ := hσ
    exact ⟨s16h_sl24_statedSLMap s16h_frobGF4 γ, (s16h_orth3Phi_conj γ).symm⟩
  have hsq : orth3Phi * orth3Phi = 1 := by
    apply MulEquiv.ext
    intro v
    have h4 : ∀ x : GF4, (x ^ 2) ^ 2 = x := by decide
    apply Multiplicative.toAdd.injective
    show ((_ ^ 2) ^ 2, (_ ^ 2) ^ 2, (_ ^ 2) ^ 2) = _
    simp only [h4]
    rfl
  have hinv : orth3Phi⁻¹ = orth3Phi := inv_eq_of_mul_eq_one_right hsq
  rw [Subgroup.mem_normalizer_iff]
  intro σ
  constructor
  · exact hfwd σ
  · intro h
    have h2 := hfwd _ h
    have hsq' : orth3Phi⁻¹ * orth3Phi⁻¹ = 1 := by rw [hinv]; exact hsq
    have h3 : orth3Phi * (orth3Phi * σ * orth3Phi⁻¹) * orth3Phi⁻¹ = σ :=
      calc orth3Phi * (orth3Phi * σ * orth3Phi⁻¹) * orth3Phi⁻¹
          = (orth3Phi * orth3Phi) * σ * (orth3Phi⁻¹ * orth3Phi⁻¹) := by group
        _ = σ := by rw [hsq, hsq', one_mul, mul_one]
    rwa [h3] at h2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
