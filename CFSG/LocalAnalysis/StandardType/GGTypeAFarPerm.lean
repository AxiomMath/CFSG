module

public import CFSG.LocalAnalysis.StandardType.GGTypeACompatFarCore
public import CFSG.LocalAnalysis.StandardType.GGPresentationWeyl

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal.SpecialLinear Matrix

section Perm

variable {F : Type} [Field F]

theorem signedPerm_one_eq_permMatrix {m : ℕ} (π : Equiv.Perm (Fin m)) :
    signedPerm π (1 : Fin m → F) = (π⁻¹).permMatrix F := by
  ext r s
  simp [signedPerm_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
  simp only [Equiv.symm_apply_eq]

theorem det_signedPerm_one (h2 : (2 : F) = 0) {m : ℕ} (π : Equiv.Perm (Fin m)) :
    (signedPerm π (1 : Fin m → F)).det = 1 := by
  rw [signedPerm_one_eq_permMatrix, Matrix.det_permutation]
  rcases Int.units_eq_one_or (Equiv.Perm.sign π⁻¹) with h | h
  · rw [h]; simp
  · rw [h]
    simp
    linear_combination -h2

@[expose] noncomputable def slPerm (h2 : (2 : F) = 0) {m : ℕ} :
    Equiv.Perm (Fin m) →* SpecialLinearGroup (Fin m) F where
  toFun π := ⟨signedPerm π 1, det_signedPerm_one h2 π⟩
  map_one' := Subtype.ext (by
    change signedPerm (1 : Equiv.Perm (Fin m)) (1 : Fin m → F) = 1
    rw [signedPerm_one]
    simp)
  map_mul' π π' := Subtype.ext (by
    change signedPerm (π * π') (1 : Fin m → F) = signedPerm π 1 * signedPerm π' 1
    rw [signedPerm_mul_signedPerm]
    congr 1
    funext s
    simp)

theorem coe_slPerm (h2 : (2 : F) = 0) {m : ℕ} (π : Equiv.Perm (Fin m)) :
    ((slPerm h2 π : SpecialLinearGroup (Fin m) F) : Matrix (Fin m) (Fin m) F) =
      signedPerm π 1 :=
  rfl

theorem slPerm_swap_castSucc_succ (h2 : (2 : F) = 0) {m : ℕ} (k : Fin m) :
    slPerm h2 (Equiv.swap k.castSucc k.succ) = weylRep m F k := by
  apply Subtype.ext
  rw [coe_slPerm, coe_weylRep_of_two m h2 k]

theorem slPerm_mul_ggDiagConj (h2 : (2 : F) = 0) {m : ℕ} (π : Equiv.Perm (Fin m))
    (h : Fin m → Fˣ) (s : SpecialLinearGroup (Fin m) F) :
    slPerm h2 π * ggDiagConj h s * (slPerm h2 π)⁻¹ =
      ggDiagConj (h ∘ π.symm) (slPerm h2 π * s * (slPerm h2 π)⁻¹) := by
  have e : (MulAut.conj (slPerm h2 π)).toMonoidHom.comp (ggDiagConj h) =
      (ggDiagConj (h ∘ π.symm)).comp (MulAut.conj (slPerm h2 π)).toMonoidHom := by
    refine MonoidHom.eq_of_eqOn_dense
      (SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field (ι := Fin m)
        (K := F)) ?_
    rintro _ ⟨⟨a, b, hab, c⟩, rfl⟩
    simp only [TransvectionStruct.toSpecialLinearGroup_mk, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [conj_transvection_of_coe_eq_signedPerm (coe_slPerm h2 π) (fun s => by simp) hab c]
    simp only [Pi.one_apply, one_mul]
    rw [ggDiagConj_transvection h hab c,
      conj_transvection_of_coe_eq_signedPerm (coe_slPerm h2 π) (fun s => by simp) hab
        (h a * c * (h b)⁻¹),
      ggDiagConj_transvection (h ∘ π.symm) (π.injective.ne hab) c]
    congr 1
    simp only [Function.comp_apply, Equiv.symm_apply_apply, Pi.one_apply, mul_one, one_mul]
  simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using
    DFunLike.congr_fun e s

theorem slPerm_swap_eq_transvections (h2 : (2 : F) = 0) {m : ℕ} {i j : Fin m} (hij : i ≠ j) :
    slPerm h2 (Equiv.swap i j) =
      SpecialLinearGroup.transvection hij 1 * SpecialLinearGroup.transvection hij.symm 1 *
        SpecialLinearGroup.transvection hij 1 := by
  have hneg : (-1 : F) = 1 := by linear_combination -h2
  have ht : (SpecialLinearGroup.transvection hij.symm 1 : SpecialLinearGroup (Fin m) F) =
      SpecialLinearGroup.transvection hij.symm (-1) := by
    congr 1
    exact hneg.symm
  apply Subtype.ext
  rw [coe_slPerm, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, ht]
  rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul,
    coe_transvection_mul_transvection_mul_transvection hij, weylMatrix]
  congr 1
  funext r
  exact (eq_one_of_mul_self_of_two h2 (weylSign_mul_self i r)).symm

theorem slLowerBlockHom_slPerm_swap (h2 : (2 : F) = 0) {n : ℕ} (i j : Fin n) :
    slLowerBlockHom n F (slPerm h2 (Equiv.swap i j)) = slPerm h2 (Equiv.swap i.succ j.succ) := by
  by_cases hij : i = j
  · subst j
    rw [Equiv.swap_self, Equiv.swap_self]
    change slLowerBlockHom n F (slPerm h2 (1 : Equiv.Perm (Fin n))) =
      slPerm h2 (1 : Equiv.Perm (Fin (n + 1)))
    simp only [map_one]
  · have hij' : i.succ ≠ j.succ := (Fin.succ_injective n).ne hij
    rw [slPerm_swap_eq_transvections h2 hij, slPerm_swap_eq_transvections h2 hij']
    simp only [map_mul, slLowerBlockHom_transvection]

theorem slUpperBlockHom_slPerm_swap (h2 : (2 : F) = 0) {n : ℕ} (i j : Fin n) :
    slUpperBlockHom n F (slPerm h2 (Equiv.swap i j)) =
      slPerm h2 (Equiv.swap i.castSucc j.castSucc) := by
  by_cases hij : i = j
  · subst j
    rw [Equiv.swap_self, Equiv.swap_self]
    change slUpperBlockHom n F (slPerm h2 (1 : Equiv.Perm (Fin n))) =
      slPerm h2 (1 : Equiv.Perm (Fin (n + 1)))
    simp only [map_one]
  · have hij' : i.castSucc ≠ j.castSucc := (Fin.castSucc_injective n).ne hij
    rw [slPerm_swap_eq_transvections h2 hij, slPerm_swap_eq_transvections h2 hij']
    simp only [map_mul, slUpperBlockHom_transvection]

theorem slPerm_conj_transvection_of_fixed (h2 : (2 : F) = 0) {m : ℕ} {π : Equiv.Perm (Fin m)}
    {x y : Fin m} (hx : π x = x) (hy : π y = y) (hxy : x ≠ y) (c : F) :
    slPerm h2 π * SpecialLinearGroup.transvection hxy c * (slPerm h2 π)⁻¹ =
      SpecialLinearGroup.transvection hxy c := by
  rw [conj_transvection_of_coe_eq_signedPerm (coe_slPerm h2 π) (fun s => by simp) hxy c]
  simp only [Pi.one_apply, mul_one, one_mul]
  apply Subtype.ext
  rw [SpecialLinearGroup.transvection_coe, SpecialLinearGroup.transvection_coe, hx, hy]

theorem slPerm_swap_zero_one_commute_lowerLower (h2 : (2 : F) = 0) {m : ℕ}
    (s : SpecialLinearGroup (Fin m) F) :
    slPerm h2 (Equiv.swap (0 : Fin (m + 1 + 1)) (0 : Fin (m + 1)).succ) *
        slLowerBlockHom (m + 1) F (slLowerBlockHom m F s) =
      slLowerBlockHom (m + 1) F (slLowerBlockHom m F s) *
        slPerm h2 (Equiv.swap (0 : Fin (m + 1 + 1)) (0 : Fin (m + 1)).succ) := by
  rw [← mul_inv_eq_iff_eq_mul]
  have e : (MulAut.conj
        (slPerm h2 (Equiv.swap (0 : Fin (m + 1 + 1)) (0 : Fin (m + 1)).succ))).toMonoidHom.comp
        ((slLowerBlockHom (m + 1) F).comp (slLowerBlockHom m F)) =
      (slLowerBlockHom (m + 1) F).comp (slLowerBlockHom m F) := by
    refine MonoidHom.eq_of_eqOn_dense
      (SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field (ι := Fin m)
        (K := F)) ?_
    rintro _ ⟨⟨a, b, hab, c⟩, rfl⟩
    simp only [TransvectionStruct.toSpecialLinearGroup_mk, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [slLowerBlockHom_transvection hab c,
      slLowerBlockHom_transvection ((Fin.succ_injective m).ne hab) c]
    exact slPerm_conj_transvection_of_fixed h2
      (by rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero a.succ)
        (by simpa using Fin.succ_succ_ne_one a)])
      (by rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero b.succ)
        (by simpa using Fin.succ_succ_ne_one b)])
      ((Fin.succ_injective (m + 1)).ne ((Fin.succ_injective m).ne hab)) c
  simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using
    DFunLike.congr_fun e s

theorem slPerm_swap_zero_last_commute_upperLower (h2 : (2 : F) = 0) {m : ℕ}
    (s : SpecialLinearGroup (Fin m) F) :
    slPerm h2 (Equiv.swap (0 : Fin (m + 1 + 1)) (Fin.last (m + 1))) *
        slUpperBlockHom (m + 1) F (slLowerBlockHom m F s) =
      slUpperBlockHom (m + 1) F (slLowerBlockHom m F s) *
        slPerm h2 (Equiv.swap (0 : Fin (m + 1 + 1)) (Fin.last (m + 1))) := by
  rw [← mul_inv_eq_iff_eq_mul]
  have e : (MulAut.conj
        (slPerm h2 (Equiv.swap (0 : Fin (m + 1 + 1)) (Fin.last (m + 1))))).toMonoidHom.comp
        ((slUpperBlockHom (m + 1) F).comp (slLowerBlockHom m F)) =
      (slUpperBlockHom (m + 1) F).comp (slLowerBlockHom m F) := by
    refine MonoidHom.eq_of_eqOn_dense
      (SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field (ι := Fin m)
        (K := F)) ?_
    rintro _ ⟨⟨a, b, hab, c⟩, rfl⟩
    simp only [TransvectionStruct.toSpecialLinearGroup_mk, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [slLowerBlockHom_transvection hab c,
      slUpperBlockHom_transvection ((Fin.succ_injective m).ne hab) c]
    exact slPerm_conj_transvection_of_fixed h2
      (by rw [Equiv.swap_apply_of_ne_of_ne (by simp) (Fin.castSucc_ne_last a.succ)])
      (by rw [Equiv.swap_apply_of_ne_of_ne (by simp) (Fin.castSucc_ne_last b.succ)])
      ((Fin.castSucc_injective (m + 1)).ne ((Fin.succ_injective m).ne hab)) c
  simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using
    DFunLike.congr_fun e s

end Perm

end CFSG.StandardType
