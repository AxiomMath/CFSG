module

public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoModel
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviHom
public import CFSG.LocalAnalysis.StandardType.FF81.CentE6.Std
import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviKer

public section

namespace CFSG.StandardType.FF81.CentE6

open scoped MatrixGroups
open CFSG CFSG.SeitzReduction CFSG.StandardType.GGSixE6Two CFSG.StandardType.GGHalf
  CFSG.Timmesfeld.LieEmbed

theorem exists_lE_mulEquiv :
    ∃ eL : ↥lE ≃* SL(6, ZMod 2), ∀ i j : Fin 6, i ≠ j →
      ∃ h : xr (a5Root i j) ∈ lE, eL ⟨xr (a5Root i j), h⟩ = elem i j := by
  classical
  have hcard : Nat.card F2 = 2 := by
    simpa using GaloisField.card 2 1 (by omega)
  have hcenter : Subgroup.center (Matrix.SpecialLinearGroup (Fin 6) F2) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    have : Fintype F2 := Fintype.ofFinite F2
    obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hz
    have h2 := FiniteField.pow_card (K := F2) r
    rw [← Nat.card_eq_fintype_card, hcard, sq] at h2
    have hr1 : r = 1 := by
      have hr0 : r ≠ 0 := by
        rintro rfl
        rw [Fintype.card_fin, zero_pow (by norm_num)] at hr
        exact zero_ne_one hr
      exact mul_left_cancel₀ hr0 (h2.trans (mul_one r).symm)
    apply Subtype.ext
    rw [← hrz, hr1]
    simp
  have hinj : Function.Injective (E6Pilot.slToAdjointE6 F2) := by
    rw [← MonoidHom.ker_eq_bot_iff, E6Pilot.ker_slToAdjointE6, hcenter]
  have hrange : (E6Pilot.slToAdjointE6 F2).range = lE := E6Pilot.range_slToAdjointE6
  let e1 : Matrix.SpecialLinearGroup (Fin 6) F2 ≃* ↥lE :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  let eF : F2 ≃+* ZMod 2 := (GaloisField.equivZmodP 2).toRingEquiv
  let eSL : Matrix.SpecialLinearGroup (Fin 6) F2 ≃*
      Matrix.SpecialLinearGroup (Fin 6) (ZMod 2) :=
    MonoidHom.toMulEquiv
      (Matrix.SpecialLinearGroup.map eF.toRingHom)
      (Matrix.SpecialLinearGroup.map eF.symm.toRingHom)
      (by
        apply MonoidHom.ext
        intro A
        apply Matrix.SpecialLinearGroup.ext
        intro i j
        simp [Matrix.SpecialLinearGroup.map_apply_coe])
      (by
        apply MonoidHom.ext
        intro A
        apply Matrix.SpecialLinearGroup.ext
        intro i j
        simp [Matrix.SpecialLinearGroup.map_apply_coe])
  refine ⟨e1.symm.trans eSL, ?_⟩
  intro i j hij
  have hx : xr (a5Root i j) =
      E6Pilot.slToAdjointE6 F2 (Matrix.SpecialLinearGroup.transvection hij (1 : F2)) := by
    rw [xr, ← E6Pilot.slToAdjointE6_transvection hij (1 : F2)]
  have hmem : xr (a5Root i j) ∈ lE := by
    rw [hx]
    exact E6Pilot.slToAdjointE6_mem_a5Levi _
  refine ⟨hmem, ?_⟩
  have hA : e1 (Matrix.SpecialLinearGroup.transvection hij (1 : F2)) =
      ⟨xr (a5Root i j), hmem⟩ := by
    apply Subtype.ext
    simp only [e1, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
      MonoidHom.ofInjective_apply]
    simpa [xr] using E6Pilot.slToAdjointE6_transvection hij (1 : F2)
  have hsymm : e1.symm ⟨xr (a5Root i j), hmem⟩ =
      Matrix.SpecialLinearGroup.transvection hij (1 : F2) := by
    rw [← hA, MulEquiv.symm_apply_apply]
  rw [MulEquiv.trans_apply, hsymm]
  show Matrix.SpecialLinearGroup.map eF.toRingHom
      (Matrix.SpecialLinearGroup.transvection hij (1 : F2)) = elem i j
  rw [Matrix.SpecialLinearGroup.map_transvection, map_one]
  rw [elem, dif_neg hij]

end CFSG.StandardType.FF81.CentE6
