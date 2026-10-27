module

public import CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Bridge
public import CFSG.LinearAlgebra.LinearGroups.Generation
import all CFSG.Fischer.F4
public import CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Stab

public section

namespace CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Elem

open CFSG.Fischer CFSG.RankThree.PartTwo.Sec10.KS1012GL34
open CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Light CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Bridge

@[expose]
def InM (H : Subgroup (Matrix.GeneralLinearGroup (Fin 3) F4)) (M : Matrix (Fin 3) (Fin 3) F4) :
    Prop :=
  ∃ g ∈ H, (g : Matrix (Fin 3) (Fin 3) F4) = M

theorem InM_one (H : Subgroup (Matrix.GeneralLinearGroup (Fin 3) F4)) : InM H 1 :=
  ⟨1, H.one_mem, Units.val_one⟩

theorem InM_mul {H : Subgroup (Matrix.GeneralLinearGroup (Fin 3) F4)}
    {A B : Matrix (Fin 3) (Fin 3) F4} (hA : InM H A) (hB : InM H B) : InM H (A * B) := by
  obtain ⟨g, hg, rfl⟩ := hA
  obtain ⟨h, hh, rfl⟩ := hB
  exact ⟨g * h, H.mul_mem hg hh, Units.val_mul g h⟩

theorem conj_elemM : ∀ (i j : Fin 3) (c : F4),
    Xd * elemM i j c * Xd2 = elemM i j (c * (Xd i i * Xd2 j j)) := by
  decide

theorem Xd_scalar_ne : ∀ i j : Fin 3, i ≠ j → Xd i i * Xd2 j j ≠ 0 ∧ Xd i i * Xd2 j j ≠ 1 := by
  decide

theorem F4_cover : ∀ d c : F4, d ≠ 0 → d ≠ 1 → c = 0 ∨ c = 1 ∨ c = d ∨ c = d * d := by
  decide

theorem elem_all_of_one {H : Subgroup (Matrix.GeneralLinearGroup (Fin 3) F4)}
    (hX : InM H Xd) (hX2 : InM H Xd2) {i j : Fin 3} (hij : i ≠ j)
    (h1 : InM H (elemM i j 1)) : ∀ c : F4, InM H (elemM i j c) := by
  have hconj : ∀ e : F4, InM H (elemM i j e) →
      InM H (elemM i j (e * (Xd i i * Xd2 j j))) := by
    intro e he
    have h := InM_mul (InM_mul hX he) hX2
    rw [conj_elemM] at h
    exact h
  have h2 : InM H (elemM i j (Xd i i * Xd2 j j)) := by
    have := hconj 1 h1
    rwa [one_mul] at this
  have h3 : InM H (elemM i j (Xd i i * Xd2 j j * (Xd i i * Xd2 j j))) := hconj _ h2
  obtain ⟨hd0, hd1⟩ := Xd_scalar_ne i j hij
  intro c
  rcases F4_cover _ c hd0 hd1 with rfl | rfl | rfl | rfl
  · have h0 : elemM i j 0 = 1 := by simp [elemM]
    rw [h0]; exact InM_one H
  · exact h1
  · exact h2
  · exact h3

theorem SLsub_le_of_E {H : Subgroup (Matrix.GeneralLinearGroup (Fin 3) F4)}
    (hE : ∀ (i j : Fin 3), i ≠ j → ∀ c : F4, InM H (elemM i j c)) : SLsub ≤ H := by
  intro g hg
  have hdet : (g : Matrix (Fin 3) (Fin 3) F4).det = 1 := hg
  have hgen : ∀ x ∈ CFSG.LinearGroups.elementarySet 3 F4,
      Matrix.SpecialLinearGroup.toGL x ∈ H := by
    rintro x ⟨i, j, hij, c, rfl⟩
    obtain ⟨h, hh, hval⟩ := hE i j hij c
    have heq : Matrix.SpecialLinearGroup.toGL
        (Matrix.SpecialLinearGroup.transvection hij c) = h :=
      Units.ext (Eq.trans rfl hval.symm)
    rw [heq]
    exact hh
  have hcl : Subgroup.closure (CFSG.LinearGroups.elementarySet 3 F4) ≤
      H.comap (Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin 3) F4 →* Matrix.GeneralLinearGroup (Fin 3) F4) := by
    rw [Subgroup.closure_le]
    exact hgen
  let s : Matrix.SpecialLinearGroup (Fin 3) F4 := ⟨(g : Matrix (Fin 3) (Fin 3) F4), hdet⟩
  have hs : s ∈ Subgroup.closure (CFSG.LinearGroups.elementarySet 3 F4) := by
    rw [CFSG.LinearGroups.special_linear_elementary_generation (n := 3) (K := F4)]
    exact Subgroup.mem_top s
  have hsg : Matrix.SpecialLinearGroup.toGL s = g := Units.ext rfl
  have hmem := hcl hs
  rw [Subgroup.mem_comap, hsg] at hmem
  exact hmem

theorem det_Xd : (Xd).det = 1 := by
  rw [← toMat_XdL, det_toMat]
  decide

theorem det_Wm1 : (Wm 1).det = 1 := by
  rw [← toMat_WmL, det_toMat]
  decide

theorem det_Zs : (Zs).det = 1 := by
  rw [← toMat_ZsL, det_toMat]
  decide

theorem stab_Xd : ∀ i : Fin 6, stabilizes i Xd := by decide

theorem stab_Wm1 : ∀ i : Fin 6, stabilizes i (Wm 1) := by decide

theorem stab_Zs : ∀ i : Fin 6, stabilizes i Zs := by decide

@[expose] noncomputable def unitOfDet1 (M : Matrix (Fin 3) (Fin 3) F4) (h : M.det = 1) :
    Matrix.GeneralLinearGroup (Fin 3) F4 :=
  Units.mk M M⁻¹ (Matrix.mul_nonsing_inv M (by rw [h]; exact isUnit_one))
    (Matrix.nonsing_inv_mul M (by rw [h]; exact isUnit_one))

theorem coe_unitOfDet1 (M : Matrix (Fin 3) (Fin 3) F4) (h : M.det = 1) :
    (unitOfDet1 M h : Matrix (Fin 3) (Fin 3) F4) = M :=
  rfl

theorem InM_of_P {H : Subgroup (Matrix.GeneralLinearGroup (Fin 3) F4)} {i : Fin 6}
    (hP : P i ≤ H) {M : Matrix (Fin 3) (Fin 3) F4} (hdet : M.det = 1) (hs : stabilizes i M) :
    InM H M := by
  have hg : unitOfDet1 M hdet ∈ P i :=
    mem_P.2 ⟨by rw [coe_unitOfDet1]; exact hdet, by rw [coe_unitOfDet1]; exact hs⟩
  exact ⟨unitOfDet1 M hdet, hP hg, coe_unitOfDet1 M hdet⟩

theorem stabilizes_inv_mul {i : Fin 6} {A R : Matrix (Fin 3) (Fin 3) F4} (hR : R.det = 1)
    (h : ∀ v ∈ Omega i, ∃ u ∈ Omega i, ∃ c : F4, c ≠ 0 ∧
      Matrix.mulVec A v = c • Matrix.mulVec R u) :
    stabilizes i (R⁻¹ * A) := by
  have hu : IsUnit R.det := by rw [hR]; exact isUnit_one
  intro v hv
  obtain ⟨u, hu', c, hc, hAv⟩ := h v hv
  refine ⟨u, hu', c, hc, ?_⟩
  rw [← Matrix.mulVec_mulVec, hAv, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul R hu, Matrix.one_mulVec]

theorem SLsub_le_of_words {H : Subgroup (Matrix.GeneralLinearGroup (Fin 3) F4)}
    (hX : InM H Xd) (hX2 : InM H Xd2)
    (h01 : InM H (elemM 0 1 1)) (h02 : InM H (elemM 0 2 1)) (h10 : InM H (elemM 1 0 1))
    (h12 : InM H (elemM 1 2 1)) (h20 : InM H (elemM 2 0 1)) (h21 : InM H (elemM 2 1 1)) :
    SLsub ≤ H := by
  apply SLsub_le_of_E
  intro i j hij c
  fin_cases i <;> fin_cases j <;>
    first
    | exact absurd rfl hij
    | exact elem_all_of_one hX hX2 (by decide) h01 c
    | exact elem_all_of_one hX hX2 (by decide) h02 c
    | exact elem_all_of_one hX hX2 (by decide) h10 c
    | exact elem_all_of_one hX hX2 (by decide) h12 c
    | exact elem_all_of_one hX hX2 (by decide) h20 c
    | exact elem_all_of_one hX hX2 (by decide) h21 c

end CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Elem

end
