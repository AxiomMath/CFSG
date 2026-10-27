module

public import CFSG.LocalAnalysis.StandardType.GGSixA6RedDefs
public import CFSG.LocalAnalysis.StandardType.GGLinearFusionCyclic
public import CFSG.LocalAnalysis.StandardType.GGRankOneSl2

public section

namespace CFSG.StandardType.A6Red

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

section Genuine

private theorem ggA6_transvection_fin_two_zero_one {F : Type} [Field F] (t : F) :
    Matrix.SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) (by decide) t =
      CFSG.LieType.Steinberg.sl2Upper t := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.SpecialLinearGroup.transvection_coe,
      CFSG.LieType.Steinberg.coe_sl2Upper, Matrix.single_apply]

private theorem ggA6_transvection_fin_two_one_zero {F : Type} [Field F] (t : F) :
    Matrix.SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0) (by decide) t =
      CFSG.LieType.Steinberg.sl2Lower t := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.SpecialLinearGroup.transvection_coe,
      CFSG.LieType.Steinberg.coe_sl2Lower, Matrix.single_apply]

private theorem injective_of_ker_le_center_sl2 {F : Type} [Field F] [CharP F 2]
    {X : Type} [Group X] (ψ : Matrix.SpecialLinearGroup (Fin 2) F →* X)
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) :
    Function.Injective ψ := by
  rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
  intro u hu
  exact PsiDiag.sl2_eq_one_of_mem_center (hker hu)

private theorem exists_conj_eq_conjSL_one {F : Type} [Field F] [Finite F] [CharP F 2]
    {X : Type} [Group X] (ψ : Matrix.SpecialLinearGroup (Fin 2) F →* X)
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) {x : X}
    {χ : Fin 2 → Fin 2 → F}
    (hχ : ∀ (i j : Fin 2) (hij : i ≠ j) (t : F),
      x⁻¹ * ψ (Matrix.SpecialLinearGroup.transvection hij t) * x =
        ψ (Matrix.SpecialLinearGroup.transvection hij (χ i j * t))) :
    ∃ D : GL (Fin 2) F, ∀ u, x⁻¹ * ψ u * x = ψ (InnerDiagA.conjSL D u) := by
  let β : Matrix.SpecialLinearGroup (Fin 2) F →* X :=
    (MulAut.conj x⁻¹).toMonoidHom.comp ψ
  have hβ : ∀ u, β u = x⁻¹ * ψ u * x := fun u => by simp [β]
  have hχ' : ∀ (i j : Fin 2) (hij : i ≠ j) (t : F),
      β (Matrix.SpecialLinearGroup.transvection hij t) =
        ψ (Matrix.SpecialLinearGroup.transvection hij (χ i j * t)) :=
    fun i j hij t => (hβ _).trans (hχ i j hij t)
  have hne : ∀ i j : Fin 2, i ≠ j → χ i j ≠ 0 := by
    intro i j hij h0
    have h1 := hχ i j hij 1
    rw [h0, zero_mul, Matrix.SpecialLinearGroup.transvection_coeff_zero, map_one] at h1
    have h2 : ψ (Matrix.SpecialLinearGroup.transvection hij 1) = 1 := by
      calc ψ (Matrix.SpecialLinearGroup.transvection hij 1)
          = x * (x⁻¹ * ψ (Matrix.SpecialLinearGroup.transvection hij 1) * x) * x⁻¹ := by group
        _ = 1 := by rw [h1]; group
    exact one_ne_zero (InnerDiagA.eq_zero_of_transvection_mem_center hij (hker h2))
  have hψ : Function.Injective ψ := injective_of_ker_le_center_sl2 ψ hker
  have hs : χ 0 1 * χ 1 0 = 1 := by
    refine PsiDiagChar.mul_eq_one_of_conj_sl2 (d := x) ψ hψ
      (Units.mk0 (χ 0 1) (hne 0 1 (by decide))) (χ' := χ 1 0) ?_ ?_
    · intro c
      rw [← ggA6_transvection_fin_two_zero_one c, Units.val_mk0,
        ← ggA6_transvection_fin_two_zero_one (χ 0 1 * c)]
      exact hχ 0 1 (by decide) c
    · intro c
      rw [← ggA6_transvection_fin_two_one_zero c, ← ggA6_transvection_fin_two_one_zero (χ 1 0 * c)]
      exact hχ 1 0 (by decide) c
  have hχ10 : χ 1 0 = (χ 0 1)⁻¹ := eq_inv_of_mul_eq_one_right hs
  let d : Fin 2 → Fˣ := fun i => if i = 0 then Units.mk0 (χ 0 1) (hne 0 1 (by decide)) else 1
  have hd0 : (d 0 : F) = χ 0 1 := by simp [d]
  have hd1 : (d 1 : F) = 1 := by simp [d]
  refine ⟨InnerDiagA.diagGL d, fun u => ?_⟩
  have hβψ : β = ψ.comp (InnerDiagA.conjSL (InnerDiagA.diagGL d)) := by
    refine MonoidHom.eq_of_eqOn_dense
      (CFSG.StandardType.RankOneXfer.closure_sl2Upper_sl2Lower_eq_top (k := F)) ?_
    intro u hu
    rcases hu with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · rw [← ggA6_transvection_fin_two_zero_one c, hχ' 0 1 (by decide) c, MonoidHom.comp_apply,
        InnerDiagA.conjSL_diagGL_transvection]
      congr 1
      rw [hd0, Units.val_inv_eq_inv_val, hd1, inv_one, mul_one]
    · rw [← ggA6_transvection_fin_two_one_zero c, hχ' 1 0 (by decide) c, MonoidHom.comp_apply,
        InnerDiagA.conjSL_diagGL_transvection]
      congr 1
      rw [hd1, Units.val_inv_eq_inv_val, hd0, ← hχ10, one_mul]
      ring_nf
  rw [← hβ, hβψ, MonoidHom.comp_apply]

private theorem exists_mem_ggInducedPairs_one {F : Type} [Field F] [Finite F] [CharP F 2]
    {X : Type} [Group X] (ψ : Matrix.SpecialLinearGroup (Fin 2) F →* X)
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) {y : X}
    (hy : GGPsiInnerDiag (SpecialLinear.rootDatum 1 F) ψ y⁻¹) :
    ∃ A : GL (Fin 2) F, (y, A) ∈ LinFusion.ggInducedPairs ψ := by
  obtain ⟨g, hg, χ, hχ⟩ :=
    InnerDiagA.exists_chi_of_ggPsiInnerDiag (m := 1) (F := F) ψ hy
  obtain ⟨s, rfl⟩ := hg
  obtain ⟨D, hD⟩ := exists_conj_eq_conjSL_one ψ hker hχ
  refine ⟨Matrix.SpecialLinearGroup.toGL s * D, fun u => ?_⟩
  rw [LinFusion.conjSL_toGL_mul, map_mul, map_mul, map_inv, ← hD u]
  group

theorem ggA6_psl_rank_one
    {f : ℕ} {X : Type} [Group X]
    (ψ : (ggU .PSL 2 f).K →* X)
    (hker : ψ.ker ≤ Subgroup.center (ggU .PSL 2 f).K) {y : X}
    (hy : GGPsiInnerDiag (ggU .PSL 2 f).D ψ y⁻¹) :
    ∃ A : GL (Fin 2) (GaloisField 2 f), (y, A) ∈ LinFusion.ggInducedPairs ψ :=
  exists_mem_ggInducedPairs_one (F := GaloisField 2 f) ψ hker hy

end Genuine

end CFSG.StandardType.A6Red
