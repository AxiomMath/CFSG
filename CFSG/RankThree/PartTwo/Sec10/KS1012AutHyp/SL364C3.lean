module

public import CFSG.RankThree.PartTwo.Sec10.KS1012AutHyp.SL34
public import CFSG.RankThree.PartTwo.Sec4.Item4Res6ProofL364Field

public section

namespace CFSG.RankThree.PartTwo.Sec10.KS1012AutHyp

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartTwo.Sec4.Res6L364 (K64 σ4)

@[expose] noncomputable def slConjSL (K : Type) [Field K] :
    GL (Fin 3) K →* MulAut (CFSG.Open.StatedSL 3 K) :=
  (MulAut.congr (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K)).toMonoidHom.comp
    (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 K)

@[expose] noncomputable def slFieldSL (K : Type) [Field K] :
    (K ≃+* K) →* MulAut (CFSG.Open.StatedSL 3 K) :=
  (MulAut.congr (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K)).toMonoidHom.comp
    (CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin 3) K)

theorem Dhom_slConjSL (K : Type) [Field K] (H : GL (Fin 3) K) :
    Dhom K (slConjSL K H) = conjAut 3 K H := by
  have : (MulAut.congr (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).symm)
      (slConjSL K H) =
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 K H := by
    ext x
    simp [slConjSL, MulAut.congr_apply]
  show descendAut 3 K ((MulAut.congr
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).symm) (slConjSL K H)) = _
  rw [this]
  rfl

theorem Dhom_slFieldSL (K : Type) [Field K] (σ : K ≃+* K) :
    Dhom K (slFieldSL K σ) = fieldAut 3 K σ := by
  have : (MulAut.congr (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).symm)
      (slFieldSL K σ) =
      CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin 3) K σ := by
    ext x
    simp [slFieldSL, MulAut.congr_apply]
  show descendAut 3 K ((MulAut.congr
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).symm) (slFieldSL K σ)) = _
  rw [this]
  rfl

theorem coe_slFieldSL (K : Type) [Field K] (σ : K ≃+* K) (x : CFSG.Open.StatedSL 3 K)
    (i j : Fin 3) :
    (((slFieldSL K σ x : CFSG.Open.StatedSL 3 K) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j =
      σ (((x : CFSG.Open.StatedSL 3 K) : GL (Fin 3) K) i j) := by
  set E := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K with hE
  have h1 : ((E.symm x : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [← CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe 3 K (E.symm x),
      E.apply_symm_apply]
  simp only [slFieldSL, MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
    MulAut.congr_apply, MulEquiv.trans_apply]
  rw [CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe]
  exact congrArg σ (congrFun (congrFun h1 i) j)

theorem exists_conj_slFieldSL_mem {F : Subgroup (MulAut (CFSG.Open.StatedSL 3 K64))}
    (hF : CFSG.Open.IsElemAbelian 3 F) {g : MulAut (CFSG.Open.StatedSL 3 K64)} (hg : g ∈ F)
    (hD : Dhom K64 g ∉ linearAutGroup 3 K64) :
    ∃ H : GL (Fin 3) K64,
      slConjSL K64 H * slFieldSL K64 σ4 * (slConjSL K64 H)⁻¹ ∈ F := by
  have hg3 : g ^ 3 = 1 := hF.2 g hg
  have hD3 : Dhom K64 g ^ 3 = 1 := by rw [← map_pow, hg3, map_one]
  obtain ⟨τ, hτ, H, hH⟩ := CFSG.RankThree.PartTwo.KFacts.linear_order_three_field_descent
    (by norm_num) (Dhom K64 g) hD3 hD
  refine ⟨H, ?_⟩
  have key : ∀ σ : K64 ≃+* K64,
      Dhom K64 g = conjAut 3 K64 H * fieldAut 3 K64 σ * (conjAut 3 K64 H)⁻¹ →
      g = slConjSL K64 H * slFieldSL K64 σ * (slConjSL K64 H)⁻¹ := by
    intro σ h
    apply Dhom_injective K64
    rw [h, map_mul, map_mul, map_inv, Dhom_slConjSL, Dhom_slFieldSL]
  rcases CFSG.RankThree.PartTwo.Sec4.Res6L364.eq_σ4_or_sq hτ with rfl | rfl
  · rw [← key _ hH]
    exact hg
  · have hg' := key _ hH
    have h1 : slFieldSL K64 (σ4 * σ4) * slFieldSL K64 σ4 = 1 := by
      rw [← map_mul, ← pow_three', CFSG.RankThree.PartTwo.Sec4.Res6L364.σ4_cube, map_one]
    have h2 : (slFieldSL K64 (σ4 * σ4))⁻¹ = slFieldSL K64 σ4 := inv_eq_of_mul_eq_one_right h1
    have h3 := inv_mem hg
    rw [hg', mul_inv_rev, mul_inv_rev, inv_inv, h2, ← mul_assoc] at h3
    exact h3

end CFSG.RankThree.PartTwo.Sec10.KS1012AutHyp

end
