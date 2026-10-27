module

public import CFSG.LocalAnalysis.StandardType.GGSL9TwoModel
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerLinearNonsplit
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestTorus
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLLIDCore

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix

section ProjEquiv

variable {K : Type} [Field K] [Finite K]

private theorem units_eq_one_of_card_two (hK : Nat.card K = 2) (c : Kˣ) : c = 1 := by
  have h1 : Nat.card Kˣ ≤ 1 := by
    rw [Nat.card_units, hK]
  have := Finite.card_le_one_iff_subsingleton.mp h1
  exact Subsingleton.elim c 1

theorem proj_nine_injective_of_card_two (hK : Nat.card K = 2) :
    Function.Injective (proj 9 K) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  obtain ⟨c, -, hc⟩ := proj_eq_one_iff.mp hA
  rw [units_eq_one_of_card_two hK c, Units.val_one, map_one] at hc
  exact Subtype.ext (hc.trans Matrix.SpecialLinearGroup.coe_one.symm)

theorem toGL_nine_bijective_of_card_two (hK : Nat.card K = 2) :
    Function.Bijective
      (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 9) K →* GL (Fin 9) K) := by
  refine ⟨SpecialLinearGroup.toGL_injective, fun A => ?_⟩
  have hdet : (A : Matrix (Fin 9) (Fin 9) K).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply,
      units_eq_one_of_card_two hK (Matrix.GeneralLinearGroup.det A), Units.val_one]
  exact ⟨⟨A, hdet⟩, Units.ext rfl⟩

@[expose] noncomputable def ggSL9ProjEquiv (hK : Nat.card K = 2) :
    projectiveSL 9 K ≃* (GGSL9V ≃ₗ[ZMod 2] GGSL9V) :=
  letI := Fintype.ofFinite K
  (MulEquiv.ofBijective (proj 9 K)
      ⟨proj_nine_injective_of_card_two hK, proj_surjective 9 K⟩).symm.trans <|
    (MulEquiv.ofBijective _ (toGL_nine_bijective_of_card_two hK)).trans <|
      (Units.mapEquiv (RingEquiv.mapMatrix (m := Fin 9) (ZMod.ringEquivOfPrime K Nat.prime_two
        (by rw [← Nat.card_eq_fintype_card, hK])).symm).toMulEquiv).trans ggSL9GLEquiv

@[expose] noncomputable def ggSL9RecipeEquiv (hK : Nat.card K = 2) :
    LargeEvenProj (LargeEvenSLGroup (Fin 9) K) ≃* (GGSL9V ≃ₗ[ZMod 2] GGSL9V) :=
  (TypeA.recipeEquiv 9 K).trans (ggSL9ProjEquiv hK)

theorem congr_ggSL9RecipeEquiv_mem (hK : Nat.card K = 2)
    {φ : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin 9) K))}
    (hφ : φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin 9) K)) Set.univ) :
    MulAut.congr (ggSL9RecipeEquiv hK) φ ∈
      Set.range
        (MulAut.conj : (GGSL9V ≃ₗ[ZMod 2] GGSL9V) →* MulAut (GGSL9V ≃ₗ[ZMod 2] GGSL9V)) := by
  obtain ⟨A, hA⟩ := TypeA.congr_recipeEquiv_mem hφ
  obtain ⟨g, rfl⟩ := (toGL_nine_bijective_of_card_two hK).2 A
  rw [← LinUnitL.conj_proj_eq_conjAut] at hA
  refine ⟨ggSL9ProjEquiv hK (proj 9 K g), ?_⟩
  rw [← mulAut_congr_conj, hA]
  ext x
  simp only [ggSL9RecipeEquiv, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_trans_apply,
    MulEquiv.symm_apply_apply]

end ProjEquiv

theorem center_ggSL9_eq_bot : Subgroup.center (GGSL9V ≃ₗ[ZMod 2] GGSL9V) = ⊥ := by
  set e := ggSL9ProjEquiv (K := ZMod 2) (Nat.card_zmod 2) with he
  rw [eq_bot_iff]
  intro x hx
  have hc : e.symm x ∈ Subgroup.center (projectiveSL 9 (ZMod 2)) := by
    rw [Subgroup.mem_center_iff]
    intro z
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact Subgroup.mem_center_iff.mp hx (e z)
  rw [CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot (n := 9) (k := ZMod 2)
    (by norm_num), Subgroup.mem_bot] at hc
  rw [Subgroup.mem_bot]
  have h1 := congrArg e hc
  rwa [MulEquiv.apply_symm_apply, map_one] at h1

theorem ggCenterPrime_ggSL9 {p : ℕ} (hp : p.Prime) :
    GGCenterPrime p (GGSL9V ≃ₗ[ZMod 2] GGSL9V) := by
  refine ggCenterPrime_of_mulEquiv (ggSL9ProjEquiv (K := ZMod 2) (Nat.card_zmod 2)).symm
    (ggCenterPrime_projectiveSL hp ?_ (by norm_num))
  rw [Nat.card_zmod]
  exact hp.not_dvd_one

theorem ggTorusLift_ggSL9 : GGTorusLift 7 3 (GGSL9V ≃ₗ[ZMod 2] GGSL9V) := by
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have hU8 := card_range_ggSL9RootHom h01 0
  refine OrthRest.ggTorusLift_of_R (by norm_num) center_ggSL9_eq_bot
    (ggCenterPrime_ggSL9 (by norm_num)) (U := (ggSL9RootHom 0 1 h01 0).range) (E := ggSL9Torus)
    ?_ (IsPGroup.of_card (n := 3) hU8) (ggSL9Torus_le_normalizer_rootHom h01 0)
    isElemAbelian_ggSL9Torus card_ggSL9Torus
  intro hbot
  rw [hbot, Subgroup.card_bot] at hU8
  exact absurd hU8 (by norm_num)

end CFSG.StandardType

end
