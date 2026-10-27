module

public import CFSG.Quasithin.Vol2.Ch11SecO1bE
public import CFSG.Quasithin.Vol2.Ch11SecO1bI
public import CFSG.Quasithin.Vol2.Ch11SecDFacts2
public import CFSG.Quasithin.Vol2.Ch11SecO1bH

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecO1b

open CFSG.Quasithin CFSG.Quasithin.H13 KGNat SecA
open CFSG.ClassicalInvolution.ModelFacts.OddCover Matrix
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (flagSpace)
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open scoped IsMulCommutative

variable {K : Type} [Field K]

theorem ind_sl3 (g : SpecialLinearGroup (Fin 3) K) (c d : K)
    (h : c • ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0]) +
      d • ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 1, 0]) = 0) : c = 0 ∧ d = 0 := by
  rw [← Matrix.mulVec_smul, ← Matrix.mulVec_smul, ← Matrix.mulVec_add] at h
  have h1 := congrArg (fun x => ((g⁻¹ : SpecialLinearGroup (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) K) *ᵥ x) h
  simp only [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec, Matrix.mulVec_zero] at h1
  exact ⟨by simpa using congrFun h1 0, by simpa using congrFun h1 1⟩

theorem plane_sl3 (g : SpecialLinearGroup (Fin 3) K) (x : Fin 3 → K) :
    (((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ x) 2 = 0 ↔
      ∃ c d : K, x = c • ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0]) +
        d • ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 1, 0]) := by
  have hg : ∀ y, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ
      (((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  have hg' : ∀ y, ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
      ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  simp only [← Matrix.mulVec_smul, ← Matrix.mulVec_add]
  constructor
  · intro h
    refine ⟨(((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ x) 0,
      (((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ x) 1, ?_⟩
    conv_lhs => rw [← hg x]
    congr 1
    generalize ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ x = y at h ⊢
    funext i
    fin_cases i <;> simp [h]
  · rintro ⟨c, d, rfl⟩
    rw [hg']
    simp

theorem ind_sp4 (g : StatedSp 2 K) (c d : K)
    (h : c • (mat 2 K g *ᵥ vec4 1 0 0 0) + d • (mat 2 K g *ᵥ vec4 0 1 0 0) = 0) :
    c = 0 ∧ d = 0 := by
  rw [← Matrix.mulVec_smul, ← Matrix.mulVec_smul, ← Matrix.mulVec_add] at h
  have h1 := congrArg (fun x => mat 2 K g⁻¹ *ᵥ x) h
  simp only [mat_inv_mulVec, Matrix.mulVec_zero] at h1
  exact ⟨by simpa [vec4] using congrFun h1 (.inl 0), by simpa [vec4] using congrFun h1 (.inl 1)⟩

theorem plane_sp4 (g : StatedSp 2 K) (x : Fin 2 ⊕ Fin 2 → K) :
    x ∈ gmapSp g (spPlane K) ↔
      ∃ c d : K, x = c • (mat 2 K g *ᵥ vec4 1 0 0 0) + d • (mat 2 K g *ᵥ vec4 0 1 0 0) := by
  rw [mem_gmapSp, mem_spPlane]
  simp only [← Matrix.mulVec_smul, ← Matrix.mulVec_add]
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨(mat 2 K g⁻¹ *ᵥ x) (.inl 0), (mat 2 K g⁻¹ *ᵥ x) (.inl 1), ?_⟩
    conv_lhs => rw [← mat_mulVec_inv g x]
    congr 1
    exact vec4_eq (by simp [vec4]) (by simp [vec4]) (by simp [vec4, h0]) (by simp [vec4, h1])
  · rintro ⟨c, d, rfl⟩
    rw [mat_inv_mulVec]
    exact ⟨by simp [vec4], by simp [vec4]⟩

end CFSG.Quasithin.Vol2.Ch11.SecO1b

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Quasithin CFSG.Quasithin.H13 KGNat SecO1b
open CFSG.ClassicalInvolution.ModelFacts.OddCover Matrix
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open scoped IsMulCommutative

theorem pointCommFact_holds : PointCommFact := by
  intro G _ _ T L I n V₁ V₂ hS hk hV₁ hV₂ a ha y hy hle
  have := SecO1.isMulCommutative hS
  obtain ⟨k, hk2⟩ := hS.sylow.1 ⟨a, ha⟩
  have ha2 : a ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk2
    simpa using this
  have haV := SecA.T_le_normalizer_fsuV T I ha
  have haL := hS.normal ha
  have haV₁ := SecA.IsVi.le_normalizer hV₁ ha
  have haV₂ := SecA.IsVi.le_normalizer hV₂ ha
  have hV₁V := SecA.IsVi.le_fsuV hV₁
  have hV₂V := SecA.IsVi.le_fsuV hV₂
  rcases hk with hk | hk
  · obtain ⟨K, _, _, _, hK, π, f, hf, g, hg⟩ := exists_coord_sl3_syl hS hk
    have hx₀ : (![1, 0, 0] : Fin 3 → K) ≠ 0 := fun h => by simpa using congrFun h 0
    obtain ⟨Tm, σ, hσ, hT⟩ := exists_semilinear_conjV hf
      (fun T' hT' => commutant_statedSL (by norm_num) T' hT') hx₀ haL haV
    have hV₁' := mem_V1_sl3_iff hS hK hf hg hV₁
    obtain ⟨p, hp⟩ := exists_point_conj hf hS.le_normalizer hV₁' hy
    refine pointComm_of_coords hf.map_mul (SecO1.IsCoord.injective_of_bot hf) hf.surj
      (ind_sl3 g) hV₁V hV₂V hV₁' (fun v => ?_) hp haV haV₁ haV₂ ha2 hσ hT hle
    rw [← Subgroup.mem_subgroupOf, mem_V2_sl3 hS hK hf hg hV₂, mem_pre_plane_iff hf g v,
      plane_sl3]
  · obtain ⟨K, _, _, _, hK, π, f, -, hf, g, hg⟩ := exists_coord_sp4_syl hS hk
    have hx₀ : (vec4 1 0 0 0 : Fin 2 ⊕ Fin 2 → K) ≠ 0 := fun h =>
      (one_ne_zero : (1 : K) ≠ 0) (congrFun h (.inl 0))
    obtain ⟨Tm, σ, hσ, hT⟩ := exists_semilinear_conjV hf
      (fun T' hT' => commutant_statedSp T' hT') hx₀ haL haV
    have hV₁' := mem_V1_sp4_iff hS hK hf hg hV₁
    obtain ⟨p, hp⟩ := exists_point_conj hf hS.le_normalizer hV₁' hy
    refine pointComm_of_coords hf.map_mul (SecO1.IsCoord.injective_of_bot hf) hf.surj
      (ind_sp4 g) hV₁V hV₂V hV₁' (fun v => ?_) hp haV haV₁ haV₂ ha2 hσ hT hle
    rw [← Subgroup.mem_subgroupOf, mem_V2_sp4 hS hK hf hg hV₂]
    exact plane_sp4 g (f v)

end CFSG.Quasithin.Vol2.Ch11.SecD
