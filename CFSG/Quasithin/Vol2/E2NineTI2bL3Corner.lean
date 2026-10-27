module

public import CFSG.LargeExtraspecial.A2ModSL
public import CFSG.LocalAnalysis.ComponentInitial.CentralSL2Semilinear
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Quasithin.Vol2.Ch3E213MP5E

public section

namespace CFSG.Quasithin.E2.TI2b.L3

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Quasithin.Ch3E213M.P5
open CFSG.LocalAnalysis.ComponentInitial (sl2Upper sl2Lower sl2_closure_upper_lower)
open scoped MatrixGroups

variable {k : Type} [Field k]

theorem tv_e0_mem_ua1 {ψ : Fin 3 → k} (hψ : ψ 0 = 0) :
    CFSG.LargeExtraspecial.A2Mod.tv (Pi.single 0 1 : Fin 3 → k) ψ ∈ ua1 k := by
  have h : ψ ⬝ᵥ (Pi.single 0 1 : Fin 3 → k) = 0 := by
    rw [dotProduct_single, hψ, zero_mul]
  rw [mem_ua1]
  refine ⟨ψ 1, ψ 2, ?_⟩
  apply Subtype.ext
  rw [CFSG.LargeExtraspecial.A2Mod.coe_tv h, coe_uu]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.vecMulVec_apply, Pi.single_apply, hψ]

theorem exists_sl2_le_of_orbit {Y : Subgroup (projectiveSL 3 k)} (hY : pa1 k ≤ Y)
    {y : Matrix.SpecialLinearGroup (Fin 3) k} (hy : proj 3 k y ∈ Y)
    (h20 : (y : Matrix (Fin 3) (Fin 3) k) 2 0 ≠ 0) :
    ∃ f : SL(2, k) →* projectiveSL 3 k, Function.Injective f ∧ f.range ≤ Y ∧ pzz k ≤ f.range := by
  obtain ⟨w, hw⟩ : ∃ w : Fin 3 → k, ∀ i, w i = (y : Matrix (Fin 3) (Fin 3) k) i 0 :=
    ⟨fun i => (y : Matrix (Fin 3) (Fin 3) k) i 0, fun i => rfl⟩
  have hw2 : w 2 ≠ 0 := by rw [hw 2]; exact h20
  have hyw : (y : Matrix (Fin 3) (Fin 3) k) *ᵥ (Pi.single 0 1 : Fin 3 → k) = w := by
    funext i
    simp [Matrix.mulVec_single_one, hw]
  obtain ⟨g, hg⟩ : ∃ g : Matrix.SpecialLinearGroup (Fin 3) k,
      (g : Matrix (Fin 3) (Fin 3) k) = !![1, 0, w 0; 0, (w 2)⁻¹, w 1; 0, 0, w 2] :=
    ⟨⟨!![1, 0, w 0; 0, (w 2)⁻¹, w 1; 0, 0, w 2], by
      rw [Matrix.det_fin_three]
      simp [hw2]⟩, rfl⟩
  have identA : ∀ c : k, g * uu 0 0 c * g⁻¹ = uu 0 0 (c * (w 2)⁻¹) := by
    intro c
    refine mul_inv_eq_iff_eq_mul.mpr ?_
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_uu, coe_uu, hg]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, hw2] <;>
      (try field_simp) <;> (try ring)
  have hψw : (![1, 0, -(w 0) / (w 2)] : Fin 3 → k) ⬝ᵥ w = 0 := by
    have h2 : -(w 0) / (w 2) * w 2 = -(w 0) := div_mul_cancel₀ (-(w 0)) hw2
    simp [dotProduct, Fin.sum_univ_three, h2]
  have identB : ∀ c : k, g * corner k (sl2Lower k c) * g⁻¹ =
      CFSG.LargeExtraspecial.A2Mod.tv (c • w) ![1, 0, -(w 0) / (w 2)] := by
    intro c
    have hψc : (![1, 0, -(w 0) / (w 2)] : Fin 3 → k) ⬝ᵥ (c • w) = 0 := by
      rw [dotProduct_smul, hψw, smul_zero]
    refine mul_inv_eq_iff_eq_mul.mpr ?_
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      CFSG.LargeExtraspecial.A2Mod.coe_tv hψc, coe_corner,
      CFSG.LocalAnalysis.ComponentInitial.coe_sl2Lower, hg]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cornerMat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.add_apply, Matrix.one_apply,
        Matrix.vecMulVec_apply, hw2] <;> field_simp <;> ring
  have key : ∀ φ' : Fin 3 → k, φ' ⬝ᵥ w = 0 →
      proj 3 k (CFSG.LargeExtraspecial.A2Mod.tv w φ') ∈ Y := by
    intro φ' hφ'
    obtain ⟨φ, hcφ⟩ : ∃ φ : Fin 3 → k, CFSG.LargeExtraspecial.A2Mod.contra y φ = φ' :=
      ⟨_, CFSG.LargeExtraspecial.A2Mod.contra_contra_inv y φ'⟩
    have hdot : φ' ⬝ᵥ w = φ ⬝ᵥ (Pi.single 0 1 : Fin 3 → k) := by
      have h := CFSG.LargeExtraspecial.A2Mod.contra_dotProduct_mulVec y φ (Pi.single 0 1)
      rw [hcφ, hyw] at h
      exact h
    have hφ0 : φ 0 = 0 := by
      have h := hdot.symm.trans hφ'
      rw [dotProduct_single, mul_one] at h
      exact h
    have hconj := CFSG.LargeExtraspecial.A2Mod.conj_tv y (Pi.single 0 1) φ
    rw [hyw, hcφ] at hconj
    have hmem0 : proj 3 k (CFSG.LargeExtraspecial.A2Mod.tv (Pi.single 0 1 : Fin 3 → k) φ) ∈
        pa1 k :=
      Subgroup.mem_map_of_mem (proj 3 k) (tv_e0_mem_ua1 hφ0)
    have hmem : proj 3 k (CFSG.LargeExtraspecial.A2Mod.tv (Pi.single 0 1 : Fin 3 → k) φ) ∈ Y :=
      hY hmem0
    rw [← hconj, map_mul, map_mul, map_inv]
    exact Y.mul_mem (Y.mul_mem hy hmem) (Y.inv_mem hy)
  obtain ⟨f, hfinj, hfA⟩ : ∃ f : SL(2, k) →* projectiveSL 3 k, Function.Injective f ∧
      ∀ A : SL(2, k), f A = proj 3 k (g * corner k A * g⁻¹) :=
    ⟨(MulAut.conj (proj 3 k g)).toMonoidHom.comp (cornerHom k),
      (MulAut.conj (proj 3 k g)).injective.comp cornerHom_injective,
      fun A => by simp [MulAut.conj_apply, cornerHom_apply, map_mul, map_inv]⟩
  have hUp : ∀ c : k, f (sl2Upper k c) = proj 3 k (uu 0 0 (c * (w 2)⁻¹)) := by
    intro c
    have hU : corner k (sl2Upper k c) = uu 0 0 c := corner_sl2UpperUnipotent c
    rw [hfA, hU, identA]
  have hLo : ∀ c : k, f (sl2Lower k c) =
      proj 3 k (CFSG.LargeExtraspecial.A2Mod.tv (c • w) ![1, 0, -(w 0) / (w 2)]) := by
    intro c
    rw [hfA, identB]
  have hYu : ∀ c : k, proj 3 k (uu 0 0 c) ∈ Y := by
    intro c
    have hpa : proj 3 k (uu 0 0 c) ∈ pa1 k :=
      Subgroup.mem_map_of_mem (proj 3 k) (mem_ua1.mpr ⟨0, c, rfl⟩)
    exact hY hpa
  refine ⟨f, hfinj, ?_, ?_⟩
  ·
    have hcl : Subgroup.closure (Set.range (sl2Upper k) ∪ Set.range (sl2Lower k)) ≤
        Y.comap f := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · show f (sl2Upper k c) ∈ Y
        rw [hUp c]
        exact hYu _
      · show f (sl2Lower k c) ∈ Y
        rw [hLo c, CFSG.LargeExtraspecial.A2Mod.tv_smul_left]
        exact key _ (by rw [smul_dotProduct, hψw, smul_zero])
    rw [sl2_closure_upper_lower] at hcl
    rintro z hz
    obtain ⟨A, rfl⟩ := MonoidHom.mem_range.mp hz
    exact Subgroup.mem_comap.mp (hcl (Subgroup.mem_top A))
  ·
    rintro z hz
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp (show z ∈ (uzz k).map (proj 3 k) from hz)
    obtain ⟨c, rfl⟩ := mem_uzz.mp hx
    refine MonoidHom.mem_range.mpr ⟨sl2Upper k (c * w 2), ?_⟩
    rw [hUp, mul_inv_cancel_right₀ hw2]

end CFSG.Quasithin.E2.TI2b.L3
