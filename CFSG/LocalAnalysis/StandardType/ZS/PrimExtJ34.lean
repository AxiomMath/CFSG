module

public import CFSG.LocalAnalysis.StandardType.ZS.PrimExtBond
public import CFSG.LocalAnalysis.StandardType.ZS.PrimExtSetting
import CFSG.LocalAnalysis.StandardType.ZS.ExcMatricesRefl

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

private theorem isUnit_det_of_mul_self {n : ℕ} {K : Type} [Field K]
    (M : Matrix (Fin n) (Fin n) K) (h : M * M = 1) : IsUnit M.det :=
  isUnit_iff_exists.mpr ⟨M.det, by rw [← Matrix.det_mul, h, Matrix.det_one],
    by rw [← Matrix.det_mul, h, Matrix.det_one]⟩

theorem exists_mem_j34Mats (hp : p ≠ 2) {β : ZMod p} (hβ : 2 * β ^ 2 + β + 1 = 0)
    (f : Module.Basis (Fin 4) (ZMod p) U) :
    (∀ i : Fin 4, i.val < 3 → ∃ g ∈ basisClosure f (j34Mats β),
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) = diagSignMat i) ∧
    (∀ i j : Fin 4, i < j → j.val < 3 → ∃ g ∈ basisClosure f (j34Mats β),
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) = pijMat i j 1) ∧
    (∃ g ∈ basisClosure f (j34Mats β), LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) =
      1 - Matrix.vecMulVec ![1, -(2 * β), -1, 0] ![1 / 2, -(β⁻¹ / 2), -(1 / 2), 0]) ∧
    ∃ g ∈ basisClosure f (j34Mats β), LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) =
      1 - Matrix.vecMulVec ![-(2 * β), 1, -1, 0] ![-(β⁻¹ / 2), 1 / 2, -(1 / 2), 0] := by
  have h2ne : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hβne : β ≠ 0 := by
    rintro rfl
    simp at hβ
  have hdiagdet : ∀ j : Fin 3, IsUnit (diagSignMat j : Matrix (Fin 3) (Fin 3) (ZMod p)).det := by
    intro j
    rw [diagSignMat, Matrix.det_diagonal]
    simp
  have hpij01 : (pijMat (0 : Fin 3) 1 (1 : ZMod p)) * pijMat 0 1 1 = 1 := by
    ext r c
    fin_cases r <;> fin_cases c <;> simp [pijMat, Matrix.mul_apply, Fin.sum_univ_three]
  have hpij12 : (pijMat (1 : Fin 3) 2 (1 : ZMod p)) * pijMat 1 2 1 = 1 := by
    ext r c
    fin_cases r <;> fin_cases c <;> simp [pijMat, Matrix.mul_apply, Fin.sum_univ_three]
  have hj34 : j34BlockMat β * j34BlockMat β = 1 := by
    ext r c
    fin_cases r <;> fin_cases c <;> simp [j34BlockMat, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.cons_val] <;> field_simp [hβne, h2ne] <;> ring_nf
  have gen : ∀ {M : Matrix (Fin 3) (Fin 3) (ZMod p)}, M ∈ j34BlockMats β → IsUnit M.det →
      ∃ g ∈ basisClosure f (j34Mats β),
        LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) = Matrix.blockSucc M := by
    intro M hM hdet
    exact exists_mem_basisClosure_toMatrix_eq f ⟨M, hM, rfl⟩ (by rwa [Matrix.det_blockSucc])
  have ha3M : (Matrix.blockSucc (j34BlockMat β) : Matrix (Fin 4) (Fin 4) (ZMod p)) =
      1 - Matrix.vecMulVec ![1, -(2 * β), -1, 0] ![1 / 2, -(β⁻¹ / 2), -(1 / 2), 0] := by
    ext i j
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => rw [Matrix.blockSucc_last_last]; simp [Matrix.vecMulVec]; ring
      | cast j =>
        rw [Matrix.blockSucc_last_castSucc]
        simp only [Matrix.vecMulVec]
        have hne : (3 : Fin 4) ≠ j.castSucc := by
          intro h
          have hv := congrArg Fin.val h
          simp at hv
          omega
        simp [hne]
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        rw [Matrix.blockSucc_castSucc_last]
        simp only [Matrix.vecMulVec]
        have hne : i.castSucc ≠ (3 : Fin 4) := by
          intro h
          have hv := congrArg Fin.val h
          simp at hv
          omega
        simp [hne]
      | cast j =>
        simp only [Matrix.blockSucc_castSucc_castSucc, Matrix.vecMulVec]
        fin_cases i <;> fin_cases j <;> simp [j34BlockMat, Matrix.cons_val] <;>
          field_simp [hβne, h2ne] <;> ring_nf
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨gh0, hgh0, hhm0⟩ := gen (M := diagSignMat 0) (by simp [j34BlockMats]) (hdiagdet 0)
    obtain ⟨gp01, hgp01, hm01⟩ := gen (M := pijMat 0 1 1) (by simp [j34BlockMats])
      (isUnit_det_of_mul_self _ hpij01)
    have hw1 : ∃ g ∈ basisClosure f (j34Mats β),
        LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) = diagSignMat (1 : Fin 4) := by
      refine ⟨gp01 * gh0 * gp01, mul_mem (mul_mem hgp01 hgh0) hgp01, ?_⟩
      rw [LinearEquiv.coe_toLinearMap_mul, LinearEquiv.coe_toLinearMap_mul,
        LinearMap.toMatrix_mul, LinearMap.toMatrix_mul, hm01, hhm0]
      rw [show (1 : Fin 4) = (1 : Fin 3).castSucc from rfl, ← blockSucc_diagSignMat (1 : Fin 3),
        ← Matrix.blockSucc_mul, ← Matrix.blockSucc_mul, Matrix.blockSucc_injective.eq_iff]
      ext r c
      fin_cases r <;> fin_cases c <;> simp [pijMat, diagSignMat, Matrix.mul_apply,
        Fin.sum_univ_three]
    obtain ⟨gh1, hgh1, hhm1⟩ := hw1
    obtain ⟨gp12, hgp12, hm12⟩ := gen (M := pijMat 1 2 1) (by simp [j34BlockMats])
      (isUnit_det_of_mul_self _ hpij12)
    have hw2 : ∃ g ∈ basisClosure f (j34Mats β),
        LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) = diagSignMat (2 : Fin 4) := by
      refine ⟨gp12 * gh1 * gp12, mul_mem (mul_mem hgp12 hgh1) hgp12, ?_⟩
      rw [LinearEquiv.coe_toLinearMap_mul, LinearEquiv.coe_toLinearMap_mul,
        LinearMap.toMatrix_mul, LinearMap.toMatrix_mul, hm12, hhm1]
      rw [show (1 : Fin 4) = (1 : Fin 3).castSucc from rfl, ← blockSucc_diagSignMat (1 : Fin 3),
        show (2 : Fin 4) = (2 : Fin 3).castSucc from rfl, ← blockSucc_diagSignMat (2 : Fin 3),
        ← Matrix.blockSucc_mul, ← Matrix.blockSucc_mul, Matrix.blockSucc_injective.eq_iff]
      ext r c
      fin_cases r <;> fin_cases c <;> simp [pijMat, diagSignMat, Matrix.mul_apply,
        Fin.sum_univ_three]
    obtain ⟨gh2, hgh2, hhm2⟩ := hw2
    have hi012 : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
    rcases hi012 with h | h | h
    · rw [show i = 0 from Fin.ext (by omega)]
      exact ⟨gh0, hgh0, by rw [hhm0, blockSucc_diagSignMat]; rfl⟩
    · rw [show i = 1 from Fin.ext (by omega)]
      exact ⟨gh1, hgh1, by rw [hhm1]⟩
    · rw [show i = 2 from Fin.ext (by omega)]
      exact ⟨gh2, hgh2, by rw [hhm2]⟩
  · intro i j hij hj
    fin_cases j
    · exact absurd hij (by simp)
    · fin_cases i
      · obtain ⟨g, hg, hgm⟩ := gen (M := pijMat 0 1 1) (by simp [j34BlockMats])
          (isUnit_det_of_mul_self _ hpij01)
        exact ⟨g, hg, by rw [hgm, blockSucc_pijMat]; rfl⟩
      · exact absurd hij (by simp)
      · exact absurd hij (by simp)
      · exact absurd hij (by simp)
    · fin_cases i
      · obtain ⟨gp01, hgp01, hm01⟩ := gen (M := pijMat 0 1 1) (by simp [j34BlockMats])
          (isUnit_det_of_mul_self _ hpij01)
        obtain ⟨gp12, hgp12, hm12⟩ := gen (M := pijMat 1 2 1) (by simp [j34BlockMats])
          (isUnit_det_of_mul_self _ hpij12)
        have hm01' : LinearMap.toMatrix f f (gp01 : U →ₗ[ZMod p] U) =
            (pijMat (0 : Fin 4) 1 1 : Matrix (Fin 4) (Fin 4) (ZMod p)) := by
          rw [hm01, blockSucc_pijMat]; rfl
        have hm12' : LinearMap.toMatrix f f (gp12 : U →ₗ[ZMod p] U) =
            (pijMat (1 : Fin 4) 2 1 : Matrix (Fin 4) (Fin 4) (ZMod p)) := by
          rw [hm12, blockSucc_pijMat]; rfl
        refine ⟨gp12 * gp01 * gp12, mul_mem (mul_mem hgp12 hgp01) hgp12, ?_⟩
        rw [LinearEquiv.coe_toLinearMap_mul, LinearEquiv.coe_toLinearMap_mul,
          LinearMap.toMatrix_mul, LinearMap.toMatrix_mul, hm12', hm01']
        ext r c
        fin_cases r <;> fin_cases c <;> simp [pijMat, Matrix.mul_apply, Fin.sum_univ_four]
      · obtain ⟨g, hg, hgm⟩ := gen (M := pijMat 1 2 1) (by simp [j34BlockMats])
          (isUnit_det_of_mul_self _ hpij12)
        exact ⟨g, hg, by rw [hgm, blockSucc_pijMat]; rfl⟩
      · exact absurd hij (by simp)
      · exact absurd hij (by simp)
    · exact absurd hj (by decide)
  · obtain ⟨ga3, hga3, hma3⟩ := gen (M := j34BlockMat β) (by simp [j34BlockMats])
      (isUnit_det_of_mul_self _ hj34)
    exact ⟨ga3, hga3, by rw [hma3, ha3M]⟩
  · obtain ⟨gp01, hgp01, hm01⟩ := gen (M := pijMat 0 1 1) (by simp [j34BlockMats])
      (isUnit_det_of_mul_self _ hpij01)
    obtain ⟨ga3, hga3, hma3⟩ := gen (M := j34BlockMat β) (by simp [j34BlockMats])
      (isUnit_det_of_mul_self _ hj34)
    have hm01' : LinearMap.toMatrix f f (gp01 : U →ₗ[ZMod p] U) =
        (pijMat (0 : Fin 4) 1 1 : Matrix (Fin 4) (Fin 4) (ZMod p)) := by
      rw [hm01, blockSucc_pijMat]; rfl
    have hma3' : LinearMap.toMatrix f f (ga3 : U →ₗ[ZMod p] U) =
        1 - Matrix.vecMulVec ![1, -(2 * β), -1, 0] ![1 / 2, -(β⁻¹ / 2), -(1 / 2), 0] := by
      rw [hma3, ha3M]
    refine ⟨gp01 * ga3 * gp01, mul_mem (mul_mem hgp01 hga3) hgp01, ?_⟩
    rw [LinearEquiv.coe_toLinearMap_mul, LinearEquiv.coe_toLinearMap_mul,
      LinearMap.toMatrix_mul, LinearMap.toMatrix_mul, hm01', hma3']
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pijMat, Matrix.mul_apply, Matrix.vecMulVec, Fin.sum_univ_four]



theorem false_of_j34Eta (hp3 : 3 < p) {β ψ₁ ψ₂ w₁ w₂ : ZMod p}
    (h1 : (ψ₁ = 0 ∧ w₁ = 0) ∨ ψ₁ * w₁ = 1) (h2 : (ψ₂ = 0 ∧ w₂ = 0) ∨ ψ₂ * w₂ = 1)
    (hsum : ψ₁ * w₁ + ψ₂ * w₂ ≠ 2) (hw : w₁ ≠ 0 ∨ w₂ ≠ 0)
    (_ha : EtaOK 4 (-(2 * β * ψ₁) - ψ₂) (-(β⁻¹ * w₁ + w₂) / 2))
    (ha' : EtaOK 4 (ψ₁ - ψ₂) ((w₁ - w₂) / 2)) : False := by
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · rcases hw with h | h <;> simp_all
  · obtain ⟨hψ1, hw1⟩ := h1
    refine not_etaOK_four_of_mul_eq_half hp3 ?_ ha'
    rw [hψ1, hw1]
    linear_combination (1 / 2 : ZMod p) * h2
  · obtain ⟨hψ2, hw2⟩ := h2
    refine not_etaOK_four_of_mul_eq_half hp3 ?_ ha'
    rw [hψ2, hw2]
    linear_combination (1 / 2 : ZMod p) * h1
  · exact hsum (by rw [h1, h2]; ring)


theorem false_of_coords_j34 (hp4 : 4 < p) [Module.Finite (ZMod p) U]
    {G : Subgroup (U ≃ₗ[ZMod p] U)} (hG : DMax p G 4) {β : ZMod p} (hβ : 2 * β ^ 2 + β + 1 = 0)
    (f : Module.Basis (Fin 4) (ZMod p) U) (hH : basisClosure f (j34Mats β) ≤ G) {w : U}
    {ψ : Module.Dual (ZMod p) U} (hψ : ψ w = 2) (hb : Module.reflection hψ ∈ G)
    (hbH : Module.reflection hψ ∉ basisClosure f (j34Mats β)) (hw0 : f.repr w 0 = 0)
    (hψ0 : ψ (f 0) = 0) (hw3 : f.repr w 3 ≠ 0) (hψ3 : ψ (f 3) ≠ 0)
    (hw : ∃ i : Fin 3, f.repr w i.castSucc ≠ 0) : False := by
  have hp2 : p ≠ 2 := by omega
  have hp3 : 3 < p := by omega
  obtain ⟨hi, hπ, ha3, hpa3⟩ := exists_mem_j34Mats hp2 hβ f
  obtain ⟨gh1, hgh1, hhm1⟩ := hi 1 (by decide)
  obtain ⟨gh2, hgh2, hhm2⟩ := hi 2 (by decide)
  obtain ⟨gp01, hgp01, hpm01⟩ := hπ 0 1 (by decide) (by decide)
  obtain ⟨gp02, hgp02, hpm02⟩ := hπ 0 2 (by decide) (by decide)
  obtain ⟨ga3, hga3, hma3⟩ := ha3
  obtain ⟨gpa3, hgpa3, hmpa3⟩ := hpa3
  have hbne : ∀ {g : U ≃ₗ[ZMod p] U}, g ∈ basisClosure f (j34Mats β) →
      g ≠ Module.reflection hψ := fun hg heq => hbH (heq ▸ hg)
  have hd1 : ∃ g ∈ G, g ≠ Module.reflection hψ ∧
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) = diagSignMat (1 : Fin 4) :=
    ⟨gh1, hH hgh1, hbne hgh1, hhm1⟩
  have hd2 : ∃ g ∈ G, g ≠ Module.reflection hψ ∧
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) = diagSignMat (2 : Fin 4) :=
    ⟨gh2, hH hgh2, hbne hgh2, hhm2⟩
  have hπ1 : ∃ g ∈ G, g ≠ Module.reflection hψ ∧
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) = pijMat (0 : Fin 4) 1 1 :=
    ⟨gp01, hH hgp01, hbne hgp01, hpm01⟩
  have hπ2 : ∃ g ∈ G, g ≠ Module.reflection hψ ∧
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) = pijMat (0 : Fin 4) 2 1 :=
    ⟨gp02, hH hgp02, hbne hgp02, hpm02⟩
  have ht1 := repr_eq_zero_or_mul_eq_one_of_dMax_four hp4 hG f hψ hb
    (i := (0 : Fin 4)) (j := (1 : Fin 4)) (by decide) hw0 hψ0 hd1 hπ1
  have ht2 := repr_eq_zero_or_mul_eq_one_of_dMax_four hp4 hG f hψ hb
    (i := (0 : Fin 4)) (j := (2 : Fin 4)) (by decide) hw0 hψ0 hd2 hπ2
  have hψsum : ψ w = ∑ i : Fin 4, ψ (f i) * f.repr w i := by
    have h := congrArg (fun φ : Module.Dual (ZMod p) U => φ w) (f.sum_dual_apply_smul_coord ψ)
    simpa [Module.Basis.coord, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] using h.symm
  have hsum : ψ (f 1) * f.repr w 1 + ψ (f 2) * f.repr w 2 ≠ 2 := by
    intro hc
    have h2 : ψ (f 3) * f.repr w 3 = 0 := by
      have hw' := hψ
      rw [hψsum, Fin.sum_univ_four] at hw'
      simp only [hψ0, hw0, mul_zero, zero_add] at hw'
      linear_combination hw' - hc
    exact mul_ne_zero hψ3 hw3 h2
  have hβne : β ≠ 0 := by
    rintro rfl
    simp at hβ
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have hge : 2 ≤ p := (Fact.out : p.Prime).two_le
    exact hp2 (le_antisymm hle hge)
  have hκρa : ∑ i : Fin 4, (![1 / 2, -(β⁻¹ / 2), -(1 / 2), 0] : Fin 4 → ZMod p) i *
      (![1, -(2 * β), -1, 0] : Fin 4 → ZMod p) i = 2 := by
    simp only [Fin.sum_univ_four]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    field_simp [hβne, h2ne]
    ring_nf
  have hκρb : ∑ i : Fin 4, (![-(β⁻¹ / 2), 1 / 2, -(1 / 2), 0] : Fin 4 → ZMod p) i *
      (![-(2 * β), 1, -1, 0] : Fin 4 → ZMod p) i = 2 := by
    simp only [Fin.sum_univ_four]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    field_simp [hβne, h2ne]
    ring_nf
  have ha : EtaOK 4 (-(2 * β * ψ (f 1)) - ψ (f 2))
      (-(β⁻¹ * f.repr w 1 + f.repr w 2) / 2) := by
    have h := etaOK_of_toMatrix hG (d := 4) (by norm_num) hp4 (by omega) f hb (hH hga3)
      (Ne.symm (hbne hga3)) hψ rfl hma3 hκρa
    have e1 : (∑ i : Fin 4, ψ (f i) * (![1, -(2 * β), -1, 0] : Fin 4 → ZMod p) i)
        = -(2 * β * ψ (f 1)) - ψ (f 2) := by
      rw [Fin.sum_univ_four]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, hψ0, mul_zero,
        zero_mul, zero_add, add_zero]
      rw [show ψ (f 1) * (-(2 * β)) = -(ψ (f 1) * (2 * β)) from mul_neg _ _,
          show ψ (f 2) * (-1) = -(ψ (f 2) * 1) from mul_neg _ _]
      simp only [mul_one]
      rw [show ψ (f 1) * (2 * β) = 2 * β * ψ (f 1) by ring]
      abel
    have e2 : (∑ i : Fin 4, (![1 / 2, -(β⁻¹ / 2), -(1 / 2), 0] : Fin 4 → ZMod p) i *
        f.repr w i) = -(β⁻¹ * f.repr w 1 + f.repr w 2) / 2 := by
      rw [Fin.sum_univ_four]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, hw0, mul_zero,
        zero_mul, zero_add, add_zero]
      refine (congrArg₂ (· + ·) (neg_mul (β⁻¹ / 2) (f.repr w 1))
        (neg_mul (1 / 2) (f.repr w 2))).trans ?_
      refine (show -((β⁻¹ / 2) * f.repr w 1) + -((1 / 2) * f.repr w 2) =
        -(((β⁻¹ / 2) * f.repr w 1) + ((1 / 2) * f.repr w 2)) by abel).trans ?_
      refine (congrArg Neg.neg (show (β⁻¹ / 2) * f.repr w 1 + (1 / 2) * f.repr w 2 =
        (β⁻¹ * f.repr w 1 + f.repr w 2) / 2 by ring_nf)).trans ?_
      exact (neg_div 2 (β⁻¹ * f.repr w 1 + f.repr w 2)).symm
    rw [e1, e2] at h
    exact h
  have ha' : EtaOK 4 (ψ (f 1) - ψ (f 2)) ((f.repr w 1 - f.repr w 2) / 2) := by
    have h := etaOK_of_toMatrix hG (d := 4) (by norm_num) hp4 (by omega) f hb (hH hgpa3)
      (Ne.symm (hbne hgpa3)) hψ rfl hmpa3 hκρb
    have e1 : (∑ i : Fin 4, ψ (f i) * (![-(2 * β), 1, -1, 0] : Fin 4 → ZMod p) i)
        = ψ (f 1) - ψ (f 2) := by
      rw [Fin.sum_univ_four]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, hψ0, mul_zero,
        zero_mul, zero_add, add_zero]
      rw [show ψ (f 2) * (-1) = -(ψ (f 2) * 1) from mul_neg _ _]
      simp only [mul_one]
      abel
    have e2 : (∑ i : Fin 4, (![-(β⁻¹ / 2), 1 / 2, -(1 / 2), 0] : Fin 4 → ZMod p) i *
        f.repr w i) = (f.repr w 1 - f.repr w 2) / 2 := by
      rw [Fin.sum_univ_four]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, hw0, mul_zero,
        zero_mul, zero_add, add_zero]
      refine (congrArg (fun t => (1 / 2) * f.repr w 1 + t)
        (neg_mul (1 / 2) (f.repr w 2))).trans ?_
      refine (show (1 / 2) * f.repr w 1 + -((1 / 2) * f.repr w 2) =
        (1 / 2) * f.repr w 1 - (1 / 2) * f.repr w 2 by abel).trans ?_
      ring_nf
    rw [e1, e2] at h
    exact h
  have hw' : f.repr w 1 ≠ 0 ∨ f.repr w 2 ≠ 0 := by
    obtain ⟨i, hi⟩ := hw
    fin_cases i
    · exact absurd hw0 hi
    · exact Or.inl hi
    · exact Or.inr hi
  exact false_of_j34Eta hp3 ht1 ht2 hsum hw' ha ha'


namespace PrimExtSetting

variable {G H : Subgroup (U ≃ₗ[ZMod p] U)}

theorem lemmaThreeFive (hp : p ≠ 2) (hp7 : p ≠ 7) [Module.Finite (ZMod p) U]
    (S : PrimExtSetting G H 4) (hneg : TFNegOrGen p (Module.finrank (ZMod p) U - 1))
    (hJ : TFJ34Model p) {β : ZMod p} (hβ : 2 * β ^ 2 + β + 1 = 0)
    {f : Module.Basis (Fin 4) (ZMod p) U} (hfH : H = basisClosure f (j34Mats β)) : False := by
  have hp4 : 4 < p := by have := seven_lt_of_two_mul_sq_add hp hp7 hβ; omega
  obtain ⟨hi, _, _, _⟩ := exists_mem_j34Mats hp hβ f
  obtain ⟨g0, hg0, hm0⟩ := hi 0 (by decide)
  obtain ⟨g1, hg1, hm1⟩ := hi 1 (by decide)
  obtain ⟨g2, hg2, hm2⟩ := hi 2 (by decide)
  have hz : LinearMap.toMatrix f f ((g0 * g1 : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) =
      diagSignMat (0 : Fin 4) * diagSignMat (1 : Fin 4) := by
    rw [LinearEquiv.coe_toLinearMap_mul, LinearMap.toMatrix_mul, hm0, hm1]
  obtain ⟨w, ψ, hψ, hb, hbH, hw0, hψ0, hwlast, hψlast, hw⟩ :=
    exists_reflection_coords hp S hneg (m := 3) f (T := j34BlockMats β) hfH hm0
      (hfH.symm ▸ hJ (W := U) f β hp hp7 hβ g0 (g0 * g1) g2 hm0 hz hm2)
  exact false_of_coords_j34 hp4 S.dmax hβ f (hfH ▸ S.H_le) hψ hb (hfH ▸ hbH) hw0 hψ0
    hwlast hψlast hw


end PrimExtSetting

end CFSG.StandardType.ZS

end
