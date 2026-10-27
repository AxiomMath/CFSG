module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.OmEichler
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.OmIso
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogQuadraticDescent
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseALangHerm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open QuadraticMap CFSG.ComponentClassification
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.UnbalancedCatalog (descentField fixSpace descentForm
  coe_descentForm finrank_fixSpace mem_fixSpace)

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem exists_singular_eigen_semilinear [Finite K] (hK2 : ringChar K ≠ 2) (hd : 3 ≤ d)
    (hQ : (polarBilin Q).Nondegenerate) (g : similarityPairs Q) (hσ2 : g.val.right ^ 2 = 1)
    (hσ1 : g.val.right ≠ 1)
    (hc : ∃ c : Kˣ, g.val.left * CatalogueBHigherLinearField.glFieldAut (Fin d) K g.val.right
      g.val.left = Matrix.GeneralLinearGroup.scalar (Fin d) c) :
    ∃ u : Fin d → K, u ≠ 0 ∧ Q u = 0 ∧ ∃ l : K, coordinateSemilinearMap g.val u = l • u := by
  classical
  obtain ⟨c, hc⟩ := hc
  have hσσ : ∀ a, g.val.right (g.val.right a) = a := by
    intro a
    have h := congrArg (fun τ : K ≃+* K => τ a) hσ2
    simpa [pow_two, RingAut.mul_apply] using h
  have hσa0 : ∃ a₀ : K, g.val.right a₀ ≠ a₀ := by
    by_contra h
    push Not at h
    exact hσ1 (RingEquiv.ext h)
  have hσsq : g.val.right * g.val.right = 1 := by
    rw [← pow_two]
    exact hσ2
  have hσc : g.val.right (c : K) = c :=
    right_apply_scalar_eq g.val (by omega) hσ2 hc
  obtain ⟨v, hv⟩ := exists_map_ne_zero_of_nondegenerate (d := d) (by omega) hQ
  have hμ : (multiplier Q g : K) * g.val.right (multiplier Q g : K) = (c : K) ^ 2 :=
    multiplier_mul_right_multiplier g hσ2 hc hv
  have hσU :=
    CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseALang.isUnitaryInvolution_of_involution
      hσ1 hσsq
  have hcinv : g.val.right ((c : K)⁻¹) = (c : K)⁻¹ := by
    rw [map_inv₀, hσc]
  obtain ⟨lam, hlam⟩ := hσU.norm_surj ((c : K)⁻¹) hcinv (inv_ne_zero (Units.ne_zero c))
  have hlam0 : lam ≠ 0 := by
    intro h0
    rw [h0, map_zero, zero_mul] at hlam
    exact (inv_ne_zero (Units.ne_zero c)) hlam.symm
  let T : (Fin d → K) →ₛₗ[(g.val.right : K →+* K)] (Fin d → K) :=
    { toFun := fun x => lam • coordinateSemilinearMap g.val x
      map_add' := by
        intro x y
        rw [map_add, smul_add]
      map_smul' := by
        intro a x
        show lam • coordinateSemilinearMap g.val (a • x) =
          g.val.right a • (lam • coordinateSemilinearMap g.val x)
        rw [coordinateSemilinearMap_smul, smul_smul, smul_smul, mul_comm lam (g.val.right a)] }
  have hTT : ∀ x, T (T x) = x := by
    intro x
    show lam • coordinateSemilinearMap g.val (lam • coordinateSemilinearMap g.val x) = x
    rw [coordinateSemilinearMap_smul, smul_smul,
      coordinateSemilinearMap_sq g.val hσ2 hc x, smul_smul]
    have hlamσ : (lam * g.val.right lam) * (c : K) = 1 := by
      rw [mul_comm lam (g.val.right lam), hlam, inv_mul_cancel₀ (Units.ne_zero c)]
    rw [hlamσ, one_smul]
  have hν : (lam ^ 2 * (multiplier Q g : K)) *
      g.val.right (lam ^ 2 * (multiplier Q g : K)) = 1 := by
    have hlamσ : lam * g.val.right lam = (c : K)⁻¹ := by
      rw [mul_comm, hlam]
    calc (lam ^ 2 * (multiplier Q g : K)) *
          g.val.right (lam ^ 2 * (multiplier Q g : K))
        = (lam * g.val.right lam) ^ 2 * ((multiplier Q g : K) *
            g.val.right (multiplier Q g : K)) := by
          rw [map_mul, map_pow]
          ring
      _ = 1 := by
          rw [hlamσ, hμ, inv_pow]
          exact inv_mul_cancel₀ (pow_ne_zero 2 (Units.ne_zero c))
  have hν0 : lam ^ 2 * (multiplier Q g : K) ≠ 0 := by
    intro h0
    rw [h0, map_zero, zero_mul] at hν
    exact zero_ne_one hν
  have hzex : ∃ z₀ : K, z₀ ≠ 0 ∧
      (lam ^ 2 * (multiplier Q g : K)) * g.val.right z₀ = z₀ := by
    by_cases hνm1 : lam ^ 2 * (multiplier Q g : K) = -1
    · obtain ⟨a₀, ha₀⟩ := hσa0
      refine ⟨a₀ - g.val.right a₀, sub_ne_zero.mpr (Ne.symm ha₀), ?_⟩
      rw [map_sub, hσσ a₀, hνm1]
      ring
    · refine ⟨1 + lam ^ 2 * (multiplier Q g : K), ?_, ?_⟩
      · intro h0
        apply hνm1
        linear_combination h0
      · have hσν : g.val.right (lam ^ 2 * (multiplier Q g : K)) =
            (lam ^ 2 * (multiplier Q g : K))⁻¹ := by
          have h := congrArg
            (fun x : K => (lam ^ 2 * (multiplier Q g : K))⁻¹ * x) hν
          rw [← mul_assoc, inv_mul_cancel₀ hν0, one_mul, mul_one] at h
          exact h
        rw [map_add, map_one, hσν, mul_add, mul_one, mul_inv_cancel₀ hν0]
        ring
  obtain ⟨z₀, hz0, hzν⟩ := hzex
  have hσz : g.val.right z₀⁻¹ = z₀⁻¹ * (lam ^ 2 * (multiplier Q g : K)) := by
    have hσz₀ : g.val.right z₀ = (lam ^ 2 * (multiplier Q g : K))⁻¹ * z₀ := by
      have h := congrArg (fun x : K => (lam ^ 2 * (multiplier Q g : K))⁻¹ * x) hzν
      rw [← mul_assoc, inv_mul_cancel₀ hν0, one_mul] at h
      exact h
    rw [map_inv₀, hσz₀, mul_inv_rev, inv_inv]
  have hQT : ∀ x, Q (T x) =
      (lam ^ 2 * (multiplier Q g : K)) * g.val.right (Q x) := by
    intro x
    show Q (lam • coordinateSemilinearMap g.val x) = _
    rw [QuadraticMap.map_smul, multiplier_spec Q g x, smul_eq_mul]
    ring
  have hTQ : ∀ x, (z₀⁻¹ • Q) (T x) = g.val.right ((z₀⁻¹ • Q) x) := by
    intro x
    rw [QuadraticMap.smul_apply, QuadraticMap.smul_apply, smul_eq_mul, smul_eq_mul, hQT,
      map_mul, hσz]
    ring
  have hW : 3 ≤ Module.finrank (descentField g.val.right)
      (⊤ : Submodule (descentField g.val.right) (fixSpace T)) := by
    rw [finrank_top,
      finrank_fixSpace (σ := g.val.right) (T := T) hσσ hTT hσa0.choose_spec,
      Module.finrank_fin_fun]
    exact hd
  have : Finite (descentField g.val.right) := Subtype.finite
  have hChar : CharP (descentField g.val.right) (ringChar K) :=
    Subfield.charP (descentField g.val.right) (ringChar K)
  have hk2 : ringChar (descentField g.val.right) ≠ 2 := by
    rw [ringChar.eq (descentField g.val.right) (ringChar K)]
    exact hK2
  obtain ⟨w, -, hw0, hwQ⟩ :=
    exists_singular_of_three_le_finrank (k := descentField g.val.right) (V := fixSpace T)
      hk2 (descentForm hTQ) (W := ⊤) hW
  refine ⟨(w : Fin d → K), ?_, ?_, ?_⟩
  · intro h
    exact hw0 (Subtype.ext h)
  · have hQ'w : (z₀⁻¹ • Q) (w : Fin d → K) = 0 := by
      rw [← coe_descentForm hTQ w, hwQ]
      rfl
    rw [QuadraticMap.smul_apply, smul_eq_mul] at hQ'w
    exact (mul_eq_zero.mp hQ'w).resolve_left (inv_ne_zero hz0)
  · have hfix : lam • coordinateSemilinearMap g.val (w : Fin d → K) = (w : Fin d → K) :=
      mem_fixSpace.1 w.2
    refine ⟨lam⁻¹, ?_⟩
    calc coordinateSemilinearMap g.val (w : Fin d → K)
        = lam⁻¹ • (lam • coordinateSemilinearMap g.val (w : Fin d → K)) := by
          rw [smul_smul, inv_mul_cancel₀ hlam0, one_smul]
      _ = lam⁻¹ • (w : Fin d → K) := by rw [hfix]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
