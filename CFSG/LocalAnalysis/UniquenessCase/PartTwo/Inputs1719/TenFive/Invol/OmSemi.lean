module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.OmEichler
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.OmSemiFix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.ComponentClassification
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem exists_eichler_inv_semilinear [Finite K] (hK2 : ringChar K ≠ 2) (hd : 3 ≤ d)
    (hQ : (polarBilin Q).Nondegenerate) (g : similarityPairs Q) (hσ2 : g.val.right ^ 2 = 1)
    (hσ1 : g.val.right ≠ 1)
    (hc : ∃ c : Kˣ, g.val.left * CatalogueBHigherLinearField.glFieldAut (Fin d) K g.val.right
      g.val.left = Matrix.GeneralLinearGroup.scalar (Fin d) c) :
    ∃ u w : Fin d → K, u ≠ 0 ∧ Q u = 0 ∧ polar Q u w = 0 ∧ w ∉ Submodule.span K {u} ∧
      eichler Q (coordinateSemilinearMap g.val u)
        ((multiplier Q g : K)⁻¹ • coordinateSemilinearMap g.val w) = eichler Q u (-w) := by
  classical
  obtain ⟨c, hc⟩ := hc
  have hσσ : ∀ a : K, g.val.right (g.val.right a) = a := by
    intro a
    have h := congrArg (fun e : K ≃+* K => e a) hσ2
    simpa [pow_two] using h
  obtain ⟨a₀, ha₀⟩ : ∃ a : K, g.val.right a ≠ a := by
    by_contra h
    push Not at h
    exact hσ1 (RingEquiv.ext h)
  let θ : K := a₀ - g.val.right a₀
  have hθ0 : θ ≠ 0 := by
    intro h
    dsimp only [θ] at h
    exact ha₀ (sub_eq_zero.mp h).symm
  have hσθ : g.val.right θ = -θ := by
    dsimp only [θ]
    rw [map_sub, hσσ, neg_sub]
  set μ : K := (multiplier Q g : K) with hμdef
  have hμ0 : μ ≠ 0 := by rw [hμdef]; exact Units.ne_zero _
  obtain ⟨v₀, hv₀⟩ := exists_map_ne_zero_of_nondegenerate (by omega : 1 ≤ d) hQ
  have hμσμ : μ * g.val.right μ = (c : K) ^ 2 := by
    rw [hμdef]
    exact multiplier_mul_right_multiplier g hσ2 hc hv₀
  obtain ⟨u, hu0, huQ, l, hSu⟩ :=
    exists_singular_eigen_semilinear hK2 hd hQ g hσ2 hσ1 ⟨c, hc⟩
  have hSsq : coordinateSemilinearMap g.val (coordinateSemilinearMap g.val u) = (c : K) • u :=
    coordinateSemilinearMap_sq g.val hσ2 hc u
  have hlc : g.val.right l * l = (c : K) := by
    have h1 : (g.val.right l * l) • u = (c : K) • u := by
      calc (g.val.right l * l) • u = g.val.right l • (l • u) := (smul_smul ..).symm
        _ = g.val.right l • coordinateSemilinearMap g.val u := by rw [hSu]
        _ = coordinateSemilinearMap g.val (l • u) :=
            (coordinateSemilinearMap_smul g.val l u).symm
        _ = coordinateSemilinearMap g.val (coordinateSemilinearMap g.val u) := by rw [hSu]
        _ = (c : K) • u := hSsq
    have h2 : (g.val.right l * l - (c : K)) • u = 0 := by rw [sub_smul, h1, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero_iff_left hu0).mp h2)
  have hl0 : l ≠ 0 := by
    rintro rfl
    exact Units.ne_zero c (by simpa using hlc.symm)
  let T' : (Fin d → K) → (Fin d → K) :=
    fun v => (l * μ⁻¹) • coordinateSemilinearMap g.val v
  have hTsmul : ∀ (a : K) (v : Fin d → K), T' (a • v) = g.val.right a • T' v := by
    intro a v
    dsimp only [T']
    rw [coordinateSemilinearMap_smul, smul_smul, smul_smul, mul_comm]
  have hTadd : ∀ v w : Fin d → K, T' (v + w) = T' v + T' w := by
    intro v w
    dsimp only [T']
    rw [map_add, smul_add]
  have hTneg : ∀ v : Fin d → K, T' (-v) = -T' v := by
    intro v
    dsimp only [T']
    rw [map_neg, smul_neg]
  have hTsub : ∀ a b : Fin d → K, T' (a - b) = T' a - T' b := by
    intro a b
    rw [sub_eq_add_neg, sub_eq_add_neg, hTadd, hTneg]
  have hlam : (l * μ⁻¹) * g.val.right (l * μ⁻¹) = (c : K)⁻¹ := by
    have h1 : g.val.right (l * μ⁻¹) = g.val.right l * (g.val.right μ)⁻¹ := by
      rw [map_mul, map_inv₀]
    have h2 : l * g.val.right l = (c : K) := by rw [mul_comm]; exact hlc
    rw [h1]
    rw [show (l * μ⁻¹) * (g.val.right l * (g.val.right μ)⁻¹)
          = (l * g.val.right l) * (μ * g.val.right μ)⁻¹ from by rw [mul_inv]; ring]
    rw [h2, hμσμ, pow_two, mul_inv]
    rw [← mul_assoc, mul_inv_cancel₀ (Units.ne_zero c), one_mul]
  have hcoefT : (l * μ⁻¹) * (g.val.right (l * μ⁻¹) * (c : K)) = 1 := by
    rw [← mul_assoc, hlam, inv_mul_cancel₀ (Units.ne_zero c)]
  have hcoefB : l⁻¹ * ((l * μ⁻¹) * μ) = 1 := by
    rw [show l⁻¹ * ((l * μ⁻¹) * μ) = (l⁻¹ * l) * (μ⁻¹ * μ) from by ring,
      inv_mul_cancel₀ hl0, inv_mul_cancel₀ hμ0, mul_one]
  have hTinv : ∀ v : Fin d → K, T' (T' v) = v := by
    intro v
    calc T' (T' v) = (l * μ⁻¹) • coordinateSemilinearMap g.val
          ((l * μ⁻¹) • coordinateSemilinearMap g.val v) := rfl
      _ = (l * μ⁻¹) • (g.val.right (l * μ⁻¹) •
            coordinateSemilinearMap g.val (coordinateSemilinearMap g.val v)) := by
            rw [coordinateSemilinearMap_smul]
      _ = (l * μ⁻¹) • (g.val.right (l * μ⁻¹) • ((c : K) • v)) := by
            rw [coordinateSemilinearMap_sq g.val hσ2 hc]
      _ = ((l * μ⁻¹) * (g.val.right (l * μ⁻¹) * (c : K))) • v := by
            rw [smul_smul, smul_smul, mul_assoc]
      _ = v := by rw [hcoefT, one_smul]
  have huS : u = l⁻¹ • coordinateSemilinearMap g.val u := by
    rw [hSu, smul_smul, inv_mul_cancel₀ hl0, one_smul]
  have hBT : ∀ y : Fin d → K, polar Q u (T' y) = g.val.right (polar Q u y) := by
    intro y
    calc polar Q u (T' y)
        = l⁻¹ • polar Q (coordinateSemilinearMap g.val u) (T' y) := by
            conv_lhs => rw [huS]
            rw [polar_smul_left]
      _ = l⁻¹ • ((l * μ⁻¹) • polar Q (coordinateSemilinearMap g.val u)
            (coordinateSemilinearMap g.val y)) := by
            dsimp only [T']
            rw [polar_smul_right]
      _ = l⁻¹ • ((l * μ⁻¹) • (μ * g.val.right (polar Q u y))) := by
            rw [polar_coordinateSemilinearMap]
      _ = g.val.right (polar Q u y) := by
            simp only [smul_eq_mul]
            rw [show l⁻¹ * ((l * μ⁻¹) * (μ * g.val.right (polar Q u y)))
                  = (l⁻¹ * ((l * μ⁻¹) * μ)) * g.val.right (polar Q u y) from by ring,
              hcoefB, one_mul]
  have hex : ∃ y : Fin d → K, polar Q u y = 0 ∧ y - T' y ∉ Submodule.span K {u} := by
    by_contra h
    push Not at h
    have hker : LinearMap.ker (polarBilin Q u) ≤ Submodule.span K {u} := by
      intro y hy
      have hBy : polar Q u y = 0 := by
        have hy' : polarBilin Q u y = 0 := LinearMap.mem_ker.mp hy
        simpa only [polarBilin_apply_apply] using hy'
      have h1 : y - T' y ∈ Submodule.span K {u} := h y hBy
      have h2θ : polar Q u (θ • y) = 0 := by
        rw [polar_smul_right, hBy, smul_zero]
      have h3 : θ • y - T' (θ • y) ∈ Submodule.span K {u} := h (θ • y) h2θ
      have hTθ : T' (θ • y) = -(θ • T' y) := by
        rw [hTsmul, hσθ, neg_smul]
      have h4 : θ • (y + T' y) ∈ Submodule.span K {u} := by
        have heq : θ • (y + T' y) = θ • y - T' (θ • y) := by
          rw [hTθ, smul_add, sub_neg_eq_add]
        rw [heq]; exact h3
      have h5 : y + T' y ∈ Submodule.span K {u} := by
        have hmem : θ⁻¹ • (θ • (y + T' y)) ∈ Submodule.span K {u} :=
          Submodule.smul_mem (Submodule.span K {u}) θ⁻¹ h4
        rwa [smul_smul, inv_mul_cancel₀ hθ0, one_smul] at hmem
      have h6 : (2 : K) • y ∈ Submodule.span K {u} := by
        have heq : (2 : K) • y = (y + T' y) + (y - T' y) := by
          rw [two_smul]; abel
        rw [heq]; exact Submodule.add_mem (p := Submodule.span K {u}) h5 h1
      have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK2
      have hmem : (2 : K)⁻¹ • ((2 : K) • y) ∈ Submodule.span K {u} :=
        Submodule.smul_mem (Submodule.span K {u}) (2 : K)⁻¹ h6
      rwa [smul_smul, inv_mul_cancel₀ h2, one_smul] at hmem
    have hdim : Module.finrank K (LinearMap.ker (polarBilin Q u)) ≤ 1 := by
      have h1 : Module.finrank K (LinearMap.ker (polarBilin Q u))
          ≤ Module.finrank K (Submodule.span K {u}) := Submodule.finrank_mono hker
      rwa [finrank_span_singleton hu0] at h1
    have hdim2 : 2 ≤ Module.finrank K (LinearMap.ker (polarBilin Q u)) := by
      have hrank := LinearMap.finrank_range_add_finrank_ker (polarBilin Q u)
      have hrange : Module.finrank K (LinearMap.range (polarBilin Q u)) ≤ 1 := by
        have h1 := Submodule.finrank_le (LinearMap.range (polarBilin Q u))
        rwa [Module.finrank_self] at h1
      have hd' : Module.finrank K (Fin d → K) = d := by
        rw [Module.finrank_fin_fun]
      omega
    omega
  obtain ⟨y, hBy, hwy⟩ := hex
  have hBuw : polar Q u (y - T' y) = 0 := by
    rw [polar_sub_right, hBy, hBT y, hBy, map_zero, sub_zero]
  have hTw : T' (y - T' y) = -(y - T' y) := by
    rw [hTsub, hTinv, neg_sub]
  refine ⟨u, y - T' y, hu0, huQ, hBuw, hwy, ?_⟩
  calc eichler Q (coordinateSemilinearMap g.val u)
        (μ⁻¹ • coordinateSemilinearMap g.val (y - T' y))
      = eichler Q (l • u) (μ⁻¹ • coordinateSemilinearMap g.val (y - T' y)) := by rw [hSu]
    _ = eichler Q u (l • (μ⁻¹ • coordinateSemilinearMap g.val (y - T' y))) := by
          rw [eichler_smul_left]
    _ = eichler Q u (-(y - T' y)) := by
          rw [smul_smul]
          simpa only [T'] using congrArg (eichler Q u) hTw

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
