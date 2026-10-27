module

public import CFSG.RankThree.GF2n.Smith81.Lin31TwoModel
import CFSG.RankThree.GF2n.Stroth80.Satz5Stroth

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement Matrix CharTwo

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace TensorModel

variable {TM : TensorModel M Q Z B}

private def v₁ : TM.M₀.E := TM.Φ.symm !![0, 1; 0, 0]

private def v₂ : TM.M₀.E := TM.Φ.symm !![1, 0; 0, 0]

private def w₁ : TM.M₀.E := TM.Φ.symm !![0, 0; 1, 0]

private def w₂ : TM.M₀.E := TM.Φ.symm !![0, 0; 0, 1]

private theorem eps_B (e f : TM.M₀.E) :
    TM.ε (TM.M₀.B e f) =
      (TM.Φ e) 0 0 * (TM.Φ f) 1 1 + (TM.Φ e) 1 1 * (TM.Φ f) 0 0 -
        (TM.Φ e) 0 1 * (TM.Φ f) 1 0 - (TM.Φ e) 1 0 * (TM.Φ f) 0 1 := by
  have h := congrArg TM.ε (TM.M₀.Qf_add e f)
  rw [TM.qf] at h
  simp only [map_add, TM.qf] at h
  simp only [Matrix.det_fin_two, Matrix.add_apply] at h
  linear_combination -h

private theorem B_v1_w1 : TM.M₀.B v₁ w₁ = 1 := by
  apply TM.ε.injective
  rw [eps_B, map_one]
  simp [v₁, w₁]

private theorem B_v2_w2 : TM.M₀.B v₂ w₂ = 1 := by
  apply TM.ε.injective
  rw [eps_B, map_one]
  simp [v₂, w₂]

private theorem B_v1_w2 : TM.M₀.B v₁ w₂ = 0 := by
  apply TM.ε.injective
  rw [eps_B, map_zero]
  simp [v₁, w₂]

private theorem B_v2_w1 : TM.M₀.B v₂ w₁ = 0 := by
  apply TM.ε.injective
  rw [eps_B, map_zero]
  simp [v₂, w₁]

private theorem B_v1_v2 : TM.M₀.B v₁ v₂ = 0 := by
  apply TM.ε.injective
  rw [eps_B, map_zero]
  simp [v₁, v₂]

private theorem B_w1_w2 : TM.M₀.B w₁ w₂ = 0 := by
  apply TM.ε.injective
  rw [eps_B, map_zero]
  simp [w₁, w₂]

private theorem Phi_rootB (m : TM.K) (e : TM.M₀.E) :
    TM.Φ (Satz5.rootB TM.M₀ v₁ v₂ m e) = !![1, TM.ε m; 0, 1] * TM.Φ e := by
  have hv₁ : TM.Φ v₁ = !![0, 1; 0, 0] := TM.Φ.apply_symm_apply _
  have hv₂ : TM.Φ v₂ = !![1, 0; 0, 0] := TM.Φ.apply_symm_apply _
  have hB₂ : TM.ε (TM.M₀.B e v₂) = (TM.Φ e) 1 1 := by
    rw [eps_B]
    simp [hv₂]
  have hB₁ : TM.ε (TM.M₀.B e v₁) = (TM.Φ e) 1 0 := by
    rw [eps_B]
    simp [hv₁]
  simp only [Satz5.rootB, map_add, TM.smul, hv₁, hv₂, map_mul, hB₂, hB₁]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]

private theorem Phi_rootA (l : TM.K) (e : TM.M₀.E) :
    TM.Φ (Satz5.rootA TM.M₀ v₂ w₁ l e) = TM.Φ e * !![1, 0; TM.ε l, 1] := by
  have hw₁ : TM.Φ w₁ = !![0, 0; 1, 0] := TM.Φ.apply_symm_apply _
  have hv₂ : TM.Φ v₂ = !![1, 0; 0, 0] := TM.Φ.apply_symm_apply _
  have hBw₁ : TM.ε (TM.M₀.B e w₁) = (TM.Φ e) 0 1 := by
    rw [eps_B]
    simp [hw₁]
  have hBv₂ : TM.ε (TM.M₀.B e v₂) = (TM.Φ e) 1 1 := by
    rw [eps_B]
    simp [hv₂]
  simp only [Satz5.rootA, map_add, TM.smul, hw₁, hv₂, map_mul, hBw₁, hBv₂]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply] <;> ring

theorem not_statedSL_le_Gamma (hc : Ctx M Q Z B) : ¬ StatedSL 2 TM.F ≤ TM.Gamma := by
  intro hSL
  have h2 : (2 : TM.K) = 0 := CharTwo.two_eq_zero
  obtain ⟨hnorm, hcent, hfaith⟩ :=
    hc.hyp.satz5_conditions (M₀ := TM.M₀) TM.gm.reg le_rfl
  have hSet : Satz5.Setting TM.M₀ (H0 M Z) v₁ v₂ w₁ w₂ :=
    Satz5.Setting.mk TM.gm.reg h2 B_v1_w1 B_v2_w2 B_v1_w2 B_v2_w1 B_v1_v2 B_w1_w2
      hnorm hcent hfaith
  have hK : 2 < Nat.card TM.K := by
    rw [TM.gm.card]
    have := hc.hyp.q4
    omega
  obtain ⟨ν, hν0, hν1⟩ := Satz5.exists_ne_zero_one hK
  have hA : ∀ l : TM.K, (l = 1 ∨ l = ν) → ∃ a ∈ H0 M Z,
      Satz5.Induces TM.M₀ a (Satz5.rootA TM.M₀ v₂ w₁ l) := by
    intro l _
    let A : GL (Fin 2) TM.F :=
      Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; TM.ε l, 1] (by
        simp [Matrix.det_fin_two_of])
    have hAmem : A ∈ StatedSL 2 TM.F :=
      CFSG.Open.StatedAPI.mem_statedSL_of_det (by simp [A, Matrix.det_fin_two_of])
    obtain ⟨m, hm, -, -, hmH⟩ := hSL hAmem
    have hdet : (!![1, 0; TM.ε l, 1] : Matrix (Fin 2) (Fin 2) TM.F).det = 1 := by
      simp [Matrix.det_fin_two_of]
    have hform : ∀ x ∈ Q, TM.Φ (TM.M₀.π (m * x * m⁻¹)) =
        TM.Φ (TM.M₀.π x) * !![1, 0; TM.ε l, 1] := fun x hx => by
      simpa [A] using hmH x hx
    refine ⟨m, ⟨hm, TM.mem_centralizer_of_right_mul hc hm hdet hform⟩, fun x hx => ?_⟩
    apply TM.Φ.injective
    rw [hform x hx]
    exact (Phi_rootA l (TM.M₀.π x)).symm
  have hB : ∀ m : TM.K, (m = 1 ∨ m = ν) → ∃ b ∈ H0 M Z,
      Satz5.Induces TM.M₀ b (Satz5.rootB TM.M₀ v₁ v₂ m) := by
    intro m _
    let U : GL (Fin 2) TM.F :=
      Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, TM.ε m; 0, 1] (by
        simp [Matrix.det_fin_two_of])
    have hUmem : U ∈ StatedSL 2 TM.F :=
      CFSG.Open.StatedAPI.mem_statedSL_of_det (by simp [U, Matrix.det_fin_two_of])
    have hU : U ∈ TM.φ.range := by rw [TM.φ_range]; exact hUmem
    obtain ⟨s, hs⟩ := hU
    refine ⟨(s : G), Lgen_le_H0 hc s.2, fun x hx => ?_⟩
    apply TM.Φ.injective
    rw [TM.act s x hx, hs]
    simpa [U] using (Phi_rootB m (TM.M₀.π x)).symm
  exact hSet.false_of_rootLifts hν0 hν1 hA hB

end TensorModel

end CFSG.RankThree.GF2n.Smith81
